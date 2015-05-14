
import std.stdio;
import std.string;
import std.algorithm;
import std.regex;

import expression;
import proof;
import proofcontext;
import expressionparser;

/+
class ForAllElim
{
	struct ContextData
	{
		uint statementOffset, symbolOffset;
	}
	ContextData[ProofContext] mOffsets;
public:
	bool run(ProofContext context, in Expression statement, in Expression symbol)
	{
		bool changed=false;
		auto subst = statement.args[1].substitute( statement.args[0].func, sym, changed );
		if( changed )
			context.newStatement(subst);
		writefln("Apply forall %s to %s: %s", statement.args[1], sym, subst);
		return changed;
	}
	bool run(ProofContext context, in Expression statement)
	{
		bool action = false;
		foreach(sym; context.symbols)
		{
		}
	}
	bool run(ProofContext context)
	{
		bool action = false;
		foreach(st; context.statements)
		{
			action |= run(context, st);
		}
		return action;
	}
}+/


/// Class providing a command-line interface to d-proof
class Application
{
private:
	LogLevel mVerbosity;
public:
	enum LogLevel { Quiet=0, Normal, Warning, Verbose, Debug }
	alias LogLevel.Normal LOG_NORMAL;
	alias LogLevel.Warning LOG_WARNING;
	alias LogLevel.Normal LOG_ERROR;
	alias LogLevel.Verbose LOG_VERBOSE;
	alias LogLevel.Debug LOG_DEBUG;
	this(LogLevel verbosity = LogLevel.Warning)
	{
		mVerbosity = verbosity;
	}
private:
	/// Logs a message if the specified level meets or exceeds the logging threshold.
	void log(Args...)(LogLevel level, Args args)
	{
		if( level <= mVerbosity )
		{
			stderr.writefln(args);
		}
	}

	/// Prints all of the statements in a ProofContext.
	void dump(ProofContext context)
	{
		if( mVerbosity == LogLevel.Quiet )
			return;
		foreach(i, st; context.allStatements)
		{
			writefln("%s: %s", i, st);
		}
	}

	enum LineType { Empty=0, Command, Statement, Goal, Error }
	/// Parses a single line for either an expression, goal, or command.
	/// Returns the type of line.
	// TODO: This should throw exceptions, not return Error.
	LineType parseLine(in char[] line, uint l, ref Expression[] premises, ref Expression goal)
	{
		if( line.length==0 || line[0] == '#' )
			return LineType.Empty;
		if( line[0] == '%' )
		{
			auto exp = PrefixParser.parseExpression(line[1..$]);
			if( !exp )
				log(LOG_WARNING, "Error on goal line %s", l);
			else
				log(LOG_VERBOSE, "Goal on line %s: %s", l, exp);
			//exp.support = "goal";
			goal = exp;
			return exp ? LineType.Goal : LineType.Error;
		}
		if( line[0] == '$' )
		{
			auto token = line[1..$];
			if( token.findSkip("include") )
			{
				auto filename = token.strip();
				Expression tmpgoal;
				if( parseFile(filename, premises, tmpgoal) )
				{
					if( tmpgoal && goal )
						log(LOG_WARNING, "Warning: New goals specified in included file %s: %s", filename, tmpgoal);
					goal = tmpgoal;
					return LineType.Empty; // Avoid errors with interactive mode
				}
				else
				{
					log(LOG_ERROR, "Error: Failed to include file '%s'", filename);
					return LineType.Error;
				}
			}
			/*else if( line[1..$] == "done" || line[1..$] == "exit" || line[1..$] == "quit" )
			{
				return true;
			}*/
			else
			{
				//log(LOG_ERROR, "Error: Unknown command '%s' on line %s", line, l);
				return LineType.Command;
			}
		}
		else
		{
			//writefln("parsing %s", line);
			auto exp = PrefixParser.parseExpression(line);
			if( !exp )
				log(LOG_WARNING, "Error on line %s", l);
			else
			{
				log(LOG_VERBOSE, "Premise on line %s: %s", l, exp);
				premises ~= exp;
			}
			return exp ? LineType.Statement : LineType.Error;
		}
	}
	/// Parses the expressions (premises and goal) in a file
	bool parseFile(in char[] filename, ref Expression[] exp, out Expression goal)
	{
		auto src = File(filename.idup, "r");
		if( !src.isOpen() )
			return false;

		uint l=1;
		foreach(line; src.byLine())
		{
			parseLine(line, l, exp, goal);
			l++;
		}
		return true;
	}
public:
	/// Allows interactive specification of premises, goals, and commands.
	int proveInteractive()
	{
		Expression[] premises;
		Expression goal;

		if( mVerbosity != LogLevel.Quiet )
			write("Enter statements:\n1> ");

		uint l=1;
		foreach(line; stdin.byLine())
		{
			switch( parseLine(line, l, premises, goal) )
			{
			case LineType.Goal:
				assert(goal);
				if( prove(premises, goal) )
				{
					// Might cause goal to be duplicated...
					premises ~= goal;
					goal = null;
				}
				break;
			case LineType.Command:
				switch( line[1..$] )
				{
				case "exit":
				case "quit":
					return 0;
				case "clear":
					premises.length = 0;
					goal = null;
					l = 0;
					break;
				case "dump":
					stdout.writeln("Premises:");
					foreach(i, st; premises)
						stdout.writefln("  %s: %s", i+1, st);
					stdout.writefln("Goal: %s\n", goal);
					break;
				case "prove":
					if( goal )
						prove(premises, goal);
					else
						log(LOG_ERROR, "Error: No goal specified");
					break;
				default:
					log(LOG_ERROR, "Error: Unknown command '%s' on line %s", line, l);
					break;
				}
				break;
			case LineType.Empty:
				l--;
				break;
			default:
				break;
			}

			l++;
			if( mVerbosity != LogLevel.Quiet )
				writef("%s> ", l);
		}
		if( mVerbosity != LogLevel.Quiet )
			writeln("");
		return 0;
	}
	/// Proves or disproves the goal in the file based on premises in the file
	int proveFile(string filename)
	{
		Expression[] premises;
		Expression goal;

		parseFile(filename, premises, goal);
		return prove(premises, goal);
	}
	/// Call the proof generator with the given premises and goal.
	///
	/// Prints the result and returns true if successful.
	bool prove(Expression[] premises, Expression goal)
	{
		auto context = new ProofContext(premises, goal);
		if( proof.prove(context) )
		{
			dump(context);
			log(LOG_NORMAL, "Found proof of %s!", goal);
			return true;
		}
		else
		{
			log(LOG_NORMAL, "Failed to find proof for %s!", goal);
			return false;
		}
	}
}

import std.getopt;

int main(string[] args)
{
	string filename;
	Application.LogLevel ll = Application.LogLevel.Warning;
	bool help=false;

	getopt( args,
		"help|h",     &help,
		"input|i",    &filename,
		"loglevel|l", &ll,
	);
	if( help )
	{
		writeln(
			"Welcome to d-proof, an automated proof generator written in D.\n"
			"Usage: <d-proof> [Options]\n"
			"Available options:\n"
			"    --help, -h     Display this help text.\n"
			"    --input, -i    Input file to read. Leave blank or use - for stdin.\n"
			"    --loglevel, -l Output verbosity level (Quiet, Normal, Warning, Verbose, Debug).\n"
		);
		return 0;
	}


	auto app = new Application(ll);
	if( filename.length == 0 || filename == "-" )
		return app.proveInteractive();
	else
		return app.proveFile(filename);
}

