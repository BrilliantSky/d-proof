
import std.stdio;
import std.string;
import std.algorithm;
import std.regex;

import expression;
import proof;
import proofcontext;

interface Parser
{
	Expression parse(in char[] src) const;
}

class PrefixParser : Parser
{
private:
	static final bool countGroups(in char[] exp, out const(char[])[] groups) pure
	{
		uint level = 0;
		uint pos=0;
		foreach(uint i, c; exp)
		{
			if( c == '(' )
			{
				if( level == 0 )
					pos = i;
				level++;
			}
			else if( c == ')' )
			{
				//writefln(") at %s (l%s): %s", i, level, exp[pos..i+1]);
				if( level == 0 )
					return false;
				else if( level == 1 )
				{
					groups ~= exp[pos..i+1];
					pos = i+1;
				}
				level--;
			}
			else if( level == 0 )
			{
				if( c == ' ' )
				{
					if( pos != i )
						groups ~= exp[pos..i];
					pos = i+1;
				}
			}
		}
		if( level != 0 )
			return false;
		if( pos < exp.length && exp[pos] != ' ' )
			groups ~= exp[pos..$];
		return true;
	}
public:
	static Expression parseExpression(in char[] src)
	{
		enum string VAR = `\p{Greek}|\w+`;

		auto re = ctRegex!(`\(\s*(`~VAR~`)\s+(.*)\s*\)`);
		auto match = src.matchFirst(re);
		if( match.empty )
		{
			//writefln("fn: '%s'", src);
			return new Expression(strip(src).idup);
		}

		const(char)[] fn = match[1];
		const(char)[] args = match[2];
		const(char[])[] argGroups;

		//writefln("fn: '%s' args: \"%s\"", fn, args);

		auto exp = new Expression(fn.idup);

		if( !countGroups(args, argGroups) )
			return null; // bad parentheses

		foreach(arg; argGroups)
		{
			//writefln("\tArg: '%s'", arg);
			auto sub = parseExpression(arg);
			if( !sub )
				return null;

			exp.add(sub);
		}

		return exp;
	}
	override Expression parse(in char[] src) const { return parseExpression(src); }
}


