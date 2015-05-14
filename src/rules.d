
import proofcontext;
import proof;
import expression;

import std.range;
import std.stdio;

interface Rule
{
	bool opCall(ProofContext context) const;
	@property string toString() const pure;
}
interface ForwardRule : Rule
{
}
interface BackwardRule : Rule
{
}


class AssumptionRule : ForwardRule
{
	bool opCall(ProofContext context) const { return false; };
	@property override string toString() const pure { return "Assumed"; }
}
class GoalRule : BackwardRule
{
	bool opCall(ProofContext context) const { return false; };
	@property override string toString() const pure { return "Goal"; }
}

class Subproof : Rule
{
protected:
	const Expression[] mPremises;
	SupportRef[] mSupport;
	const Expression mResult;

public:
	this(const Expression[] premises, const Expression result)
	{
		mPremises = premises;
		mResult = result;
		mSupport[0..premises.length] = SupportRef(null,ulong.max);
	}
	@property override string toString() const pure { return "Subproof"; }

	bool opCall(ProofContext context) const
	{
		//ulong[] found;
		//found[0..mPremises.length] = ulong.max;
		//uint cnt=0;
		foreach(i, premise, support; lockstep(mPremises,mSupport))
		{
			if( support.supported )
				continue;

			foreach(j, st; context.statements)
			{
				if( premise.compare(st.expression) )
					goto found_support;
			}
			return false;
		found_support:
			continue;
		}
		context.newStatement(mResult, this, mSupport);
		return true;
	}
}

class AndElim : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		bool action = false;
		auto newst = context.prevStatements; // Original new statements
		auto n = context.statements.length-1;
		foreach(i, st; newst)
		{
			if( st.expression.func == "and" && st.expression.nargs > 1 )
			{
				action = true;
				foreach(arg; st.expression.args)
				{
					context.newStatement(arg, this, [SupportRef(context,i+n)]);
				}
			}
		}
		return action;
	}
	@property override string toString() const pure { return "And Elim"; }
}
class NotElim : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		bool action = false;
		auto newst = context.prevStatements; // Original new statements
		auto n = context.statements.length-1;
		foreach(i, st; newst)
		{
			if( st.expression.func == "not" && st.expression.nargs == 1 )
			{
				auto nest = st.expression.args[0];
				if( nest.func == "not" && nest.nargs == 1 )
				{
					action = true;
					context.newStatement(nest.args[0], this, [SupportRef(context,i+n)]);
				}
			}
		}
		return action;
	}
	@property override string toString() const pure { return "Not Elim"; }
}
/+
class NotIntro : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		bool action = false;
		auto newst = context.newStatements; // Original new statements
		auto n = context.statements.length;
		foreach(i, st; newst)
		{
			auto subproof = new ProofContext(context, new Expression("not", [context.goal.expression]));
			auto success = subproof.prove();
			action = success;
			if( success )
				context.newStatement(context.goal.expression, this, [SupportRef(context,i+n)]);
		}
		return action;
	}
	@property override string toString() const { return "Not Intro"; }
}
+/
class OrElim : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		auto newst = context.prevStatements; // Original new statements
		foreach(st; newst)
		{
			if( st.expression.func == "or" && st.expression.nargs > 1 )
			{
				foreach(arg; st.expression.args)
				{
//					if( st.expression is arg )
//						break;
					writefln("Trying both cases for %s: case %s", st.expression, arg);
					auto subproof = new ProofContext(context, context.goal.expression);
					subproof.newStatement(st.expression.args[0], ASSUMED, []);
					//subproof.applyNewStatements();
					auto success = subproof.prove();
					writefln("Case %s: %s", arg, success ? "Found goal" : "Failed goal");
					if( !success )
						goto failed;
				}
				context.newStatement(context.goal.expression, this, []);
				return true;
			failed:
				continue;
			}
		}
		return false;
	}
	@property override string toString() const pure { return "Or Elim"; }
}
class ContradictionElim : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		auto newst = context.prevStatements; // Original new statements
		foreach(st; context.allStatements)
		{
			writefln("Checking %s for contradictions...", st.expression);
			foreach(st2; newst)
			{
				writefln("Checking %s for contradiction with %s (1)", st.expression, st2.expression);
				if( st2.expression.func == "not" && st2.expression.nargs == 1 )
				{
					if( st2.expression.args[0].compare(st.expression) )
					{
						context.newStatement(context.goal.expression, this, []);
						return true;
					}
				}
			}
			if( st.expression.func == "not" && st.expression.nargs == 1 )
			{
				foreach(st2; newst)
				{
					writefln("Checking %s for contradiction with %s (2)", st.expression, st2.expression);
					if( st.expression.args[0].compare(st2.expression) )
					{
						context.newStatement(context.goal.expression, this, []);
						return true;
					}
				}
			}
		}
		return false;
	}
	@property override string toString() const pure { return "Contradiction"; }
}
class ConditionalElim : ForwardRule
{
public:
	bool opCall(ProofContext context) const
	{
		auto newst = context.prevStatements; // Original new statements
		auto n = context.statements.length-1;
		foreach(i,st; context.allStatements)
		{
			writefln("Checking %s for implications...", st);
			foreach(j,st2; newst)
			{
				writefln("Checking %s for implications from %s (1)", st, st2);
				if( st2.expression.func == "implies" && st2.expression.nargs == 2 )
				{
					if( st2.expression.args[0].compare(st.expression) )
					{
						context.newStatement(st2.expression.args[1], this, [SupportRef(context,i),SupportRef(context,j+50)]);
						return true;
					}
				}
			}
			if( st.expression.func == "implies" && st.expression.nargs == 2 )
			{
				foreach(j,st2; newst)
				{
					writefln("Checking %s for implications from %s (2)", st, st2);
					if( st.expression.args[0].compare(st2.expression) )
					{
						context.newStatement(st.expression.args[1], this, [SupportRef(context,i),SupportRef(context,j+30)]);
						return true;
					}
				}
			}
		}
		return false;
	}
	@property override string toString() const pure { return "Conditional Elim"; }
}

