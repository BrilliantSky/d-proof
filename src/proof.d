
import std.algorithm;
import std.conv;
import std.array;

import expression;
import proofcontext;
import rules;

import std.stdio;

void printNewStatements(in ProofContext pc)
{
	writeln("New Statements:");
	foreach(st; pc.newStatements)
		writefln("\t%s  [%s %s]", st.expression, st.supportRule, join(map!(to!string)(st.supportStatements), ", ") );
	writeln("");
}

bool checkGoalCondition(in ProofContext pc)
{
	bool isGoal(bool a, in Statement b) { return a || b.expression.compare(pc.goal.expression); }
	return reduce!isGoal(false, pc.newStatements);
	//return reduce!"(a,b) => a || b.compare(mGoal)"(false, newStatements);
	/+foreach(st; newStatements)
	{
		if( st.compare(mGoal) )
			return true;
	}
	return false;+/
}


class ForwardProver
{
	const(ForwardRule[]) mRules;

	this(in ForwardRule[] rules) { mRules=rules; }

	enum ProofState { Failed=0, Changed, Success };

	ProofState step(ProofContext context) const
	{
		context.printNewStatements();
		if( context.checkGoalCondition() )
			return ProofState.Success;
		context.applyNewStatements();

		foreach(subproof; context.openSubproofs)
		{
			step(subproof);
		}

		// ^ elim:  (and * * ...) ==> a, b
		// | elim:  (or * * ...) ==> sub(a), sub(b), ...

		uint cnt=0;
		foreach(rule; mRules)
		{
			cnt += rule(context);
		}

		//uint changed = reduce!((n,r) => n+r(mContext))( mRules );
		return cnt > 0 ? ProofState.Changed : ProofState.Failed;
	}
}

bool prove(ProofContext pc)
{
	assert(pc.goal.expression, "Must have a goal to prove");

	ForwardRule[] rules = [cast(ForwardRule)new AndElim(), cast(ForwardRule)new NotElim(), cast(ForwardRule)new OrElim(), cast(ForwardRule)new ContradictionElim(), cast(ForwardRule)new ConditionalElim()];
	auto prover = new ForwardProver(rules);

	ForwardProver.ProofState result;
	do
	{
		result = prover.step(pc);
		writefln("Step result: %s", result);
	} while( result == ForwardProver.ProofState.Changed );

	return result == ForwardProver.ProofState.Success;
/+
	auto andElim = new AndElim();
	auto notElim = new NotElim();
	//auto notIntro = new NotIntro();
	auto orElim = new OrElim();
	auto contraElim = new ContradictionElim();
	auto condElim = new ConditionalElim();
	uint changed;

	pc.printNewStatements();
	if( pc.checkGoalCondition() )
		return true;
	pc.applyNewStatements();

	do
	{
		changed = andElim(pc) + notElim(pc) + orElim(pc) + contraElim(pc) + condElim(pc);
		pc.printNewStatements();

		if( pc.checkGoalCondition() )
			return true;

		pc.applyNewStatements();

	} while( changed );
	return false;+/
}

