
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

/// Proves a goal by generating new statements from existing ones.
///
/// Currently it just applies all the rules to everything every step
/// and checks for the goal. There is no heuristic to speed things up.
class ForwardProver
{
	const(ForwardRule[]) mRules;

	/// Constructor. Pass in the set of rules to use in proofs.
	this(in ForwardRule[] rules) { mRules=rules; }

	enum ProofState { Failed=0, Changed, Success };

	/// Executes one step of a proof.
	///
	/// A step can be arbitrarily large, but is guarenteed to halt.
	/// Currently one step generates all possible new statements
	/// from only the current existing statements. Also runs one step
	/// of all subproofs.
	ProofState step(ProofContext context) const
	{
		// Print the statements that were previously generated
		context.printNewStatements();
		// Check for the goal
		if( context.checkGoalCondition() )
			return ProofState.Success;
		// Remove the 'new' status from the new statements (they become 'previous')
		context.applyNewStatements();

		// Step each subproof - this makes them run in parallel (not CPU parallel)
		// so that if any particular one does not halt, others will still continue
		foreach(subproof; context.openSubproofs)
		{
			step(subproof);
		}

		// ^ elim:  (and * * ...) ==> a, b
		// | elim:  (or * * ...) ==> sub(a), sub(b), ...

		// Apply each rule and keep track of how many new expressions were created
		uint cnt=0;
		foreach(rule; mRules)
		{
			cnt += rule(context);
		}

		// Return whether or not the proof has been updated
		return cnt > 0 ? ProofState.Changed : ProofState.Failed;
	}
}

/// Use the ForwardProver to generate a proof of the goal in pc.
///
/// Runs until the prover is successful or calling step() does
/// not result in new lines (indicating failure).
bool prove(ProofContext pc)
{
	assert(pc.goal.expression, "Must have a goal to prove");

	ForwardRule[] rules = [cast(ForwardRule)new AndElim(), cast(ForwardRule)new NotElim(), cast(ForwardRule)new OrElim(), cast(ForwardRule)new ContradictionElim(), cast(ForwardRule)new ConditionalElim()];
	auto prover = new ForwardProver(rules);

	ForwardProver.ProofState result;
	do
	{
		result = prover.step(pc);
	} while( result == ForwardProver.ProofState.Changed );

	return result == ForwardProver.ProofState.Success;
}

