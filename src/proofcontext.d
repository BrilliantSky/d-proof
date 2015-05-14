
import std.algorithm;
import std.array;
import std.conv;
import std.range;

import expression;
import rules;

/// Extracts all variables from the statements
const(Expression)[] getSymbols(const(Expression)[] statements)
{
	bool[const(Expression)] contained;
	const(Expression)[] symbols;

	foreach(p; statements)
	{
		foreach(symbol; p.getSymbols())
		{
			if( symbol in contained )
				continue;
			symbols ~= symbol;
			contained[symbol] = true;
		}
	}
	return symbols;
}

/// Defines a context and line number for support information
struct SupportRef
{
	ProofContext context=null;
	ulong line=ulong.max;
	@property bool supported() const pure { return context !is null; }
	string toString() const pure { return to!string(line); }
}
/// A single expression with support rule and referenced statements
struct Statement
{
	const Expression expression;
	const SupportRef[] supportStatements;
	const Rule supportRule;
	string toString() const pure
	{
		return expression.toString() ~ " [" ~ supportRule.toString() ~ " " ~ join(map!(to!string)(supportStatements), ", ") ~ "]";
	}
}

static const(Rule) ASSUMED = new const AssumptionRule();

/// Current state of a proof containing statements and a goal.
///
/// May contain subproof contexts and keeps track of recently
/// added statements. This class represents a proof, but does
/// not contain any proof algorithms.
class ProofContext
{
protected:
	const(Statement)[] mStatements;
	ulong mPrevStatementIdx;
	ulong mNewStatementIdx;

	// What symbols are present
	const(Expression[]) mSymbols;

	// The goal statement
	Statement mGoal;

	// Parent ProofContexxt, if any
	ProofContext mBase=null;
	uint mLevel; // How many levels deep?
	ProofContext[] mSubproofs;
protected:
public:
	this(in const(Expression)[] premises, Expression goal=null)
	{
		auto empty = (ulong[]).init;
		auto tmp = map!(e => Statement(e, [], ASSUMED))(premises);
		mStatements ~= array(tmp);

		mSymbols = getSymbols(premises);
		//applyNewStatements();
		mGoal.expression = goal;
		mLevel=0;
	}
	this(ProofContext base, in Expression goal=null)
	{
		mBase = base;
		mStatements ~= base.mStatements;
		mSymbols = base.mSymbols;
		applyNewStatements();
		mGoal.expression = goal;
		mLevel = base.mLevel+1;
	}
	/// All statements except for the newly created ones
	@property auto statements() const
	{
		return mStatements[0..mNewStatementIdx];
//		const(Statement[]) st = mStatements[0..mNewStatementIdx];
//		if( !mBase ) return chain!.Result(st, st.init);
//		auto result = chain(mBase ? mBase.statements : const(Statement[]).init, st);
//		return chain(mBase.statements, st.init);
	}
	/// Only the newly created statements
	@property const(Statement[]) newStatements() const
	{
		return mStatements[mNewStatementIdx..$];
	}
	/// Only the statements from the previous step
	@property const(Statement[]) prevStatements() const
	{
		return mStatements[mPrevStatementIdx..mNewStatementIdx];
	}
	/// Every single statement
	@property const(Statement[]) allStatements() const
	{
		return mStatements;
		//return mBase ? chain(mBase.allStatements, mStatements) : mStatements;
	}
	/// Symbols extracted from the arguments
	@property const(Expression[]) symbols() const
	{
		return mSymbols;
	}
	/// Get the goal statement
	@property const(Statement) goal() const { return mGoal; }
	/// Ditto
	@property Statement goal() { return mGoal; }

	@property auto level() const { return mLevel; }

	/// Create a new statement, supported by $(PARAM rule) and referencing $(PARAM support) statements
	///
	/// The new statement is added to the list, but will not be returned by statements() until
	/// applyNewStatements() is called. Then it will become a previous statement, and then a normal
	/// statement when applyNewStatements() is called again.
	void newStatement(const Expression statement, const Rule rule, const SupportRef[] support)
	{
		mStatements ~= Statement(statement, support, rule);
	}
	/+void addStatement(in Expression statement) // TOO CONFUSING
	{
		mStatements.insertInPlace(mNewStatementIdx++, statement);
	}+/
	/// Turn new statements into previous statements, and previous statements into regular statements.
	///
	/// This functionality allows rules to only process changes to the proof rather than having to
	/// redo work already done.
	void applyNewStatements()
	{
		mPrevStatementIdx = mNewStatementIdx;
		mNewStatementIdx = mStatements.length;
	}
	/// Get all the subproofs
	ProofContext[] openSubproofs() pure
	{
		return mSubproofs;
	}
}


