
import std.algorithm;
import std.array;
import std.conv;
import std.range;

import expression;
import rules;

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

struct SupportRef
{
	ProofContext context=null;
	ulong line=ulong.max;
	@property bool supported() const pure { return context !is null; }
	string toString() const pure { return to!string(line); }
}
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

class ProofContext
{
protected:
	const(Statement)[] mStatements;
	ulong mPrevStatementIdx;
	ulong mNewStatementIdx;

	const(Expression[]) mSymbols;

	Statement mGoal;

	ProofContext mBase=null;
	uint mLevel;
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
	@property auto statements() const
	{
		return mStatements[0..mNewStatementIdx];
//		const(Statement[]) st = mStatements[0..mNewStatementIdx];
//		if( !mBase ) return chain!.Result(st, st.init);
//		auto result = chain(mBase ? mBase.statements : const(Statement[]).init, st);
//		return chain(mBase.statements, st.init);
	}
	@property const(Statement[]) newStatements() const
	{
		return mStatements[mNewStatementIdx..$];
	}
	@property const(Statement[]) prevStatements() const
	{
		return mStatements[mPrevStatementIdx..mNewStatementIdx];
	}
	@property const(Statement[]) allStatements() const
	{
		return mStatements;
		//return mBase ? chain(mBase.allStatements, mStatements) : mStatements;
	}
	@property const(Expression[]) symbols() const
	{
		return mSymbols;
	}
	@property const(Statement) goal() const { return mGoal; }
	@property Statement goal() { return mGoal; }
	@property auto level() const { return mLevel; }

	void newStatement(const Expression statement, const Rule rule, const SupportRef[] support)
	{
		mStatements ~= Statement(statement, support, rule);
	}
	/+void addStatement(in Expression statement) // TOO CONFUSING
	{
		mStatements.insertInPlace(mNewStatementIdx++, statement);
	}+/
	void applyNewStatements()
	{
		mPrevStatementIdx = mNewStatementIdx;
		mNewStatementIdx = mStatements.length;
	}
	ProofContext[] openSubproofs() pure
	{
		return mSubproofs;
	}
}


