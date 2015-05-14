
import std.string;


/// Logic Expression containing either a single variable
/// or a predicate and one or more subexpressions.
class Expression
{
	/// Predicate or variable
	string mFunc;
	/// Subexpressions
	const(Expression)[] mArgs;

	this(string func) pure
	{
		mFunc = func;
	}
	this(string func, in Expression[] args) pure
	{
		mFunc = func;
		mArgs = args;
	}
	/// Add a subexpression as an argument to the predicate
	void add(Expression sub) pure
	{
		mArgs ~= sub;
	}

	override string toString() const pure
	{
		if( mArgs.length == 0 ) return mFunc;

		string[] argstr = [mFunc];
		foreach(arg; mArgs)
			argstr ~= arg.toString();
		return '('~argstr.join(" ")~')';
	}

	/// Full comparison between expressions.
	///
	/// Compares subexpressions for equality.
	bool compare(const(Expression) other) const pure
	{
		//writefln("Compare %s with %s", this, other);
		// Only variable substitution
		/+if( mArgs.length == 0 && other.mArgs.length == 0 )
		{
			if( mFunc == other.mFunc )
				return true;
			if( mFunc.length > 0 && mFunc[0]=='_' ) // starting with underscore are bound variables
				return true;
			if( other.mFunc.length > 0 && other.mFunc[0]=='_' )
				return true;
		}+/
		/+if( mArgs.length == 0 && mFunc.startsWith('_') )
			return true;
		if( other.mArgs.length == 0 && other.mFunc.startsWith('_') )
			return true;+/

		if( mFunc!=other.mFunc || mArgs.length != other.mArgs.length )
			return false;
		for(uint i=0; i<mArgs.length; i++)
		{
			if( !mArgs[i].compare(other.mArgs[i]) )
				return false;
		}
		return true;
	}
	/+
	/// Substitution for forAll Elim
	const(Expression) substitute(const(Expression) other, const(Expression) name) const pure
	{
		// 1. (forall x_ (MP (func1 x_) (func2 x_)) )
		// 2. (func1 a)
		//    --------------------
		// (MP (func1 x_) (func2 x_)).subst( (func1 a), x_ )
		// (func1 x_).subst( (func1 a), x_ ) ==> (func1 a)

		if( mArgs.length == 0 )
			return new Expression(name.mFunc);

		if( mFunc!=other.mFunc || mArgs.length != other.mArgs.length )
			return null;
		for(uint i=0; i<mArgs.length; i++)
		{
			if( !mArgs[i].substitute(other.mArgs[i], name) )
				return null;
		}
		return this;
	}
	const(Expression) substitute(string from, const(Expression) to, ref bool action) const pure
	{
		//writefln("SUBST CALLED %s (action %s)", this, action);
		if( mArgs.length == 0 )
		{
			//writefln("subst(%s) %s --> %s", mFunc, from, to);
			if( mFunc == from && to.mFunc != mFunc )
			{
				//writefln("subst(%s) %s --> %s PASS", mFunc, from, to);
				action = true;
				return to;
			}
			else
				return this;
		}
		bool changed = false;
		const(Expression)[] replacements;
		replacements.reserve(mArgs.length);
		for(uint i=0; i<mArgs.length; i++)
		{
			replacements ~= mArgs[i].substitute(from, to, changed);
			//writefln("Changed %s? %s", this, changed);
		}
		//writefln("Action %s? %s", this, action);
		action |= changed;
		//writefln("Action? %s", action);
		//if( changed )
		//	writefln("subst(%s) %s --> %s CHANGED: %s", this, from, to, new Expression(mFunc, replacements));
		return !changed ? this : new Expression(mFunc, replacements);
	}+/
	/// Return all symbols in all subexpressions (some may be listed more than once)
	const(Expression)[] getSymbols() const pure
	{
		if( mArgs.length == 0 )
			return [this];
		const(Expression)[] symbols;
		foreach(arg; mArgs)
			symbols ~= arg.getSymbols();
		return symbols;
	}

	/// Predicate or variable
	@property string func() const pure { return mFunc; }
	/// Subexpressions used as arguments to the predicate
	@property const(Expression)[] args() const pure { return mArgs; }
	/// How many arguments to the predicate
	@property auto nargs() const pure { return mArgs.length; }
}

