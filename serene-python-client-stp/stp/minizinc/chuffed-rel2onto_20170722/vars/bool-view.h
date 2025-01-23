#ifndef bool_view_h
#define bool_view_h

#include "vars/vars.h"
#include "core/sat.h"

class Propagator;

class BoolView : public Var {
 public:
	int v;
	bool s;



	BoolView() {}
	BoolView(Lit p) : v(var(p)), s(sign(p)) {}

	friend BoolView operator ~(BoolView& o) { return BoolView(o.getLit(0)); }

	void setPreferredVal(PreferredVal p) {
		if (p == PV_MIN || p == PV_SPLIT_MIN) sat.polarity[v] = s^1;
		if (p == PV_MAX || p == PV_SPLIT_MAX) sat.polarity[v] = s;
	}

	void attach(Propagator *p, int pos, int eflags);
	void detach(Propagator *p, int pos, int eflags);

	// Read data:

	VarType getType() { return BOOL_VAR; }

	bool isFixed() const { return sat.assigns[v]; }
	bool isTrue()  const { return sat.assigns[v] == 1-2*s; }
	bool isFalse() const { return sat.assigns[v] == -1+2*s; }
	int  getVal()  const { assert(isFixed()); return (sat.assigns[v]+1)/2 ^ s; }

        int getMin() const {return isFixed() && isTrue() ? 1 : 0;}
        int getMax() const {return isFixed() && isFalse() ? 0 : 1;}
	bool indomain(int64_t v) const { assert(0 <= v && v <= 1); return !isFixed()? true : ((isTrue() && v) || (isFalse() && !v));}

	// Lit for explanations:

	Lit getValLit() const { if (!isFixed()){exit(1);} assert(isFixed()); return Lit(v, (sat.assigns[v]+1)/2); }
	Lit getLit(bool sign) const { return Lit(v, sign ^ s ^ 1); }

	// For Branching:

	bool finished() { return isFixed(); }
	double getScore(VarBranch vb) { NOT_SUPPORTED; }
	DecInfo* branch() { return new DecInfo(NULL, 2*v+(sat.polarity[v])); }

	// Change domains:

	bool setValNotR(bool x) const { return sat.assigns[v] != (x^s)*2-1; }

	bool setVal(bool x, Reason r = NULL) {
		assert(setValNotR(x));
		sat.cEnqueue(getLit(x), r);
		return (sat.confl == NULL);
	}

	bool setVal2(bool x, Reason r = NULL) {
		assert(setValNotR(x));
		sat.enqueue(getLit(x), r.pt);
		return (sat.confl == NULL);
	}

	operator Lit () const { return getLit(true); }
	Lit operator = (bool v) const { return getLit(v); }
	bool operator == (BoolView o) const { return v == o.v && s == o.s; }

        //For NonBinary Branching
        void getSetMinDec() {
            engine.branchingDescs.push();
            BranchingDesc& b = engine.branchingDescs.last();
            b.choices.push(DecInfo(NULL, 2*v+(s^1)));
            b.choices.push(DecInfo(NULL, 2*v+(s^0)));
        }

        void getSetMaxDec() {
            engine.branchingDescs.push();
            BranchingDesc& b = engine.branchingDescs.last();
            b.choices.push(DecInfo(NULL, 2*v+(s^0)));
            b.choices.push(DecInfo(NULL, 2*v+(s^1)));
        }


};

const BoolView bv_true(lit_True);
const BoolView bv_false(lit_False);

inline BoolView newBoolVar(int min = 0, int max = 1) {
	BoolView v(Lit(sat.newVar(),0));
        engine.bvars.push(v.v);
	if (min == 1) v.setVal(1);
	if (max == 0) v.setVal(0);
	return v;
}

#endif
