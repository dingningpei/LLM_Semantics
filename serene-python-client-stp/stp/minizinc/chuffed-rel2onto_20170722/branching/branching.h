#ifndef branching_h
#define branching_h

#include <cstdio>
#include <cassert>
#include <climits>
#include "support/misc.h"
#include "core/engine.h"

//-----

enum VarBranch {
	VAR_DEFAULT,             // autonomous search
	VAR_INORDER,             // inorder
        TSP_STRATEGY,            //For TSP
	DCMST_ORDER,             // for DCMST problems
	PRIM_ORDER,              // for trees, follow prim's algorithm
	SHORTEST_PATH_ORDER,     // for SP problems
	CLOSESTNEXT_ORDER,     // for SP problems
        NURSES_PREFS,
	VAR_SIZE_MIN,            // smallest domain 
	VAR_SIZE_MAX,            // largest domain
	VAR_MIN_MIN,             // smallest smallest value in domain
	VAR_MIN_MAX,             // largest smallest value in domain
	VAR_MAX_MIN,             // smallest largest value in domain
	VAR_MAX_MAX,             // largest largest value in domain
	VAR_DEGREE_MIN,          // smallest degree
	VAR_DEGREE_MAX,          // largest degree
	VAR_REGRET_MIN_MAX,      // largest min regret
	VAR_REGRET_MAX_MAX,      // largest max regret
	VAR_REDUCED_COST,        // largest reduced cost from MIP
	VAR_PSEUDO_COST,         // largest pseudo cost from MIP
	VAR_ACTIVITY,            // largest vsids activity
	VAR_RANDOM               // random
};

//-----

enum ValBranch {
	VAL_DEFAULT,            // preferred pol (static), then global pol (dynamic)
	VAL_MIN,                // smallest value
	VAL_MAX,                // largest value
	VAL_MIDDLE,             // middle value
	VAL_MEDIAN,             // median value
	VAL_SPLIT_MIN,          // lower half
	VAL_SPLIT_MAX,          // upper half
	VAL_RANDOM              // random
};

class Tint;

struct DecInfo {
	void *var; int val; int type;
	DecInfo(void *_var, int _val, int _type = -1) :
		var(_var), val(_val), type(_type) {}
};

class Branching {
public:
	virtual bool finished() = 0;
	virtual double getScore(VarBranch vb) = 0;
	virtual DecInfo* branch() = 0;


    //For NonBinary Branching
	virtual void getDefaultDec()  { getSetMinDec(); }
	virtual void getSetMinDec()   { NEVER; }
	virtual void getSetMaxDec()   { NEVER; }
	virtual void getSplitMinDec() { NEVER; }
	virtual void getSplitMaxDec() { NEVER; }
        virtual bool isFixed() const { NEVER; }
	virtual int  getSize()    const { NEVER; }
	virtual int  getDegree()  const { NEVER; }
	virtual int  getMin()  const { NEVER; }
	virtual int  getMax()  const { NEVER; }
	virtual bool indomain(int64_t v) const {NEVER; }
};


class BranchGroup : public Branching {
public:
	vec<Branching*> x;
	VarBranch var_branch;
	bool terminal;

	// Persistent data
	Tint fin;
	Tint cur;

	// Intermediate data
	vec<int> moves;

	BranchGroup(VarBranch vb = VAR_INORDER, bool t = false);
	BranchGroup(vec<Branching*>& _x, VarBranch vb, bool t = false);

	bool finished();
	double getScore(VarBranch vb);
	DecInfo* branch();

	void add(Branching *n) { x.push(n); }

};

void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch, vec<int> vv  = vec<int>());

//For NonBinary Branching
class BranchingDesc {
public:
	int alt;
	vec<DecInfo> choices;

	BranchingDesc() : alt(0) {}

	bool finished() { return alt == choices.size(); }
};


class MinMinBranching : public Branching {
public:
	vec<Branching*> a;
	MinMinBranching(vec<Branching*> _a) : a(_a) {}
	DecInfo* branch();
    bool finished();
    double getScore(VarBranch vb) { NOT_SUPPORTED; }
};

class NurseBranching : public Branching {
public:
    std::vector<Branching*> a;
    std::vector< int > p;
    Tint* tested;
    Tint curr;
    NurseBranching(vec<Branching*> _a, vec<int> vv);
    DecInfo* branch();
    bool finished();
    double getScore(VarBranch vb) { NOT_SUPPORTED; }
};

#endif
