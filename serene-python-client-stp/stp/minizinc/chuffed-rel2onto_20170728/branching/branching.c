#include <new>
#include "branching/branching.h"
#include "vars/vars.h"
#include "core/engine.h"
#include "core/options.h"

BranchGroup::BranchGroup(VarBranch vb, bool t) :
	var_branch(vb), terminal(t), fin(0), cur(-1) {}

BranchGroup::BranchGroup(vec<Branching*>& _x, VarBranch vb, bool t) :
	x(_x), var_branch(vb), terminal(t), fin(0), cur(-1) {}

bool BranchGroup::finished() {
	if (fin) return true;
	for (int i = 0; i < x.size(); i++) {
		if (!x[i]->finished()) return false;
	}
	fin = 1;
	return true;
}

double BranchGroup::getScore(VarBranch vb) {
	double sum = 0;
	for (int i = 0; i < x.size(); i++) {
		sum += x[i]->getScore(vb);
	}
	return sum / x.size();
}

DecInfo* BranchGroup::branch() {
    //printf("Looking for new group\n");
	// If we're working on a group and it's not finished, continue there
	if (cur >= 0 && !x[cur]->finished()) return x[cur]->branch();

        //	printf("bra%d\n",var_branch);

	// Need to find new group
	if (var_branch == VAR_INORDER) {

		int i = 0;
		while (i < x.size() && x[i]->finished()) i++;
		if (i == x.size()) {
//			assert(is_top_level_branching);
			return NULL;
		}
		if (!terminal) cur = i;
		return x[i]->branch();
	}

	double best = -1e100;
	moves.clear();
	for (int i = 0; i < x.size(); i++) {
		if (x[i]->finished()) continue;
		double s = x[i]->getScore(var_branch);
		if (s >= best) {
			if (s > best) {
				best = s;
				moves.clear();
			}
			moves.push(i);
		}
	}
	if (moves.size() == 0) {
//		assert(is_top_level_branching);
		return NULL;
	}
	int best_i = moves[0];
	if (so.branch_random) best_i = moves[rand()%moves.size()];

//	printf("best = %.2f\n", best);
//	printf("%d: %d ", engine.decisionLevel(), best_i);

	if (!terminal) cur = best_i;
	return x[best_i]->branch();
}








class BranchNonBinary : public Branching {
 public:
    bool finished() { return var_sel(x) == NULL; }
    double getScore(VarBranch) {NOT_SUPPORTED;}

    vec<Branching*> x;
    Branching* (*var_sel) (vec<Branching*>& x);
    DecInfo* (*val_sel) (Branching *x);
    
    BranchNonBinary(vec<Branching*>& _x) : x(_x), var_sel(NULL), val_sel(NULL) {}
    DecInfo* branch() {	return val_sel(var_sel(x)); }
};

Branching* varSelINORDER(vec<Branching*>& x) {
	int i = 0;
	while (i < x.size() && x[i]->isFixed()) {
//		printf("%d = %d, ", ((IntVar*)x[i])->var_id, ((IntVar*)x[i])->getVal());
		i++;
	}
	if (i == x.size()) return NULL;
//	printf("Var choice = %d\n", ((IntVar*) x[i])->var_id);
	return x[i];
}


#define VAR_SEL(name, vtype, ival, ineq, vop)                 \
Branching* varSel ## name(vec<Branching*>& x) {                           \
	vtype m = ival;                                             \
	Branching *v = NULL;                                              \
	for (int i = 0; i < x.size(); i++) {                        \
		if (x[i]->isFixed()) continue;                           \
		if (x[i]->vop() ineq m) {                                 \
			v = x[i];                                               \
			m = x[i]->vop();                                        \
		}                                                         \
	}                                                           \
	return v;                                                   \
}

//VAR_SEL(DEFAULT, double, 2, <, getDefault)
VAR_SEL(DEFAULT,    int, INT_MAX, <, getSize)
VAR_SEL(SIZE_MIN,   int, INT_MAX, <, getSize)
VAR_SEL(SIZE_MAX,   int, INT_MIN, >, getSize)
VAR_SEL(MIN_MIN,    int, INT_MAX, <, getMin)
VAR_SEL(MAX_MAX,    int, INT_MIN, >, getMax)
VAR_SEL(DEGREE_MIN, int, INT_MAX, <, getDegree)
VAR_SEL(DEGREE_MAX, int, INT_MIN, >, getDegree)

//-----

// Select Val

DecInfo* valSelMIN(Branching *x) {
	if (!x) return NULL; 
	x->getSetMinDec();
	return &engine.branchingDescs.last().choices.last(); //Unused, just !NULL
}

DecInfo* valSelMAX(Branching *x) {
	if (!x) return NULL;
	x->getSetMaxDec();
	return &engine.branchingDescs.last().choices.last(); //Unused, just !NULL
}

DecInfo* valSelSPLIT_MIN(Branching *x) {
	if (!x) return NULL;
	x->getSplitMinDec();
	return &engine.branchingDescs.last().choices.last(); //Unused, just !NULL
}

DecInfo* valSelSPLIT_MAX(Branching *x) {
	if (!x) return NULL;
	x->getSplitMaxDec();
	return &engine.branchingDescs.last().choices.last(); //Unused, just !NULL
}


bool MinMinBranching::finished() { 
    int m = INT_MAX;
    int bchoices = 0;
    for (int i = 0; i < a.size(); i++) {
        if (a[i]->isFixed()) continue;
        if (a[i]->getMin() < m) {
            m = a[i]->getMin();
            bchoices = 0;
        }
        if (a[i]->getMin() == m) bchoices++;
    }
    return bchoices != 0;
}
DecInfo* MinMinBranching::branch() {
    engine.branchingDescs.push();
	BranchingDesc& b = engine.branchingDescs.last();

	int m = INT_MAX;

	for (int i = 0; i < a.size(); i++) {
//			a[i]->print();
		if (a[i]->isFixed()) continue;
		if (a[i]->getMin() < m) {
			m = a[i]->getMin();
			b.choices.clear();
		}
		if (a[i]->getMin() == m) b.choices.push(DecInfo(a[i], m, 1));
	}

	if (!b.choices.size()) {
		engine.branchingDescs.pop();
		return NULL;
	}

	return &b.choices.last();
}

NurseBranching::NurseBranching(vec<Branching*> _a, vec<int> vv) {
    int i = 0;
    for (i = 0; i < _a.size(); i++) {
        assert(_a[i]);
        a.push_back(_a[i]);
        ((Var*) a[i])->setPreferredVal(PV_MIN);
    }
    for (i = 1; i < vv.size(); i++) {
        p.push_back(vv[i]);
    }
    curr = 0;

}

DecInfo* NurseBranching::branch() {
    while (a[curr]->finished() && curr < a.size()) {
        curr++;
    }
    if (curr == a.size()) {
        assert(finished());
        return NULL;
    }
    if (a[curr]->indomain(p[curr])) {
        return new DecInfo(a[curr],p[curr],1);
    } else {
        return a[curr]->branch();
    }
}

bool NurseBranching::finished() {
    bool res = true;
    for (int  i = 0; i < a.size(); i++) {        
        if (!a[i]->finished()) 
            res = false;
    }
    return res;
}

BrRel2OntoCEFP::BrRel2OntoCEFP(vec<Branching*> _a, vec<int> data) : sorter(costs) {
	//std::cout<<"Building DS"<<std::endl;
	for (int i = 0; i < _a.size(); i++) {
		((Var*)_a[i])->setPreferredVal(PV_MAX);
		a.push_back(_a[i]);
		map.push_back(i);
	}

	int nb_costs = data[0];
	int nb_patts = data[1];
	//std::cout<<"nbEdges: "<<nb_costs<<std::endl;
	//std::cout<<"nbPatts: "<<nb_patts<<std::endl;
	int i = 2;
	//std::cout<<"costs ";
	for( ; i < 2 + nb_costs; i++) {
		costs.push_back(data[i]);
		epatt.push_back(std::vector<int>());
	//	std::cout<<data[i]<<",";
	}
	//std::cout<<std::endl;
	//std::cout<<"sizes ";
	int pos = i;
	for( ; i < pos + nb_patts; i++) {
		psize.push_back(data[i]);
		patts.push_back(std::vector<int>());
	//	std::cout<<data[i]<<",";
	}
	//std::cout<<std::endl;
	//std::cout<<"pcosts ";
	pos = i;
	for( ; i < pos + nb_patts; i++) {
		pcost.push_back(data[i]);
	//	std::cout<<data[i]<<";";
	}
	//std::cout<<std::endl;
	//std::cout<<"patts {";
	int p = 0;
	for( ; i < data.size(); i++) {
		patts[p].push_back(data[i] - 1);
		epatt[data[i] - 1].push_back(p);
	//	std::cout<<data[i]<<"-";
		if (patts[p].size() == psize[p]) {
			p++;
	//		std::cout<<"}{";
		}
	}
	//std::cout<<"}"<<std::endl;

	std::sort(map.begin(),map.end(),sorter);

	//std::cout<<"DONE"<<std::endl;

	curr = 0;
}
DecInfo* BrRel2OntoCEFP::branch() {
	while (a[map[curr]]->finished() && curr < map.size()) {
		curr++;
	}
	if (curr == map.size()) {
		assert(finished());
		return NULL;
	}
	int res_cost = costs[map[curr]];
	int arg_min = curr;
	for (int _i = curr; _i < a.size(); _i++) {
		if (a[map[_i]]->finished()) continue;
		int i = map[_i];
		for (int ep = 0; ep < epatt[i].size(); ep++) {
			int j = epatt[i][ep];
			int fixed = 0;
			for (int k = 0; k < patts[j].size(); k++) {
				if (a[patts[j][k]]->isFixed() && a[patts[j][k]]->getMin() == 1) 
					fixed++;
			}
			if (fixed == patts[j].size() - 1) {
				int nrc = costs[i] - pcost[j];
				if (nrc < res_cost) {
					res_cost = nrc;
					arg_min = _i;
				}
			}
		}
	}//*/
	assert(arg_min < a.size());
	assert(!a[map[arg_min]]->finished());
	//std::cout<<"Decision "<<arg_min<<" "<<a[map[arg_min]]<<" "<<engine.decisionLevel()<<" "<<curr<<std::endl;
	return a[map[arg_min]]->branch();//new DecInfo(a[arg_min],true,1);
}
bool BrRel2OntoCEFP::finished() {
	bool res = true;
	for (int  i = 0; i < a.size(); i++) {        
		if (!a[i]->finished()) 
			res = false;
	}
	return res;
}


//-----

void impact(vec<Var*>& x);

void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch, vec<int> vv) {

    if (!so.nonbinary) {
        switch(var_branch) {

        case NURSES_PREFS: 
            engine.branching->add(new NurseBranching(x,vv));
            break;
		case REL2ONTO_CEFP:
		     engine.branching->add(new BrRel2OntoCEFP(x,vv));
		     break;
        default:        
            engine.branching->add(new BranchGroup(x, var_branch, true));
            if (val_branch == VAL_DEFAULT) return;
            PreferredVal p;
            switch (val_branch) {
            case VAL_MIN: p = PV_MIN; break;
            case VAL_MAX: p = PV_MAX; break;
            case VAL_SPLIT_MIN: p = PV_SPLIT_MIN; break;
            case VAL_SPLIT_MAX: p = PV_SPLIT_MAX; break;
            default: NEVER;
            }
            for (int i = 0; i < x.size(); i++) ((Var*) x[i])->setPreferredVal(p);
        }

    } else {

	BranchNonBinary *b = new BranchNonBinary(x);

	#define VAR_CHOICE(name) case VAR_ ## name: b->var_sel = varSel ## name; break;

	switch (var_branch) {
		VAR_CHOICE(DEFAULT)
		VAR_CHOICE(INORDER)
		VAR_CHOICE(SIZE_MAX)
		VAR_CHOICE(SIZE_MIN)
		VAR_CHOICE(MIN_MIN)
		VAR_CHOICE(MAX_MAX)
		VAR_CHOICE(DEGREE_MIN)
		VAR_CHOICE(DEGREE_MAX)
		default: ERROR("Unknown VarBranch %d for non-binary branching\n", var_branch);
	}

	#define VAL_CHOICE(name) case VAL_ ## name: b->val_sel = valSel ## name; break;

	switch (val_branch) {
		case VAL_DEFAULT   : b->val_sel = valSelMIN; break;
		case VAL_MIN       : b->val_sel = valSelMIN; break;
		case VAL_MAX       : b->val_sel = valSelMAX; break;
		case VAL_SPLIT_MIN : b->val_sel = valSelSPLIT_MIN; break;
		case VAL_SPLIT_MAX : b->val_sel = valSelSPLIT_MAX; break;
		default: ERROR("Unknown ValBranch %d for non-binary branching\n", val_branch);
	}

	engine.branching->add(b);
    }

}


/*SEE globals/tsp_heldkarp... void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
	engine.branching->add(new BranchGroup(x, var_branch, true));
	if (val_branch == VAL_DEFAULT) return;
	PreferredVal p;
	switch (val_branch) {
		case VAL_MIN: p = PV_MIN; break;
		case VAL_MAX: p = PV_MAX; break;
		case VAL_SPLIT_MIN: p = PV_SPLIT_MIN; break;
		case VAL_SPLIT_MAX: p = PV_SPLIT_MAX; break;
		default: NEVER;
	}
	for (int i = 0; i < x.size(); i++) ((Var*) x[i])->setPreferredVal(p);
}
//*/
