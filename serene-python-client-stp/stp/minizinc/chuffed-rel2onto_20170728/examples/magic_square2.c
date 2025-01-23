#include <cstdio>
#include <cassert>
#include "support/vec.h"
#include "support/misc.h"
#include "core/engine.h"
#include "vars/vars.h"
#include "branching/branching.h"
#include "core/propagator.h"

class MagicSquare : public Problem {
public:
	const int n;
	const int sum;

	vec<vec<IntVar*> > x; // values

	MagicSquare(int _n) : n(_n), sum(n*(n*n+1)/2), x(n) {

		vec<IntVar*> a;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				IntVar *v = newIntVar(1,n*n);
				x[i].push(v);
				a.push(v);
			}
		}

		all_different(a);

		vec<IntVar*> empty;
		for (int i = 0; i < n; i++) {
			vec<IntVar*> column;
			for (int j = 0; j < n; j++) column.push(x[j][i]);
			//int_linear(x[i], IRT_EQ, sum);
			//int_linear(column, IRT_EQ, sum);
		}

		branch(a, VAR_INORDER, VAL_MIN);

	}

	void print() {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (x[i][j]->isFixed())
				printf("%3d ", x[i][j]->getVal());
				else
				printf("? ");
			}
			printf("\n");
		}
		printf("\n");
	}

};



int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 2);

	engine.solve(new MagicSquare(atoi(argv[1])));

	return 0;
}



