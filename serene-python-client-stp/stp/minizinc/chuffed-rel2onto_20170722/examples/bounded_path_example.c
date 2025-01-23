#include <cstdio>
#include <cassert>
#include "core/engine.h"
#include "core/propagator.h"
#include "branching/branching.h"
#include "vars/modelling.h"

#include <iostream>
using namespace std;

class BoundedPath : public Problem {
public:
    vec<BoolView> vs;                                 
    vec<BoolView> es;                                 
    vec<IntVar*> x;
    vec< vec<int> > in;
    vec< vec<int> > out;
    vec< vec<int> > endnodes;

    int n;
    int e;

    BoundedPath() {
        n = 5;
        e = 7;


        for (int i = 0; i < n; i++)
            in.push(vec<int>());
        in[1].push(0);
        in[1].push(1);
        in[2].push(2);
        in[2].push(3);
        in[3].push(4);
        in[3].push(6);
        in[4].push(5);

        for (int i = 0; i < n; i++)
            out.push(vec<int>());
        out[0].push(0);
        out[1].push(2);
        out[1].push(6);
        out[2].push(1);
        out[2].push(4);
        out[3].push(3);
        out[3].push(5);


        for (int i = 0; i < e; i++)
            endnodes.push(vec<int>());
        endnodes[0].push(0);
        endnodes[0].push(1);
        endnodes[1].push(2);
        endnodes[1].push(1);
        endnodes[2].push(1);
        endnodes[2].push(2);
        endnodes[3].push(3);
        endnodes[3].push(2);
        endnodes[4].push(2);
        endnodes[4].push(3);
        endnodes[5].push(3);
        endnodes[5].push(4);
        endnodes[6].push(1);
        endnodes[6].push(3);
            
        createVars(vs, n);
        createVars(es, e);
        createVars(x,1,0,7);

        // Post some constraints
        es[6].setVal(false,NULL);
        vs[0].setVal(true,NULL);
        vs[1].setVal(true,NULL);
        vs[2].setVal(true,NULL);
        vs[3].setVal(true,NULL);
        vs[4].setVal(true,NULL);

        vec<int> ws;
        ws.push(1);
        ws.push(4);
        ws.push(4);
        ws.push(2);
        ws.push(2);
        ws.push(1);
        ws.push(1);

        bounded_path(0,4,vs,es,in,out,endnodes,ws,x[0]);
        vec<Branching*> ptrs;
        for(int i = 0; i < vs.size(); i++) {
            ptrs.push(&vs[i]);
        }
        for(int i = 0; i < es.size(); i++) {
            ptrs.push(&es[i]);
        }
        if (x.size() > 0) {
            for(int i = 0; i < x.size(); i++) {
                ptrs.push(x[i]);
            }
        }
        branch(ptrs, VAR_INORDER, VAL_MIN);
        output_vars(ptrs);

    }

    // Function to print out solutio
    void print() {
        cout << "Nodes IN:" <<endl;
        for(int i = 0; i < vs.size(); i++){
            if (vs[i].isFixed() && vs[i].getVal() == 1)
                cout << i << endl;
        }
        cout<< endl;
        cout << "Nodes OUT:" <<endl;
        for(int i = 0; i < vs.size(); i++){
            if (vs[i].isFixed() && vs[i].getVal() == 0)
                cout << i << endl;
        }
        cout<< endl;
        cout << "Edges IN:" <<endl;
        for(int i = 0; i < es.size(); i++){
            if (es[i].isFixed() && es[i].getVal() == 1)
                cout << i << endl;
        }
        cout<< endl;
        cout << "Edges OUT:" <<endl;
        for(int i = 0; i < es.size(); i++){
            if (es[i].isFixed() && es[i].getVal() == 0)
                cout << i << endl;
        }
        cout<< "Done"<< endl;
        if (x.size() > 0) {
            cout <<"Weight: ";
            for(int i = 0; i < x.size(); i++){
                cout <<" (";
                IntVar::const_iterator it = x[i]->begin();
                //            (*x[i]).getVal() <<" ";
                for ( ; it != x[i]->end(); it++) {
                    cout << *it<<",";
                }
                cout <<") ";
            }
            cout<<endl;
        }
    }

};

int main(int argc, char** argv) {
	parseOptions(argc, argv);
	engine.solve(new BoundedPath());

	return 0;
}



