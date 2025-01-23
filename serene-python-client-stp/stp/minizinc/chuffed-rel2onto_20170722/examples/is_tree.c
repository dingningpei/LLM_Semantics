#include <cstdio>
#include <cassert>
#include "core/engine.h"
#include "core/propagator.h"
#include "branching/branching.h"
#include "vars/modelling.h"

#include <iostream>
using namespace std;


class IsTree : public Problem {

 public:
    int const nbv;
    int const nbe;
    vec<BoolView> vs;
    vec<BoolView> es;
    vec< vec<int> > adj;
    vec< vec<int> > endnodes;


    void K4(){
        //4 nodes
        //6 edges
        endnodes.push(vec<int>());
        endnodes[0].push(0);
        endnodes[0].push(1);
        endnodes.push(vec<int>());
        endnodes[1].push(1);
        endnodes[1].push(2);
        endnodes.push(vec<int>());
        endnodes[2].push(2);
        endnodes[2].push(3);
        endnodes.push(vec<int>());
        endnodes[3].push(3);
        endnodes[3].push(0);
        endnodes.push(vec<int>());
        endnodes[4].push(0);
        endnodes[4].push(2);
        endnodes.push(vec<int>());
        endnodes[5].push(1);
        endnodes[5].push(3);


        adj.push(vec<int>());
        adj[0].push(0);
        adj[0].push(3);
        adj[0].push(4);
        adj.push(vec<int>());
        adj[1].push(0);
        adj[1].push(1);
        adj[1].push(5);
        adj.push(vec<int>());
        adj[2].push(1);
        adj[2].push(2);
        adj[2].push(4);
        adj.push(vec<int>());
        adj[3].push(2);
        adj[3].push(3);
        adj[3].push(5);



        //*
        vs[0].setVal(1);
        vs[3].setVal(1);
        es[2].setVal(1);
        //*/
        /*
          vs[0].setVal(1);
          vs[3].setVal(1);
        //*/
        //Force failure
        /*
          vs[0].setVal(1);
          vs[1].setVal(1);
          vs[2].setVal(1);
          vs[3].setVal(1);
          es[0].setVal(1);
          es[1].setVal(1);
          es[2].setVal(1);
          es[3].setVal(1);
        //*/
        /*
          vs[0].setVal(1);
          vs[3].setVal(1);
          es[0].setVal(0);
          es[1].setVal(0);
          es[2].setVal(0);
          es[3].setVal(0);
        //*/
        /*
          vs[0].setVal(1);
          vs[3].setVal(1);
          es[2].setVal(1);
          vs[2].setVal(0);
        //*/
    }

    void ex2() {
        //6 nodes
        //5 or 6 edges

        endnodes.push(vec<int>());
        endnodes[0].push(0);
        endnodes[0].push(1);
        endnodes.push(vec<int>());
        endnodes[1].push(1);
        endnodes[1].push(2);
        endnodes.push(vec<int>());
        endnodes[2].push(2);
        endnodes[2].push(3);
        endnodes.push(vec<int>());
        endnodes[3].push(3);
        endnodes[3].push(0);
        endnodes.push(vec<int>());
        endnodes[4].push(4);
        endnodes[4].push(5);
        /*
        endnodes.push(vec<int>());
        endnodes[5].push(0);
        endnodes[5].push(4);
        //*/

        adj.push(vec<int>());
        adj[0].push(0);
        adj[0].push(3);
		
        //adj[0].push(5);
		
        adj.push(vec<int>());
        adj[1].push(0);
        adj[1].push(1);
        adj.push(vec<int>());
        adj[2].push(1);
        adj[2].push(2);
        adj.push(vec<int>());
        adj[3].push(2);
        adj[3].push(3);
        adj.push(vec<int>());
        adj[4].push(4);
		
        //adj[4].push(5);
		
        adj.push(vec<int>());
        adj[5].push(4);

        /*
        vs[0].setVal(1);
        vs[1].setVal(1);
        vs[2].setVal(1);
        vs[4].setVal(1);
        vs[5].setVal(1);

        es[0].setVal(1);
        es[1].setVal(1);
        es[2].setVal(1);
        es[4].setVal(1);
        //*/
        //es[5].setVal(1);
    }

 IsTree() : nbv(6),nbe(5){
		
        createVars(es, nbe);
        createVars(vs, nbv);


        //K4();
        ex2();

        tree(vs,es,adj,endnodes);

        vec<Branching*> ptrs;
        for(int i = 0; i < vs.size(); i++) {
            ptrs.push(&vs[i]);
        }
        branch(ptrs, VAR_INORDER, VAL_MIN);
        output_vars(ptrs);
        cout << engine.outputs.size() <<endl;
    }


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

    }

};

int main(int argc, char** argv) {
    parseOptions(argc, argv);

    engine.solve(new IsTree());

    return 0;
}
