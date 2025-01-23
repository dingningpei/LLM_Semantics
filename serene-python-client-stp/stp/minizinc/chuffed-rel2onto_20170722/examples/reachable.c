#include <cstdio>
#include <cassert>
#include "core/engine.h"
#include "core/propagator.h"
#include "branching/branching.h"
#include "vars/modelling.h"

#include <iostream>
using namespace std;

class Reachable : public Problem {
public:
    vec<BoolView> vs;                                 
    vec<BoolView> es;                                 
    vec<IntVar*> x;
    vec< vec<int> > in;
    vec< vec<int> > out;
    vec< vec<int> > endnodes;

    int n;
    int e;

    Reachable() {
        n = 13;
        e = 21;


        for (int i = 0; i < n; i++)
            in.push(vec<int>());
        in[0].push(11);
        in[1].push(2);
        in[1].push(14);
        in[2].push(1);
        in[3].push(0);
        in[4].push(13);
        in[4].push(15);
        in[5].push(12);
        in[5].push(17);
        in[6].push(3);
        in[7].push(4);
        in[8].push(16);
        in[8].push(19);
        in[9].push(5);
        in[9].push(6);
        in[9].push(8);
        in[9].push(10);
        in[10].push(7);
        in[11].push(9);
        in[11].push(20);
        in[12].push(18);

        for (int i = 0; i < n; i++)
            out.push(vec<int>());
        out[0].push(0);
        out[0].push(1);
        out[0].push(2);
        out[1].push(15);
        out[2].push(12);
        out[2].push(14);
        out[2].push(13);
        out[3].push(3);
        out[3].push(4);
        out[4].push(18);
        out[5].push(16);
        out[6].push(5);
        out[7].push(6);
        out[7].push(7);
        out[8].push(17);
        out[8].push(20);
        out[9].push(9);
        out[10].push(8);
        out[11].push(10);
        out[11].push(11);
        out[12].push(19);


        for (int i = 0; i < e; i++)
            endnodes.push(vec<int>());
        endnodes[0].push(0);
        endnodes[0].push(3);
        endnodes[1].push(0);
        endnodes[1].push(2);
        endnodes[2].push(0);
        endnodes[2].push(1);
        endnodes[3].push(3);
        endnodes[3].push(6);
        endnodes[4].push(3);
        endnodes[4].push(7);
        endnodes[5].push(6);
        endnodes[5].push(9);
        endnodes[6].push(7);
        endnodes[6].push(9);
        endnodes[7].push(7);
        endnodes[7].push(10);
        endnodes[8].push(10);
        endnodes[8].push(9);
        endnodes[9].push(9);
        endnodes[9].push(11);
        endnodes[10].push(11);
        endnodes[10].push(9);
        endnodes[11].push(11);
        endnodes[11].push(0);
        endnodes[12].push(2);
        endnodes[12].push(5);
        endnodes[13].push(2);
        endnodes[13].push(4);
        endnodes[14].push(2);
        endnodes[14].push(1);
        endnodes[15].push(1);
        endnodes[15].push(4);
        endnodes[16].push(5);
        endnodes[16].push(8);
        endnodes[17].push(8);
        endnodes[17].push(5);
        endnodes[18].push(4);
        endnodes[18].push(12);
        endnodes[19].push(12);
        endnodes[19].push(8);
        endnodes[20].push(8);
        endnodes[20].push(11);

            
            
        createVars(vs, n);
        createVars(es, e);
        
        // Post some constraints
        //vs[0].setVal(true,NULL);
          vs[8].setVal(true,NULL);
          vs[12].setVal(true,NULL);
          es[0].setVal(false,NULL); 

        //es[2].setVal(false,NULL);
        //es[14].setVal(false,NULL);
          es[15].setVal(false,NULL);


        // vs[0].setVal(true,NULL);
        // vs[1].setVal(true,NULL);
        // vs[2].setVal(true,NULL);
        // vs[4].setVal(true,NULL);
        // vs[5].setVal(true,NULL);
        // vs[8].setVal(true,NULL);
        // vs[12].setVal(true,NULL);

        // vs[3].setVal(false,NULL);
        // vs[6].setVal(false,NULL);
        // vs[7].setVal(false,NULL);
        // vs[9].setVal(false,NULL);
        // vs[10].setVal(false,NULL);
        // vs[11].setVal(false,NULL);

        // es[1].setVal(true,NULL);
        // es[2].setVal(true,NULL);
        // es[12].setVal(true,NULL);
        // es[13].setVal(true,NULL);
        // es[14].setVal(true,NULL);
        // es[16].setVal(true,NULL);
        // es[18].setVal(true,NULL);

        // es[0].setVal(false,NULL);
        // es[3].setVal(false,NULL);
        // es[4].setVal(false,NULL);
        // es[5].setVal(false,NULL);
        // es[6].setVal(false,NULL);
        // es[7].setVal(false,NULL);
        // es[8].setVal(false,NULL);
        // es[9].setVal(false,NULL);
        // es[10].setVal(false,NULL);
        // es[11].setVal(false,NULL);
        // es[15].setVal(false,NULL);
        // es[17].setVal(false,NULL);
        // es[19].setVal(false,NULL);
        // es[20].setVal(false,NULL);

        

        /*
        vs[0].setVal(true,NULL);
        vs[2].setVal(true,NULL);
        vs[4].setVal(true,NULL);
        vs[8].setVal(true,NULL);
        vs[11].setVal(true,NULL);
        vs[12].setVal(true,NULL);
        vs[1].setVal(false,NULL);
        vs[3].setVal(false,NULL);
        vs[5].setVal(false,NULL);
        vs[6].setVal(false,NULL);
        vs[7].setVal(false,NULL);
        vs[9].setVal(false,NULL);
        vs[10].setVal(false,NULL);

        es[1].setVal(true,NULL);
        es[13].setVal(true,NULL);
        es[18].setVal(true,NULL);
        es[19].setVal(true,NULL);
        es[20].setVal(true,NULL);
        es[11].setVal(true,NULL);
        */
        //dreachable(0,vs,es,in,out,endnodes);


        /*        vs[0].setVal(true,NULL);
        vs[1].setVal(true,NULL);
        vs[2].setVal(true,NULL);
        vs[4].setVal(true,NULL);
        vs[5].setVal(true,NULL);
        vs[8].setVal(true,NULL);
        vs[9].setVal(true,NULL);
        vs[11].setVal(true,NULL);
        vs[12].setVal(true,NULL);
        vs[3].setVal(false,NULL);
        vs[6].setVal(false,NULL);
        vs[7].setVal(false,NULL);
        vs[10].setVal(false,NULL);

es[0].setVal(false,NULL);
es[3].setVal(false,NULL);
es[4].setVal(false,NULL);
es[5].setVal(false,NULL);
es[6].setVal(false,NULL);
es[7].setVal(false,NULL);
es[8].setVal(false,NULL);
es[9].setVal(false,NULL);
es[17].setVal(false,NULL);

es[1].setVal(true,NULL);
es[2].setVal(true,NULL);
es[10].setVal(true,NULL);
es[11].setVal(true,NULL);
es[12].setVal(true,NULL);
es[13].setVal(true,NULL);
es[14].setVal(true,NULL);
es[15].setVal(true,NULL);
es[16].setVal(true,NULL);
es[18].setVal(true,NULL);
es[19].setVal(true,NULL);
es[20].setVal(true,NULL);*/



          
          /*es[1].setVal(true,NULL);
          es[10].setVal(true,NULL);
          es[13].setVal(true,NULL);
          es[17].setVal(true,NULL);
          es[18].setVal(true,NULL);
          es[19].setVal(true,NULL);
          es[20].setVal(true,NULL);
          //es[0].setVal(false,NULL);
          es[2].setVal(false,NULL);
          es[3].setVal(false,NULL);
          es[4].setVal(false,NULL);
          es[5].setVal(false,NULL);
          es[6].setVal(false,NULL);
          es[7].setVal(false,NULL);
          es[8].setVal(false,NULL);
          es[9].setVal(false,NULL);
          es[11].setVal(false,NULL);
          es[12].setVal(false,NULL);
          es[14].setVal(false,NULL);
          //es[15].setVal(false,NULL);
          es[16].setVal(false,NULL);
          vs[0].setVal(true,NULL);
          //*/

          dag(0,vs,es,in,out,endnodes);
          //dreachable(0,vs,es,in,out,endnodes);
        //vs[0].setVal(true,NULL);
        //vs[8].setVal(true,NULL);
        //dtree(0,vs,es,in,out,endnodes);
        //reversedtree(8,vs,es,in,out,endnodes);
          //path(0,8,vs,es,in,out,endnodes);

          //createVars(x, vs.size(), 0, vs.size());
          //pathsucc(0,8,vs,es,x,in,out,endnodes);
          //dptree(0,vs,es,x,in,out,endnodes);
          //dtree(0,vs,es,in,out,endnodes);
        //reversedptree(0,vs,es,x,in,out,endnodes);
        //reversedtree(0,vs,es,in,out,endnodes);

        vec<Branching*> ptrs;
        for(int i = 0; i < vs.size(); i++) {
            ptrs.push(&vs[i]);
        }
        for(int i = 0; i < es.size(); i++) {
            ptrs.push(&es[i]);
        }
        if (x.size() > 0) {
            for(int i = 0; i < vs.size(); i++) {
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
            cout <<"Parents: ";
            for(int i = 0; i < vs.size(); i++){
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
	engine.solve(new Reachable());

	return 0;
}



