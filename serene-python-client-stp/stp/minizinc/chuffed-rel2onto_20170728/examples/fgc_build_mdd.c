#include <iostream>
#include <cstdlib>
#include <cmath>
#include <algorithm>
#include <vector>
#include "circuit/FDNNF.h"
#include "mdd/MDD.h"
#include "circuit/CFG.h"
#include "circuit/CYK.h"
#include "globals/mddglobals.h"
#include "globals/circglobals.h"
#include "circuit/nnfprop.h"
#include "circuit/circ_fns.h"
#include "mdd/mdd_to_lgraph.h"
#include "mdd/wmdd_prop.h"

int main(int argc, char** argv)
{

    int foxes = atoi(argv[1]);
    int geese = atoi(argv[2]);
    int corns = atoi(argv[3]);
    
    std::cout<< " F: " <<foxes
             << " G: " <<geese
             << " C: " <<corns <<std::endl;


    /////////////////////////////////////////////////////////////////////////
    // predicate alone(var 0..1: b, var 0..f: fox0, var 0..f: fox1,        //
    //             var 0..g: geese0, var 0..g: geese1,                     //
    //     	var 0..c: corn0, var 0..c: corn1) =                        //
    //       if b == 1 then                                                //
    //       if fox0 = 0 /\ geese0 = 0                                     //
    //          \/ fox0 = 0 /\ corn0 = 0                                   //
    //          \/ geese0 = 0 /\ corn0 = 0                                 //
    //          \/ fox0 < 0                                                //
    //          \/ geese0 < 0                                              //
    //          \/ corn0 < 0                                               //
    //       then                                                          //
    //          fox1 = fox0 /\ geese1 = geese0 /\ corn1 = corn0            //
    //       elseif fox0 > 0 /\ geese0 > 0                                 //
    //       then                                                          //
    //           corn1 = corn0                                             //
    //           /\ if fox0 > geese0 then                                  //
    //     	    fox1 = fox0 - 1 /\ geese1 = geese0                     //
    //              else                                                   //
    //     	    fox1 = fox0 /\ geese1 = geese0 - fox0                  //
    //              endif                                                  //
    //       elseif geese0 = 0 /\ fox0 > 0 /\ corn0 > 0                    //
    //       then                                                          //
    //           fox1 = fox0 - 1 /\ geese1 = 0 /\ corn1 = corn0 - 1        //
    //       else                                                          //
    //           fox1 = 0                                                  //
    //           /\ if geese0 <= corn0 then                                //
    //     	    corn1 = corn0 - geese0 /\ geese1 = geese0              //
    //              else                                                   //
    //     	    corn1 = corn0 - 1 /\ geese1 = geese0 - 1               //
    //              endif                                                  //
    //        endif                                                        //
    //     else true endif;                                                //
    /////////////////////////////////////////////////////////////////////////

    int b = 0;
    int fox0 = 1;
    int fox1 = 2;
    int geese0 = 3;
    int geese1 = 4;
    int corn0 = 5;
    int corn1 = 6;

    MDDTable t(7); //7 vars    
    

    // corn1 = corn0 - 1 
    _MDD c1c0_1 = MDDFALSE;
    for (int i = 0; i < corns; i++) {
        _MDD c0 = t.mdd_vareq(corn0,i);
        _MDD c1 = t.mdd_vareq(corn1,i+1);
        _MDD _and = t.mdd_and(c0,c1);
        c1c0_1 = t.mdd_or(c1c0_1,_and);
    }
    //t.print_mdd(c1c0_1);
    // geese1 = geese0 - 1
    _MDD g1g0_1 = MDDFALSE;
    for (int i = 0; i < geese; i++) {
        _MDD g0 = t.mdd_vareq(geese0,i);
        _MDD g1 = t.mdd_vareq(geese1,i+1);
        _MDD _and = t.mdd_and(g0,g1);
        g1g0_1 = t.mdd_or(g1g0_1,_and);
    }
    //t.print_mdd(g1g0);
    //corn1 = corn0 - 1 /\ geese1 = geese0 - 1
    _MDD c1c0_1_g1g0_1 = t.mdd_and(g1g0_1,c1c0_1);


    //corn1 = corn0 - geese0
    _MDD c1c0g0 = MDDFALSE;
    for (int i = 0; i <= corns; i++) {
        _MDD c1 = t.mdd_vareq(corn1,i);
        for (int j = i; j <= corns; j++) {
            _MDD c0 = t.mdd_vareq(corn0,j);
            _MDD g0 = t.mdd_vareq(geese0,j-i);
            _MDD _and = t.mdd_and(c0,g0);
            _and = t.mdd_and(_and,c1);
            c1c0g0 = t.mdd_or(c1c0g0,_and);
        }
    }
    //t.print_mdd(c1c0g0);
    //geese1 = geese0
    _MDD g1g0 = MDDFALSE;
    for (int i = 0; i <= geese; i++) {
        _MDD g0 = t.mdd_vareq(geese0,i);
        _MDD g1 = t.mdd_vareq(geese1,i);
        _MDD _and = t.mdd_and(g0,g1);
        g1g0 = t.mdd_or(g1g0,_and);
    }
    //t.print_mdd(g1g0);
    // corn1 = corn0 - geese0 /\ geese1 = geese0
    _MDD c1c0g0_g1g0 = t.mdd_and(c1c0g0,g1g0);
    

    //geese0 <= corn0
    _MDD g0c0 = MDDFALSE;
    for (int i = 0; i <= geese; i++) {
        _MDD g0 = t.mdd_vareq(geese0,i);
        for (int j = i; j <= corns; j++) {
            _MDD c0 = t.mdd_vareq(corn0,j);
            _MDD _and = t.mdd_and(g0,c0);
            g0c0 = t.mdd_or(g0c0,_and); 
        }
    }
    //t.print_mdd(g0c0);

    //           fox1 = 0                                                  //
    //           /\ if geese0 <= corn0 then                                //
    //     	    corn1 = corn0 - geese0 /\ geese1 = geese0              //
    //              else                                                   //
    //     	    corn1 = corn0 - 1 /\ geese1 = geese0 - 1               //
    //              endif                                                  //
    _MDD last_else = t.mdd_and(t.mdd_vareq(fox1,0),
                               t.mdd_or(t.mdd_and(g0c0,c1c0g0_g1g0),
                                        t.mdd_and(t.mdd_not(g0c0), c1c0_1_g1g0_1)));
    //t.print_mdd(last_else);


    //           fox1 = fox0 - 1 /\ geese1 = 0 /\ corn1 = corn0 - 1        //
    _MDD f1f0_1 = MDDFALSE;
    for (int i = 0; i < foxes; i++) {
        _MDD f0 = t.mdd_vareq(fox0,i);
        _MDD f1 = t.mdd_vareq(fox1,i+1);
        _MDD _and = t.mdd_and(f0,f1);
        f1f0_1 = t.mdd_or(f1f0_1,_and);
    }    
    _MDD last_then_body = t.mdd_and(f1f0_1,
                               t.mdd_and(t.mdd_vareq(geese1,0),c1c0_1));
    //t.print_mdd(last_then_body);
    //       elseif geese0 = 0 /\ fox0 > 0 /\ corn0 > 0                    //
    _MDD f0_pos = MDDFALSE;
    for (int i = 1; i <= foxes; i++) {
        _MDD f0 = t.mdd_vareq(fox0,i);
        f0_pos = t.mdd_or(f0_pos,f0);
    }        
    _MDD c0_pos = MDDFALSE;
    for (int i = 1; i <= corns; i++) {
        _MDD c0 = t.mdd_vareq(corn0,i);
        c0_pos = t.mdd_or(c0_pos,c0);
    }    
    _MDD last_then_cond = t.mdd_and(t.mdd_vareq(geese0,0),
                                    t.mdd_and(f0_pos,c0_pos));
    //t.print_mdd(last_then_cond);



    //       then                                                          //
    //           corn1 = corn0                                             //
    //           /\ if fox0 > geese0 then                                  //
    //     	    fox1 = fox0 - 1 /\ geese1 = geese0                     //
    //              else                                                   //
    //     	    fox1 = fox0 /\ geese1 = geese0 - fox0                  //
    //              endif                                                  //
    
    _MDD c1c0 = MDDFALSE;
    for (int i = 0; i <= corns; i++) {
        _MDD c0 = t.mdd_vareq(corn0,i);
        _MDD c1 = t.mdd_vareq(corn1,i);
        _MDD _and = t.mdd_and(c0,c1);
        c1c0 = t.mdd_or(c1c0,_and);
    }    
    _MDD f1f0 = MDDFALSE;
    for (int i = 0; i <= foxes; i++) {
        _MDD f0 = t.mdd_vareq(fox0,i);
        _MDD f1 = t.mdd_vareq(fox1,i);
        _MDD _and = t.mdd_and(f0,f1);
        f1f0 = t.mdd_or(f1f0,_and);
    }    
    _MDD g1g0f0 = MDDFALSE;
    for (int i = 0; i <= geese; i++) {
        _MDD g1 = t.mdd_vareq(geese1,i);
        for (int j = i; j <= geese; j++) {
            _MDD g0 = t.mdd_vareq(geese0,j);
            _MDD f0 = t.mdd_vareq(fox0,j-i);
            _MDD _and = t.mdd_and(g0,f0);
            _and = t.mdd_and(_and,g1);
            g1g0f0 = t.mdd_or(g1g0f0,_and);
        }
    }
    _MDD f1f0_g1g0f0 = t.mdd_and(f1f0,g1g0f0);
    _MDD f1f0_1_g1g0 = t.mdd_and(f1f0_1,g1g0);
    _MDD f0g0 = MDDFALSE;
    for (int i = 0; i <= foxes; i++) {
        _MDD f0 = t.mdd_vareq(fox0,i);
        for (int j = 0; j < i; j++) {
            _MDD g0 = t.mdd_vareq(geese0,j);
            _MDD _and = t.mdd_and(f0,g0);
            f0g0 = t.mdd_or(f0g0,_and); 
        }
    }    
    _MDD middle_then_body = t.mdd_and(c1c0,
                                      t.mdd_or(t.mdd_and(f0g0,f1f0_1_g1g0),
                                               t.mdd_and(t.mdd_not(f0g0),f1f0_g1g0f0)));
    //t.print_mdd(middle_then_body);
    //       elseif fox0 > 0 /\ geese0 > 0                                 //
    _MDD g0_pos = MDDFALSE;
    for (int i = 1; i <= geese; i++) {
        _MDD g0 = t.mdd_vareq(geese0,i);
        g0_pos = t.mdd_or(g0_pos,g0);
    }        
    _MDD middle_then_cond = t.mdd_and(f0_pos,g0_pos);


    _MDD first_then_body = t.mdd_and(f1f0,t.mdd_and(c1c0,g1g0));
    //t.print_mdd(first_then_body);

    //       if fox0 = 0 /\ geese0 = 0                                     //
    //          \/ fox0 = 0 /\ corn0 = 0                                   //
    //          \/ geese0 = 0 /\ corn0 = 0                                 //
    //          \/ fox0 < 0                                                //
    //          \/ geese0 < 0                                              //
    //          \/ corn0 < 0                                               //
    _MDD first_then_cond = t.mdd_or(
                                    t.mdd_and(t.mdd_vareq(fox0,0),
                                              t.mdd_vareq(geese0,0)),
                                    t.mdd_or(
                                             t.mdd_and(t.mdd_vareq(fox0,0),
                                                       t.mdd_vareq(corn0,0)),
                                             t.mdd_and(t.mdd_vareq(geese0,0),
                                                       t.mdd_vareq(corn0,0))));
    //t.print_mdd(first_then_cond);
    

    _MDD all_conditions = t.mdd_or(
                                   t.mdd_or(
                                            t.mdd_and(first_then_cond,first_then_body),
                                            t.mdd_or(
                                                     t.mdd_and(middle_then_cond,middle_then_body),
                                                     t.mdd_and(last_then_cond,last_then_body))),
                                            last_else);
    //t.print_mdd(all_conditions);

    _MDD final = t.mdd_or(
                          t.mdd_and(t.mdd_vareq(b,1),all_conditions),
                          t.mdd_and(t.mdd_vareq(b,0),MDDTRUE));
    t.print_mdd(final);
        

    
    {
        MDD mdd;
        mdd.val = final;
        mdd.table = &t;
        std::unordered_map<_MDD, int> nmap;
        std::vector<int> rnmap;
        std::vector<int> ecount;
        std::vector<int> layer_length(7,0);
        int ncount = 2; //0 and 1 are FFF and TTT
        ecount.push_back(0);
        ecount.push_back(0);
        rnmap.push_back(0);
        rnmap.push_back(1);
        nmap[0] = 0;
        nmap[1] = 1;
    

        _MDD r = mdd.val;
        if(r == MDDFALSE) {
            ERROR("MDD is False!\n");
        }
        
        const std::vector<MDDNode>& nodes = mdd.table->getNodes();
        std::vector<_MDD> status(nodes.size());
        std::vector<_MDD> queued;
        queued.push_back(r);
        status[0] = 1;
        status[1] = 1;
        status[r] = 1;
        unsigned int head = 0;

        while( head < queued.size() )
        {
            _MDD n = queued[head];
            assert(nmap.find(n) == nmap.end());
            layer_length[nodes[n]->var]++;
            nmap[n] = ncount++;
            rnmap.push_back(n);
            ecount.push_back(nodes[n]->sz);
            for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ ) {
                if( status[nodes[n]->edges[jj].dest] == 0 ) {
                    status[nodes[n]->edges[jj].dest] = 1;
                    queued.push_back(nodes[n]->edges[jj].dest);
                }
            }
            head++;
        }

        //Number of nodes
        std::cout<< "mddnodes"<<so.mdd_name<<" = "<<ncount<<";\n";

        //Edge count
        std::cout<<"mddlayers"<<so.mdd_name<<" = [";
        for (int i = 0; i < layer_length.size(); i++) {
            std::cout<<layer_length[i];
            if (i < layer_length.size()-1)std::cout<<",";
        }
        std::cout<<"];\n";
        //Edges
        std::cout<<"mddedges"<<so.mdd_name<<" = [|";
        for (int i = 2; i < rnmap.size(); i++) {
            int n = rnmap[i];
            //Anything below the next edge goes to ...
            std::cout<<"-1"<<","<<nodes[n]->low<<"|"; 
            for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ ) {
                std::cout<<nodes[n]->edges[jj].val<<","<<nmap[nodes[n]->edges[jj].dest]<<"|";
            }       
        }
        std::cout<<"];\n";

    }    

    
  return 0;
}
