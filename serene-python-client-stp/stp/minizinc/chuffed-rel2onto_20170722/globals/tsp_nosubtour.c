#include "tsp_nosubtour.h"

using namespace std;



//This propagator ABSOLUTELLY need the graph to be connectred when it is called.
// Make sure a conneced or biconnecte proagator runs before!


NoSubtourPropagator::NoSubtourPropagator(vec<BoolView>& _vs, vec<BoolView>& _es,
                                         vec< vec<edge_id> >& _adj, vec< vec<int> >& _en)
    : GraphPropagator(_vs,_es,_en),ruf(nbNodes()) {
    priority = 3;

    for (int i = 0; i < nbEdges(); i++) {
        getEdgeVar(i).attach(this, i, EVENT_LU);
    }
    for (int i = 0; i < nbNodes(); i++) 
        if (getNodeVar(i).setValNotR(true))
            getNodeVar(i).setVal(true); //TSP, all necessary

    nodes2edge = std::vector<std::vector<int> >(nbNodes());
    for (int i = 0; i < nbNodes(); i++) 
        nodes2edge[i] = std::vector<int>(nbNodes(),-1);    
    for (int e = 0; e < nbEdges(); e++) {
        nodes2edge[getEndnode(e,0)][getEndnode(e,1)] = e;
        nodes2edge[getEndnode(e,1)][getEndnode(e,0)] = e;
    }

    adj = vector<vector<int> >(_adj.size(), vector<int>());    
    for (int i = 0; i < nbNodes(); i++)  {
        for (int j = 0; j < _adj[i].size(); j++)  {
            adj[i].push_back(_adj[i][j]);
        }        
    }

    in_edges_tsize = 0;
    in_edges_size = 0;
    last_state_e = vector<Tint>(nbEdges(),UNK);

    extremity1 = vector<Tint>(nbNodes());
    for (int i = 0; i < nbNodes(); i++) extremity1[i] = i;
    extremity2 = vector<Tint>(nbNodes());
    for (int i = 0; i < nbNodes(); i++) extremity2[i] = i;
    chainl = vector<Tint>(nbNodes(),1);
    
}

void NoSubtourPropagator::update_inedges() {
    if (in_edges_tsize < in_edges_size) {
        in_edges.resize(in_edges_tsize);
        in_edges_size = in_edges_tsize;
    }
}

void NoSubtourPropagator::add_inedge(int i) {
    if(last_state_e[i] != IN) {
        last_state_e[i] = IN;
        in_edges.push_back(i);
        in_edges_tsize++;
        in_edges_size++;    
        new_in_edges.push_back(i);
    }
}



void NoSubtourPropagator::wakeup(int i, int c) {
    update_inedges();

    if (getEdgeVar(i).isTrue() && last_state_e[i] != IN) {
        //cout<<" Added edge "<<i<<" "<<getEndnode(i,0)<<" "<<getEndnode(i,1)<<" "<<endl;
        add_inedge(i);
        pushInQueue();
    } 
}

Tint& NoSubtourPropagator::other_extremity(int node) {
    if (extremity1[node] == node) 
        return extremity2.at(node);
    return extremity1.at(node);
}

bool NoSubtourPropagator::propagate() {
    update_inedges();

    //string deb ="";
    //for (int i = 0; i < in_edges.size(); i++)
    //    deb += "("+to_string(getEndnode(in_edges[i],0))+","+to_string(getEndnode(in_edges[i],1))+") ";
    //cout<<"================================================PROPAGATE "<<__FILE__<<" "<<deb<<endl;
    Clause* r = NULL;
    vec<Lit> ps; ps.push(getNodeVar(0).getValLit()); //dummy
    

    for (int i = 0; i < new_in_edges.size(); i++) {
        
        int e = new_in_edges[i];
        int a = getEndnode(e,0);
        int b = getEndnode(e,1);

        //cout<<"Added Edge "<< a<<" to "<<b<<" "<<endl;
        //Add this edge e to the data structures,
        //check after if there is a problem.
        int ext_a = other_extremity(a);
        int ext_b = other_extremity(b);
        other_extremity(ext_a) = ext_b;
        other_extremity(ext_b) = ext_a;
        int t = chainl[ext_a] + chainl[ext_b];
        chainl[ext_a] = t;
        chainl[ext_b] = t;

        //Try to unite. It may not unite if it's the last edge in the ham-cycle
        ruf.unite(a,b); 

        if (t > 2) { 
            int expl_len = 0;
            if (so.lazy) {
                vector<int> path = ruf.connectionsFromTo(ext_a,ext_b);
                for(int k = 0; k < path.size() - 1; k++) {
                    assert(nodes2edge[path[k]][path[k+1]] != -1);
                    assert(getEdgeVar(nodes2edge[path[k]][path[k+1]]).isTrue());
                    ps.push(getEdgeVar(nodes2edge[path[k]][path[k+1]]).getValLit());
                    expl_len++;
                }
                //fullExpl(ps);
            }
            if (t < nbNodes()) {
                assert(ruf.connected(ext_a,ext_b));
                assert(expl_len < nbNodes() -1);
                //Remove the edge between extremities, if possible.
                int e_ext = nodes2edge[ext_a][ext_b];
                if (!getEdgeVar(e_ext).isFixed()) {                    
                    if(so.lazy) 
                        r = Reason_new(ps);
                    getEdgeVar(e_ext).setVal(false,r);
                } else if (getEdgeVar(e_ext).isTrue()) {
                    if(so.lazy) {
                        Clause *expl = Clause_new(ps);
                        expl->temp_expl = 1;
                        sat.rtrail.last().push(expl);
                        sat.confl = expl;        
                    }         
                    return false;
                }
            } else if (t == nbNodes()) {
                //Cycle is full, add the last edge
                int e_ext = nodes2edge[ext_a][ext_b];
                if (!getEdgeVar(e_ext).isFixed()) {
                    if(so.lazy) r = Reason_new(ps);
                    getEdgeVar(e_ext).setVal(true,r);
                    add_inedge(e_ext);
                }
            }
        }
    }

    // cout<<"Ext1: ";
    // for (int i = 0; i < extremity1.size(); i++) {
    //     cout<<extremity1[i]<<" ";
    // }
    // cout<<endl;
    // cout<<"Ext2: ";
    // for (int i = 0; i < extremity2.size(); i++) {
    //     cout<<extremity2[i]<<" ";
    // }
    // cout<<endl;
    // cout<<"Size ";
    // for (int i = 0; i < chainl.size(); i++) {
    //     cout<<chainl[i]<<" ";
    // }
    // cout<<endl;
    // cout<<available_to_dot()<<endl;

    return true;
}

void NoSubtourPropagator::clearPropState() {
    GraphPropagator::clearPropState();
    new_in_edges.clear();
}

