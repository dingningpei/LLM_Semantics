#include "cycle_cost_simple.h"

#include <unordered_map>
#include <limits>
#include <cmath>
#include <iomanip>
#include <sstream>

using namespace std;


CycleCostSimple::CycleCostSimple(vec<BoolView>& _vs, vec<BoolView>& _es, 
                             vec< vec<edge_id> >& _adj, vec< vec<int> >& _en,
                             IntVar* _w, vec<int>& _ws)
    : GraphPropagator(_vs,_es,_en), obj(_w) {
    priority = 3;

    original_ws = new int[nbEdges()];
    for (int i = 0; i < nbEdges(); i++) {
        original_ws[i] = _ws[i];
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


    in_edges_tsize = 0;
    in_edges_size = 0;
    last_state_e = vector<Tint>(nbEdges(),OUT);
    //All out unless you see them, then they are unknown.

    neigh_sizes = new Tint[nbNodes()];
    adj = vector<vector<int> >(_adj.size(), vector<int>());    
    adj_map = vector<vector<int> >(_adj.size(), vector<int>());    
    for (int i = 0; i < nbNodes(); i++)  {
        adj[i] = vector<int>(_adj[i].size(), -1);
        adj_map[i] = vector<int>(nbEdges(), -1);
        for (int j = 0; j < _adj[i].size(); j++)  {
            adj[i][j] = _adj[i][j];
            last_state_e[adj[i][j]] = UNK;
            adj_map[i][_adj[i][j]] = j;
        }        
        neigh_sizes[i] = adj[i].size();
    }



    obj->attach(this,-1,EVENT_LU);

    //Build arrays anf fill them
    mand1 = new Tint[nbNodes()]; std::memset(mand1,-1,sizeof(Tint)*nbNodes());
    mand2 = new Tint[nbNodes()]; std::memset(mand2,-1,sizeof(Tint)*nbNodes());
    for (int e = 0; e < nbEdges(); e++)
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
            update_mand_vectors(e);

}

bool CycleCostSimple::update_mand_vectors(int edge) {
    int u =  getEndnode(edge,0);
    int v =  getEndnode(edge,1);

    if (mand1[u] == -1) {
        mand1[u] = edge;
    } else if(mand2[u] == -1 && mand1[u] != edge) {
        mand2[u] = edge;
    }

    if (!(mand1[u] == edge || mand2[u] == edge))
        return false;

    if (mand1[v] == -1) {
        mand1[v] = edge;
    } else if(mand2[v] == -1 && mand1[v] != edge) {
        mand2[v] = edge;
    }

    if (!(mand1[v] == edge || mand2[v] == edge))
        return false;

    return true;
}

void CycleCostSimple::repair_backtrack() {
    if (in_edges_tsize < in_edges_size) {
        //cout<<"Backtracked"<<endl;
        in_edges.resize(in_edges_tsize);
        in_edges_size = in_edges_tsize;
    }
}

bool CycleCostSimple::add_inedge(int i) {
    if(last_state_e[i] != IN) {
        in_edges.push_back(i);
        last_state_e[i] = IN;
        in_edges_tsize++;
        in_edges_size++;    
        bool ok = update_mand_vectors(i);

        for (int j = 0; j < 2; j++) {
            int u = getEndnode(i,j);
            int pos = adj_map[u][i];
            int last = adj[u][neigh_sizes[u] - 1];
            adj[u][pos] = last; //the last edge goes wherever 'i' was
            adj_map[u][last] = pos;
            adj[u][neigh_sizes[u] - 1] = i; //removed edge goes at the back
            adj_map[u][i] = neigh_sizes[u] - 1;
            neigh_sizes[u]--;
        }

    }
    return true;
}


bool CycleCostSimple::check_two_edges(int n, int e1, int e2) {
    if(e1 == -1 || e2 == -1) {
        vec<Lit> psf;
        if (so.lazy) {
            for (unsigned int i = neigh_sizes[n]; i < adj[n].size(); i++) {
                int e = adj[n][i];
                if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
                    psf.push(getEdgeVar(e).getValLit());
                }
            }
            Clause *expl = Clause_new(psf);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;                                
        }
        return false;
    }
    return true;
}

bool CycleCostSimple::filter_expensive_edges_simple() {
    int lb = 0;
    int ub = 0;
    vector<int> replacement(nbNodes(),-1);
    vec<Lit> expl; expl.push();
    vector<int> e1s(nbNodes(),-1);
    vector<int> e2s(nbNodes(),-1);

    for (int n = 0; n < nbNodes(); n++) {
        int e1, e2;
        find_two_cheapest(n,e1,e2,original_ws,expl);
        if(!check_two_edges(n,e1,e2)) 
            return false;
        assert(e1 != -1 && e2 != -1);
        e1s[n] = e1;
        e2s[n] = e2;
        lb += original_ws[e1] + original_ws[e2];
        replacement[n] = original_ws[e2];
    }
    lb /= 2;

    Clause* r = NULL;
    if(so.lazy) {
        expl.push(obj->getMaxLit());
        //fullExpl(expl);
        r = Reason_new(expl);
    }

    int delta = obj->getMax() - lb;
    for (int n = 0; n < nbNodes(); n++) {

        int e1 = e1s[n], e2 = e2s[n];

        assert(e1 != -1 && e2 != -1);
        //assert(!(getEdgeVar(e1).isFixed() && getEdgeVar(e1).isFalse()));
        //assert(!(getEdgeVar(e2).isFixed() && getEdgeVar(e2).isFalse()));
        if (getEdgeVar(e2).isFixed() && getEdgeVar(e2).isTrue() && 
            getEdgeVar(e1).isFixed() && getEdgeVar(e1).isTrue()) {
            continue;
        }
        int a = 0;

        vec<Lit> psf; psf.push(); 
        vector<int> to_remove;

        for (unsigned int i = 0; i < adj[n].size(); i++) {
            int e = adj[n][i];
            int u = getEndnode(e,0), v = getEndnode(e,1);
            if (getEdgeVar(e).isFixed()) {
                if (getEdgeVar(e).isFalse()) psf.push(getEdgeVar(e).getValLit());
                continue;
            }
            a++;
            if (e == e1 || e == e2) continue;
                    
            if ((2*original_ws[e] - replacement[u] - replacement[v])/2 > delta) { 
                //Remove e
                getEdgeVar(e).setVal(false,r);
                //cout<<"PRUNNING4 R "<< getEndnode(e,0)<<" "<<getEndnode(e,1)<<endl;
                to_remove.push_back(e);
                //on_edge_removal(e);
                //i--; //The adj[n] changed order and need to recheck the same index
                psf.push(getEdgeVar(e).getValLit());
                a--;
            }
        }

        for (int i = 0; i < to_remove.size(); i++)
            on_edge_removal(to_remove[i]);

        

    }
    return true;
}

bool CycleCostSimple::propagate_upper_bound() {
    int sum = 0;
    vec<Lit> ps; ps.push();
    Clause* r = NULL;
    for (int n = 0; n < nbNodes(); n++) {
        int e1, e2;
        find_two_expensive(n,e1,e2,original_ws,ps);
        assert(e1 != -1 && e2 != -1);
        sum += original_ws[e1] + original_ws[e2];
    }
    sum /= 2;

    if(!obj->getMin() > sum) {
        //This can actually happen if the graph yat this point does not
        //actually contain a cycle. It can be biconnected and yet not contain a
        //cycle:
        //      /-------\
        //     A----B----C
        //    ||   ||    ||
        //    ||   ||    ||
        //    ||   ||    ||
        //    ||   ||    F---\   
        //    ||   ||     \   \
        //    ||    E======H  |
        //    ||          /   /
        //     D=========G----/ 
        // Where double lines mean mandatory and simple optional.
        // See Revision 1035, test eil101 (lazy=false) after 
        // sol 720 for an example
        //Since this very very rarelly happens, its better to just 
        // use the bicconected proapgator and not the circuit which is
        // more expensive and fail here.
        //cout<<available_to_dot()<<endl;
        //cout<<obj->getMin()<<" "<<sum<<endl;
        if (so.lazy) {
            vec<Lit> ps; fullExpl(ps); 
            Clause *expl = Clause_new(ps);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;                                
        }        
        return false;
    }

    if (obj->getMax() > sum && sum >= obj->getMin()) {
        //fullExpl(ps);
        if (so.lazy)
            r = Reason_new(ps);
        obj->setMax(sum,r);
    }
    return true;
}

void CycleCostSimple::on_edge_removal(int i) {
    last_state_e[i] = OUT;
    for (int j = 0; j < 2; j++) {
        int u = getEndnode(i,j);
        int pos = adj_map[u][i];
        int last = adj[u][neigh_sizes[u] - 1];
        adj[u][pos] = last; //the last edge goes wherever 'i' was
        adj_map[u][last] = pos;
        adj[u][neigh_sizes[u] - 1] = i; //removed edge goes at the back
        adj_map[u][i] = neigh_sizes[u] - 1;
        neigh_sizes[u]--;
    }

}

void CycleCostSimple::wakeup(int i, int c) {
    repair_backtrack();

    if (i == -1) {
        pushInQueue();
    } else if (i >= 0 && i < nbEdges()){        
        if (getEdgeVar(i).isTrue() && last_state_e[i] != IN) {
            add_inedge(i);
            pushInQueue();
        } else if (getEdgeVar(i).isFalse() && last_state_e[i] != OUT) {
            on_edge_removal(i);
            pushInQueue();
        }
    }
}

bool CycleCostSimple::propagate() {
    repair_backtrack();
    //string deb ="";
    //for (int i = 0; i < in_edges.size(); i++)
    //    deb += "("+to_string(getEndnode(in_edges[i],0))+","+to_string(getEndnode(in_edges[i],1))+") ";
    //cout<<"================================================PROPAGATE "<<__FILE__<<" "<<deb<<endl;

    if(!propagate_upper_bound())
        return false;
    
    return filter_expensive_edges_simple();
}

void CycleCostSimple::clearPropState() {
    GraphPropagator::clearPropState();
}

bool CycleCostSimple::checkFinalSatisfied() {
    //cout<<available_to_dot()<<endl;
    return true;
}

