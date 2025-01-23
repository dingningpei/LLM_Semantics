#include "td_bounded_path.h"

#include <algorithm>
#include <queue>
#include "../support/Dijkstra.h"
#include "dtree.h"
#include "../core/engine.h"
#include "diff_logic.h"

using namespace std;

#define MAX(a,b) ((a<b)?b:a)

#include <iostream>
#define PRINTDBG(l) {}//cerr<<l <<" ("<<__FILE__<<":"<<__LINE__<<")\n";
#define PRINTDBGb(l) {}//cerr<<l<<" ";

#define GiveFailureExplanation(v)  Clause *__expl = Clause_new(v); \
                                   __expl->temp_expl = 1; \
                                   sat.rtrail.last().push(__expl); \
                                   sat.confl = __expl; \
                                   TDBoundedPath::expl_len += v.size(); \
                                   TDBoundedPath::expl_count++; 

#define ReasonNew(v)               Reason_new(v);       \
    TDBoundedPath::expl_len += v.size();                \
    TDBoundedPath::expl_count++;                 



int dicho_function(vector<vector<int> >& v, int t) {
    int lo = 0;
    int hi = v.size() - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2;
        if (v[mid][0] == t) {
            return v[mid][1];
        }
        if (v[lo][0] == t) {
            return v[lo][1];
        }
        if (v[hi][0] == t) {
            return v[hi][1];
        }
            
        if (v[mid][0] < t && v[mid + 1][0] > t) {
            int sign = v[mid][1] < v[mid + 1][1] ? 1 : (v[mid][1] == v[mid + 1][1] ? 0 :-1);
            return v[mid][1] + sign * (t - v[mid][0]);                
        }
        if (v[mid][0] > t) hi = mid - 1; 
        if (v[mid][0] < t) lo = mid + 1; 
    }
    assert(false);
    return -1;
}

void summarize_function(vector<vector<int> >& from, 
                        vector<vector<vector<int> > >& to) {
    to = vector<vector<vector<int> > >(from.size(),vector< vector<int> >());
    for (uint i = 0; i < from.size(); i++) {
        uint xs = 0;
        while (xs < from[i].size()) {
            uint vs = from[i][xs];
            uint xe = xs + 1;
            uint ve = from[i][xe];
            uint delta = ve - vs;
            uint start = xs;
            while (ve - vs == delta) {
                xs = xe;                
                vs = from[i][xs];
                xe += 1;
                if (xe >= from[i].size()) break;
                ve = from[i][xe];
            }
            to[i].push_back(vector<int>());
            to[i].back().push_back(start);
            to[i].back().push_back(from[i][start]);
            to[i].push_back(vector<int>());
            to[i].back().push_back(xe - 1);
            to[i].back().push_back(from[i][xe - 1]);
            xs = xe;
        }
    }    
}


int TDBoundedPath::expl_count = 0;
int TDBoundedPath::expl_len = 0;
int TDBoundedPath::props = 0;

TDBoundedPath::TDBoundedPath(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                             vec<BoolView>& _order, vec<BoolView>& _order_opt,
                             vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                             vec< vec<int> >& _en, vec< vec<int> >& ws, 
                             vec<int> ds, IntVar* _w) 
    : GraphPropagator(_vs,_es,_en), 
      source(_s), dest(_d), before(_order), local_before(_order_opt),
      w(_w), all_constant(false), reachable(NULL),
      sort_arrivals(this), sort_latests(this) {

    priority = 5;

    PRINTDBG("Constructor");

    adj = vector<vector<int> >(nbNodes(), vector<int>());
    for (int i = 0; i < _in.size(); i++) 
        for (int j = 0; j < _in[i].size(); j++) 
            adj[i].push_back(_in[i][j]);
    for (int i = 0; i < _out.size(); i++) 
        for (int j = 0; j < _out[i].size(); j++) 
            adj[i].push_back(_out[i][j]);

    incident = vector<vector<int> >();
    for (int i = 0; i < _in.size(); i++) {
        incident.push_back(vector<int>());
        for (int j = 0; j < _in[i].size(); j++) {
            incident[i].push_back(_in[i][j]);
        }
    }

    outgoing = vector<vector<int> >();
    for (int i = 0; i < _out.size(); i++) {
        outgoing.push_back(vector<int>());
        for (int j = 0; j < _out[i].size(); j++) {
            outgoing[i].push_back(_out[i][j]);
        }
    }

    nodes2edge = vvi_t(nbNodes(),std::vector<int>(nbNodes(), -1));
    for (int e = 0; e < nbEdges(); e++)
        nodes2edge[getTail(e)][getHead(e)] = e;

    is_negative = vector<bool>(nbEdges(), false);
    is_constant = vector<bool>(nbEdges(), true);
    int const_count = 0;
    time_weight = vector<vector<int> >();
    for (int i = 0; i < ws.size(); i++) {
        time_weight.push_back(vector<int>());
        for (int j = 0; j < ws[i].size(); j++) {
            time_weight[i].push_back(ws[i][j]);
            if (ws[i][j] < 0) {
                if (getEdgeVar(i).setValNotR(false)) 
                    getEdgeVar(i).setVal(false);
                is_negative[i] = true;
            } else if (ws[i][j] != ws[i][0]) {
                is_constant[i] = false;
            }            
        }
        if (is_constant[i])                 
            const_count++;
    }
    all_constant = (const_count == ws.size());
    //summarize_function(time_weight,abrv_time_weight);


    task_time = vector<int>();
    for (int i = 0; i < ds.size(); i++) {
        task_time.push_back(ds[i]);
    }


    vvi_t arrivalTime = vvi_t(ws.size(), vector<int>(ws[0].size(), -1));
    for (int i = 0; i < ws.size(); i++) {
        for (int j = 0; j < ws[i].size(); j++) {
            arrivalTime[i][j] = ws[i][j] + j;
        }
    }

    latest_time = vector<vector<int> >(ws.size());
    for (uint i = 0; i < latest_time.size(); i++) {
        latest_time[i] = vector<int>(arrivalTime[i][arrivalTime[i].size()-1]+1, -1);
        for (uint x = 0; x < arrivalTime[i].size(); x++) {
            int v = arrivalTime[i][x];
            int v2 = latest_time[i].size();
            if (x < arrivalTime[i].size() - 1){ 
                v2 = arrivalTime[i][x+1];
            }
            if (v < 0) v = 0;
            if (v2 < 0) v2 = 0;
            for (int k = v; k < v2; k++) {
                latest_time[i][k] = MAX(latest_time[i][k], (int)x);
            }   
        }
    }
    //summarize_function(latest_time,abrv_latest_time);


    last_state_e = new Tint[nbEdges()];
    memset(last_state_e,UNK,sizeof(Tint)*nbEdges());
    last_state_n = new Tint[nbNodes()];
    memset(last_state_n,UNK,sizeof(Tint)*nbNodes());

    was_in_earliest = new Tint[nbEdges()];
    memset(was_in_earliest,0,sizeof(Tint)*nbEdges());


    for (int i = 0; i < nbEdges(); i++) {
        if (isSelfLoop(i) && getEdgeVar(i).setValNotR(false)) {
            getEdgeVar(i).setVal(false);
        } else {
            getEdgeVar(i).attach(this, i,EVENT_LU);
        }
    }

    for (int i = 0; i < nbNodes(); i++) {
        getNodeVar(i).attach(this, i + nbEdges(),EVENT_LU);
    }

    w->attach(this, -1, EVENT_LU);

    
    


    explanation_tsize = 2;
    fail_expl.push_back(Lit()); //Room for the node causing failure
    fail_expl.push_back(Lit()); //Room for w->getValLit();
    prop_expl.push_back(Lit()); //Empty first cell
    prop_expl.push_back(Lit()); //Room for w->getValLit();

    in_nodes_tsize = 0;


    earliest_ready_dp = new FilteredDijkstraMandatory(this, source, dest, 
                                                      endnodes, incident, outgoing, 
                                                      time_weight, task_time);
    earliest_ready_dp->init();

    //For density of graph
    available_edges = nbEdges();


    //For predecesors: (Tint is big enough for this small graphs..)
    preds = new Tint[nbNodes()];
    for (int i = 0; i < nbNodes(); i++)
        preds[i] = 0;
    if (before.size()) { 
        for (int i = 0; i < nbNodes(); i++)
            for (int j = 0; j < nbNodes(); j++)
                if (i != j) {
                    getUBeforeV(i,j).attach(this,nbNodes() + nbEdges() + i*nbNodes()+j,EVENT_LU);
                } else if (getUBeforeV(i,j).setValNotR(false)) {
                    getUBeforeV(i,j).setVal(false,NULL);
                    if (getUBeforeVPossible(i,j).setValNotR(false))
                        getUBeforeVPossible(i,j).setVal(false,NULL);
                }
    }    

    fixed_outgoing = new Tint[nbNodes()];
    for (int i = 0; i < nbNodes(); i++)
        fixed_outgoing[i] = -1;
    fixed_incident = new Tint[nbNodes()];
    for (int i = 0; i < nbNodes(); i++)
        fixed_incident[i] = -1;


    vector<int> far;
    int furthest_node = source;
    find_earliest_ready(far,furthest_node);
    if (w->getMin() < earliest_ready[dest])
        w->setMin(earliest_ready[dest],NULL);


    return;
    bool ok = false;
    int lb = earliest_ready_dp->run(&ok);

    if (w->getMin() < lb) {
        w->setMin(lb,NULL);
    }   

}

TDBoundedPath::~TDBoundedPath() {
    delete[] last_state_e;
    delete[] last_state_n;
    delete[] was_in_earliest;
}

void TDBoundedPath::wakeup(int i, int c) {
    priority = 5;
    update_explanation();
    update_innodes();

    if (i == -1) {
        pushInQueue();
    } else if (i < nbEdges()) {
        if (isForbiddenE(i) && last_state_e[i] != OUT) {
            if (was_in_earliest[i]) {
                PRINTDBG("Adding to Explanation "<<i<<" "<<stateE(i));
                assert(fail_expl.size() == prop_expl.size());
                assert(fail_expl.size() >= 2);
                fail_expl.push_back(getEdgeVar(i).getValLit());
                prop_expl.push_back(getEdgeVar(i).getValLit());
                explanation_tsize += 1;
                pushInQueue();
            }
            available_edges -= 1;
        } else if (isMandatoryE(i)) {
            fixed_edges.insert(i);
            fixed_incident[getHead(i)] = i;
            fixed_outgoing[getTail(i)] = i;
        }
    } else if (i < nbEdges() + nbNodes()) {
        i = i - nbEdges();
        if (isMandatoryN(i) && last_state_n[i] != IN) {
            in_nodes_list.push_back(i);
            in_nodes_tsize += 1;
            //pushInQueue();
        }
    } else if (before.size() && i < nbNodes() + nbEdges() + before.size()){
        i = i - nbNodes() - nbEdges();
        int u = i/nbNodes();
        int v = i % nbNodes();
        //u is before v. before[u,v]
        if(getUBeforeV(u,v).isTrue()) {
            //makeUBeforeV(u,v);
            u_before_v.push_back(make_pair(u,v));
        }
    }

}

bool TDBoundedPath::makeLocallyUBeforeV(int u, int v, vec<Lit> expl) {
    //Preds only set when nodes are mandatory.
    if (getUBeforeVPossible(u,v).isFixed() && getUBeforeVPossible(u,v).isTrue()) {
        //preds[v] = preds[v] | (1 << u);
    } else if (!getUBeforeVPossible(u,v).isFixed()){
        Clause* r = NULL;
        if (so.lazy) {
            r = Reason_new(expl);
        }
        getUBeforeVPossible(u,v).setVal(true,r);
        //preds[v] = preds[v] | (1 << u);
    } else {
        if (so.lazy) {
            if (expl.size() == 0){
                expl = vec<Lit>();
                expl.push();
            }
            expl[0] = getUBeforeVPossible(u,v).getValLit();
            GiveFailureExplanation(expl);
        }
        return false;
    }

    if (!getUBeforeVPossible(v,u).isFixed()) {
        Clause* r = NULL;
        if (so.lazy) {
            vector<Lit>ps; ps.push_back(Lit());
            ps.push_back(getUBeforeVPossible(u,v).getValLit());
            r = Reason_new(ps);
        }
        getUBeforeVPossible(v,u).setVal(false,r);
    } else if (getUBeforeV(v,u).isTrue()) {
        if (so.lazy) {
            vector<Lit>ps; 
            ps.push_back(getUBeforeVPossible(u,v).getValLit());
            ps.push_back(getUBeforeVPossible(v,u).getValLit());
            Clause *__expl = Clause_new(ps);
            __expl->temp_expl = 1;
            sat.rtrail.last().push(__expl);
            sat.confl = __expl;
        }
        return false;
    }

    if (nodes2edge[v][u] >= 0) {
        if (!isFixedE(nodes2edge[v][u])) {
            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit>ps; ps.push_back(Lit());
                ps.push_back(getUBeforeVPossible(v,u).getValLit());
                r = Reason_new(ps);
            }
            getEdgeVar(nodes2edge[v][u]).setVal(false,r);
        } else if (isMandatoryE(nodes2edge[v][u])) {
            if (so.lazy) {
                vector<Lit>ps; 
                ps.push_back(getUBeforeVPossible(v,u).getValLit());
                ps.push_back(getEdgeVar(nodes2edge[v][u]).getValLit());
                Clause *__expl = Clause_new(ps);
                __expl->temp_expl = 1;
                sat.rtrail.last().push(__expl);
                sat.confl = __expl;
            }
            return false;
        }
    }

    return true;
}

bool TDBoundedPath::makeUBeforeV(int u, int v, vec<Lit> expl) {
    if (!makeLocallyUBeforeV(u,v))
        return false;
    for (int x = 0; x < nbNodes(); x++) {
        if (getUBeforeVPossible(x,u).isFixed() && getUBeforeVPossible(x,u).isTrue()) {
            vec<Lit> ps;
            if (so.lazy) {
                ps.push();
                ps.push(getUBeforeVPossible(x,u).getValLit());
                ps.push(getUBeforeVPossible(u,v).getValLit());
            }
            if(!makeLocallyUBeforeV(x,v,ps))
                return false;
        }
    }

    if (!isMandatoryN(u) || !isMandatoryN(v))
        return true;

    if (getUBeforeV(u,v).isFixed() && getUBeforeV(u,v).isTrue()) {
        preds[v] = preds[v] | (1 << u);
    } else if (!getUBeforeV(u,v).isFixed()){
        Clause* r = NULL;
        if (so.lazy) {
            r = Reason_new(expl);
        }
        getUBeforeV(u,v).setVal(true,r);
        preds[v] = preds[v] | (1 << u);
    } else {
        if (so.lazy) {
            if (expl.size() == 0){
                expl = vec<Lit>();
                expl.push();
            }
            expl[0] = getUBeforeV(u,v).getValLit();
            GiveFailureExplanation(expl);
        }
        return false;
    }

    if (!getUBeforeV(v,u).isFixed()) {
        Clause* r = NULL;
        if (so.lazy) {
            vector<Lit>ps; ps.push_back(Lit());
            ps.push_back(getUBeforeV(u,v).getValLit());
            r = Reason_new(ps);
        }
        getUBeforeV(v,u).setVal(false,r);
    } else if (getUBeforeV(v,u).isTrue()) {
        if (so.lazy) {
            vector<Lit>ps; 
            ps.push_back(getUBeforeV(u,v).getValLit());
            ps.push_back(getUBeforeV(v,u).getValLit());
            Clause *__expl = Clause_new(ps);
            __expl->temp_expl = 1;
            sat.rtrail.last().push(__expl);
            sat.confl = __expl;
        }
        return false;
    }

    for (int x = 0; x < nbNodes(); x++) {
        if (getUBeforeV(x,u).isFixed() &&getUBeforeV(x,u).isTrue()) {
            vec<Lit> ps;
            if (so.lazy) {
                ps.push();
                ps.push(getUBeforeVPossible(x,u).getValLit());
                ps.push(getUBeforeVPossible(u,v).getValLit());
            }
            if(!makeUBeforeV(x,v,ps))
                return false;
        }
    }

    /*if (nodes2edge[v][u])) {
      if (!isFixedE(nodes2edge[v][u])) {
        Clause* r = NULL;
        if (so.lazy) {
            vector<Lit>ps; ps.push_back(Lit());
            ps.push_back(getUBeforeV(v,u).getValLit());
            r = Reason_new(ps);
        }
        getEdgeVar(nodes2edge[v][u]).setVal(false,r);
    } else if (isMandatoryE(nodes2edge[v][u])) {
        if (so.lazy) {
            vector<Lit>ps; 
            ps.push_back(getUBeforeV(v,u).getValLit());
            ps.push_back(getEdgeVar(nodes2edge[v][u]).getValLit());
            Clause *__expl = Clause_new(ps);
            __expl->temp_expl = 1;
            sat.rtrail.last().push(__expl);
            sat.confl = __expl;
        }
        return false;
        }
    }*/
    return true;

}

void TDBoundedPath::find_earliest_ready(std::vector<int>& too_late, int& furthest_node) {
    std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                        Dijkstra::Priority> q 
        = std::priority_queue<Dijkstra::tuple, 
                              std::vector<Dijkstra::tuple>, 
                              Dijkstra::Priority>();

    vector<bool> vis = vector<bool>(nbNodes(), false);

    int count = 0;
    vector<int> pred = vector<int>(nbNodes(), -1);
    vector<int>& cost = earliest_ready;
    cost = vector<int>(nbNodes(), -1);    

    pred[source] = source;
    cost[source] = duration(source);
    Dijkstra::tuple initial(source,cost[source]);

    q.push(initial);

    furthest_node = source;

    while (!q.empty() && count < nbNodes()) {

        Dijkstra::tuple top = q.top(); q.pop();
        int curr = top.node;


        if (vis[curr]) continue;
        vis[curr] = true;

        if (top.cost > w->getMax()) {
            too_late.push_back(curr);
        } else if (top.cost > cost[furthest_node] && isMandatoryN(curr)) {
            furthest_node = curr;
        }

        count++;

        for (uint i = 0 ; i < outgoing[curr].size(); i++) {
            int e = outgoing[curr][i];
            if (isForbiddenE(e) || isNegativeE(e)) {
                continue;
            }
            int other = getHead(e); //Head of e

            if (isForbiddenN(other)) {
                continue;            
            }    
            
            int ready = cost[curr] + weight(e,cost[curr]) + duration(other);

            if (ready < w->getMax()) {
                //was_in_earliest[nodes2edge[curr][other]] = 1;
            }

            if(vis[other])
                continue;

            if (cost[other] == -1 
                || cost[other] > ready) {
                assert(ready >= 0);
                cost[other] = ready;
                pred[other] = curr;

                q.push(Dijkstra::tuple(other, cost[other]));
            }             
        }
    }

}

void TDBoundedPath::find_latest_arrivals(vector<int>& too_slow) {

    class Priority {
    public:
        bool operator() (const Dijkstra::tuple& lhs, const Dijkstra::tuple&rhs) const {
            return lhs.cost < rhs.cost;
        }
    };

    std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                        Priority> q 
        = std::priority_queue<Dijkstra::tuple, 
                              std::vector<Dijkstra::tuple>, Priority>();

    

    vector<bool> vis = vector<bool>(nbNodes(), false);

    int count = 0;
    vector<int> pred = vector<int>(nbNodes(), -1);
    vector<int>& latest = latest_arrivals;
    latest = vector<int>(nbNodes(), -1);    

    pred[dest] = dest;
    latest[dest] = w->getMax() - task_time[dest];
    assert(latest[dest] >= 0);
    Dijkstra::tuple initial(dest,latest[dest]);

    q.push(initial);

    while (!q.empty() && count < nbNodes()) {

        Dijkstra::tuple top = q.top(); q.pop();
        int curr = top.node;

        assert(latest[curr] >= 0);

        if (vis[curr]) continue;
        vis[curr] = true;

        count++;

        for (uint i = 0 ; i < incident[curr].size(); i++) {
            int e = incident[curr][i];
            if (isForbiddenE(e) || isNegativeE(e)) { 
                continue;
            }
            int other = getTail(e); //Tail of e

            if (isForbiddenN(other) || vis[other]) {
                continue;            
            }    
            
            int arrive_other = depart_to_arrive(e,latest[curr]) - duration(other);

            if (earliest_ready[other] + weight(e,earliest_ready[other]) > latest[curr]) {
                //I can't use this edge, otherwise I need to depart other 
                //before 0 to be at curr in time. Remove it
                too_slow.push_back(e);
            } 
            if (arrive_other >= 0 &&
                (latest[other] == -1 || latest[other] < arrive_other)) {

                assert(arrive_other >= 0);
                latest[other] = arrive_other;
                pred[other] = curr;

               
                q.push(Dijkstra::tuple(other, latest[other]));
            }             
        }
    }

}

std::vector<Lit> TDBoundedPath::explain_naive(bool fail) {
    vector<Lit> ps;
    if (!fail) ps.push_back(Lit());
    ps.push_back(w->getMaxLit());
    fullExpl(ps);
    for (int i = 0; i < before.size(); i++) {
        if (before[i].isFixed()) {
            ps.push_back(before[i].getValLit());
        }
        if (local_before[i].isFixed()) {
            ps.push_back(local_before[i].getValLit());
        }
    }
    assert(ps.size() >= fail_expl.size());
    return ps;
}

void TDBoundedPath::explain_basic(int n, vector<Lit>& ps) {
    if (n >= 0 && isMandatoryN(n)) {
        fail_expl[0] = getNodeVar(n).getValLit();
        fail_expl[1] = w->getMaxLit();
        ps = fail_expl;
        return ;
    } else {
        if (n == -1) 
            prop_expl[1] = getNodeVar(source).getValLit(); //Dummy
        else 
            prop_expl[1] = w->getMaxLit();
        ps = prop_expl;
        return;
    }
}

vector<Lit> TDBoundedPath::explain_basic(int n) {
    if (n >= 0 && isMandatoryN(n)) {
        fail_expl[0] = getNodeVar(n).getValLit();
        fail_expl[1] = w->getMaxLit();
        return fail_expl;
    } else {
        if (n == -1) 
            prop_expl[1] = getNodeVar(source).getValLit(); //Dummy
        else 
            prop_expl[1] = w->getMaxLit();
        return prop_expl;
    }
}

int TDBoundedPath::explain_n_too_far(int n, int limit, vector<Lit>& lits, int ignore) {
    //lits = explain_basic(n);
    //return;
    //explain_basic(n,lits);
    //return;

    class Priority {
    public:
        bool operator() (const Dijkstra::tuple& lhs, const Dijkstra::tuple&rhs) const {
            return lhs.cost < rhs.cost;
        }
    };

    std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                        Priority> q 
        = std::priority_queue<Dijkstra::tuple, 
                              std::vector<Dijkstra::tuple>, Priority>();

    

    vector<bool> vis = vector<bool>(nbNodes(), false);

    int count = 0;
    vector<int> pred = vector<int>(nbNodes(), -1);
    vector<int> latest = vector<int>(nbNodes(), -1);    

    pred[n] = n;
    latest[n] = limit;
    assert(limit >= 0);
    Dijkstra::tuple initial(n,latest[n]);

    q.push(initial);

    while (!q.empty() && count < nbNodes()) {

        Dijkstra::tuple top = q.top(); q.pop();
        int curr = top.node;

        assert(latest[curr] >= 0);

        if (vis[curr]) continue;
        vis[curr] = true;

        count++;

        for (uint i = 0 ; i < incident[curr].size(); i++) {
            int e = incident[curr][i];
            if (isNegativeE(e) || 
                isSelfLoop(e)  ||
                getHead(e) == source ||
                getTail(e) == dest) continue;
            int other = getTail(e); //Tail of e

            if (vis[other]) {
                continue;            
            }    
            
            int arrive_other = depart_to_arrive(e,latest[curr]) - duration(other);

            if (isForbiddenE(e)) {

                if (latest[other] == -1 && 
                    (/*arrive_other < 0 ||*/ //NOT FULLY CONVINCED ABOUT THIS...
                     arrive_other >= earliest_ready[other] - duration(other))) {
                    lits.push_back(getEdgeVar(e).getValLit());
                    continue;
                }
            }

            if (arrive_other >= 0 &&
                (latest[other] == -1 || latest[other] < arrive_other)) {
                assert(arrive_other >= 0);
                latest[other] = arrive_other;
                pred[other] = curr;
                if (other != ignore)
                    q.push(Dijkstra::tuple(other, latest[other]));
            }             
        }
    }
    return latest[source];
}

int TDBoundedPath::explain_n_too_early(int n, int start, vector<Lit>& lits, int ignore) {
    //lits = explain_basic(n);
    //return;
    //explain_basic(n,lits);
    //return;

    //vector<int> edges;

    std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                        Dijkstra::Priority> q 
        = std::priority_queue<Dijkstra::tuple, 
                              std::vector<Dijkstra::tuple>, 
                              Dijkstra::Priority>();

    vector<bool> vis = vector<bool>(nbNodes(), false);

    int count = 0;
    vector<int> pred = vector<int>(nbNodes(), -1);
    vector<int> cost = vector<int>(nbNodes(), -1);    

    pred[n] = n;
    cost[n] = 0;//start + duration(n);
    Dijkstra::tuple initial(n,start + duration(n)/*cost[n]*/);

    q.push(initial);


    while (!q.empty() && count < nbNodes()) {

        Dijkstra::tuple top = q.top(); q.pop();
        int curr = top.node;


        if (vis[curr]) continue;
        vis[curr] = true;

        count++;

        for (uint i = 0 ; i < outgoing[curr].size(); i++) {
            int e = outgoing[curr][i];
            if (isNegativeE(e) || 
                isSelfLoop(e)  ||
                getHead(e) == source ||
                getTail(e) == dest) continue;
            int other = getHead(e); //Head of e
            if(vis[other])
                continue;

            int ready = cost[curr] + weight(e,cost[curr]) + duration(other);
            assert(ready >= 0);
            if (isForbiddenE(e)) {

                //If I need to be at the head of e at time a_hd
                //and this edge would allow me to do so,
                //this edge explains why I have one less way of
                //getting to dest in time.

                if (//latest_arrivals[other] < 0 || //NOT FULLY CONVINCED...
                    ready - duration(other) <= latest_arrivals[other]) {
                    lits.push_back(getEdgeVar(e).getValLit());
                    //edges.push_back(e);
                    continue;
                }
            }

            if (cost[other] == -1 
                || cost[other] > ready) {
                assert(ready >= 0);
                cost[other] = ready;
                pred[other] = curr;

                if (other != ignore)
                    q.push(Dijkstra::tuple(other, cost[other]));
            }             
        }
    }

    return cost[dest];
}

void TDBoundedPath::update_explanation() {
    if (explanation_tsize < (int)fail_expl.size()) {
        fail_expl.resize(explanation_tsize);
        prop_expl.resize(explanation_tsize); 
    }
}

void TDBoundedPath::update_innodes() {
    if (in_nodes_tsize < (int)in_nodes_list.size()) {
        in_nodes_list.resize(in_nodes_tsize);
    }
}

bool TDBoundedPath::propagate() {
    PRINTDBG("Propagate");

    TDBoundedPath::props++;

    update_explanation();

    for (unsigned int i = 0; i < u_before_v.size(); i++) {
        //before[u,v] is already set, not need to explain.
        //the call to makeUbeforeV will just do the propagation
        //assuming that u is indeed before v.
        if (!makeUBeforeV(u_before_v[i].first,u_before_v[i].second))
            return false;
    }


    vector<int> far;
    int furthest_node = source;
    find_earliest_ready(far,furthest_node);
    vector<int> too_slow;
    find_latest_arrivals(too_slow);

    int lb = earliest_ready[dest];
    
    if (w->getMax() < lb) {
        if (so.lazy) {
            vector<Lit> ps; 
            ps.push_back(w->getMaxLit());
            explain_n_too_early(source, 0, ps);

            //Same as above. Seem to behave equally:
            //explain_n_too_far(dest, w->getMax(), ps);
            
            //ps = explain_naive(true);
            GiveFailureExplanation(ps);
        }
        return false;
    }



    for (uint i = 0; i < far.size(); i++) {
        int n = far[i];
        if (isMandatoryN(n)) {
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(w->getMaxLit());
                explain_n_too_far(n, w->getMax(), ps);
                //ps = explain_naive(true);
                GiveFailureExplanation(ps);
            }
            return false;
        } else {
            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(Lit());
                explain_n_too_far(n, w->getMax(), ps);
                //ps = explain_naive(false);
                r = ReasonNew(ps);
            }
            getNodeVar(n).setVal(false,r);
            last_state_n[n] = OUT;
            if (!GraphPropagator::coherence_outedges(n))
                return false;
        }
    }
    //return true;//should 21615

    for (int n = 0; n < nbNodes(); n++) {
        int arrival_n = earliest_ready[n] - duration(n);
        assert(arrival_n >= 0 || isForbiddenN(n));
        if (isForbiddenN(n)) continue;
        if (latest_arrivals[n] < 0) { 
            //You would need to be here in negative time!
            if (isMandatoryN(n)) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(w->getMaxLit());
                    ps.push_back(getNodeVar(n).getValLit());
                    explain_n_too_early(n, arrival_n, ps);
                    GiveFailureExplanation(ps);
                }
                return false;
            } else {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_early(n, arrival_n, ps);
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                getNodeVar(n).setVal(false,r);
                last_state_n[n] = OUT;
                if (!GraphPropagator::coherence_outedges(n))
                    return false;
            }
        }
    }

    //return true; //should 21600
    for (int n = 0; n < nbNodes(); n++) {
        if (isForbiddenN(n)) continue;
        //if (latest_arrivals[n] < 0)
        //    continue;
        int arrival_n = earliest_ready[n] - duration(n);
        int total = arrival_n + w->getMax() -latest_arrivals[n];
        if (total > w->getMax()) { //latest_arrivals[n] < arrival_n
            if (isMandatoryN(n)) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(w->getMaxLit());
                    ps.push_back(getNodeVar(n).getValLit());
                    int d = explain_n_too_far(n, latest_arrivals[n], ps);
                    int relaxed = latest_arrivals[n] - d;
                    explain_n_too_early(n, relaxed, ps); //arrival_n
                    //explain_n_too_early(n, arrival_n, ps);
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            } else {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    int d = explain_n_too_far(n, latest_arrivals[n], ps);
                    int relaxed = latest_arrivals[n] - d;
                    explain_n_too_early(n, relaxed, ps); //arrival_n
                    //explain_n_too_early(n, arrival_n, ps); 
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                getNodeVar(n).setVal(false,r);
                last_state_n[n] = OUT;
                if (!GraphPropagator::coherence_outedges(n))
                    return false;
            }
        }
    }
    //return true; //should 17488


    for (int n = 0; n < nbNodes(); n++) {
        if (isMandatoryN(n)) {
            if (earliest_ready[n] + w->getMax() - latest_arrivals[n] > 
                earliest_ready[furthest_node] + w->getMax() - latest_arrivals[furthest_node]) {
                furthest_node = n;
            }
        }
    }

    //Not sure why this doesnt work for variable weights (Its the explanation)
    int dist = earliest_ready[furthest_node] + all_constant*(w->getMax() - latest_arrivals[furthest_node]);

    if (w->getMin() < dist) {
        Clause* r = NULL;
        if (so.lazy) {
            vector<Lit> ps;
            ps.push_back(Lit());
            ps.push_back(w->getMaxLit());
            ps.push_back(getNodeVar(furthest_node).getValLit());
            //assert(latest_arrivals[furthest_node] >= 0);
            explain_n_too_far(furthest_node, latest_arrivals[furthest_node], ps);
            explain_n_too_early(furthest_node, 
                                earliest_ready[furthest_node] - duration(furthest_node), ps);
            //ps = explain_naive(false);
            r = ReasonNew(ps);
        }
        w->setMin(dist,r);
    }
    //return true; //should 18150


    /*for (uint i = 0; i < too_slow.size(); i++) {        
        int e = too_slow[i];
        if (isForbiddenE(e))
            continue;
        int hd = getHead(e);
        int tl = getTail(e);
        int arrival_hd = earliest_ready[hd] - duration(hd);        
        if (isMandatoryE(e)) {
            if (so.lazy) {
                vector<Lit> ps;
                ps.push_back(w->getMaxLit());
                ps.push_back(getEdgeVar(e).getValLit());
                explain_n_too_far(tl, latest_arrivals[tl], ps);
                explain_n_too_early(hd, arrival_hd, ps);
                //ps = explain_naive(true);
                GiveFailureExplanation(ps);
            }
            return false;
        } else {
            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(Lit());
                ps.push_back(w->getMaxLit());
                explain_n_too_far(tl, latest_arrivals[tl], ps);
                explain_n_too_early(hd, arrival_hd, ps);
                //ps = explain_naive(false);
                r = ReasonNew(ps);
            }
            getEdgeVar(e).setVal(false,r);
        }
    }*/


    
    for (int e = 0; e < nbEdges(); e++) {
        if (isSelfLoop(e) || isForbiddenE(e))
            continue;
        
        int hd = getHead(e);
        int tl = getTail(e);

        int s_to_tl = earliest_ready[tl];
        int arrival_hd = earliest_ready[hd] - duration(hd);        

        if (s_to_tl + weight(e,s_to_tl) > latest_arrivals[hd]) {
            // Cannot get from s to d in time through e.
            if (!getEdgeVar(e).isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_far(tl, latest_arrivals[tl], ps);
                    explain_n_too_early(hd, arrival_hd, ps);
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                getEdgeVar(e).setVal(false,r);
                last_state_e[e] = OUT;
            } else if (getEdgeVar(e).isTrue()) {
                if (so.lazy) {
                    vector<Lit> ps;
                    ps.push_back(w->getMaxLit());
                    ps.push_back(getEdgeVar(e).getValLit());
                    explain_n_too_far(tl, latest_arrivals[tl], ps);
                    explain_n_too_early(hd, arrival_hd, ps);
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            }
        } else {
            was_in_earliest[e] |= 1;
        }
    }
    



    //return true; //NODP
    //*
    float density = (float)available_edges/(nbNodes()*(nbNodes()-1));
    if (true ||density < 0.6) {

        bool ok = true;
        //double st = wallClockTime();
        lb = earliest_ready_dp->run(&ok);
        //cout<< wallClockTime() - st<<" "<<lb<<endl;

        if (!ok) {
            if (so.lazy) {
                vector<Lit> ps;// = explain_naive(dest);
                fail_expl[0] = getNodeVar(dest).getValLit();
                fail_expl[1] = w->getMaxLit();
                ps.insert(ps.end(), fail_expl.begin(), fail_expl.end());
                ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                GiveFailureExplanation(ps);
            }
            return false;
        }
        
        if (w->getMax() < lb) {
            if (so.lazy) {
                vector<Lit> ps;// = explain_naive(dest);
                //ps.push_back(w->getMaxLit());
                //explain_dest_dp(ps);
                //GiveFailureExplanation(ps);
                fail_expl[0] = getNodeVar(dest).getValLit();
                fail_expl[1] = w->getMaxLit();
                ps.insert(ps.end(), fail_expl.begin(), fail_expl.end());
                ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                GiveFailureExplanation(ps);
            }
            return false;
        }

     
        if (w->getMin() < lb) {
            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps;// = explain_naive(-1);
                //ps.push_back(Lit());
                //ps.push_back(w->getMaxLit());
                //explain_dest_dp(ps);
                prop_expl[1] = w->getMaxLit();
                ps.insert(ps.end(), prop_expl.begin(), prop_expl.end());
                ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                r = ReasonNew(ps);
            }
            w->setMin(lb,r);
        }   
    }
    //*/

    
    return true;
}

void TDBoundedPath::clearPropState() {
    GraphPropagator::clearPropState();
    fixed_edges.clear();
    u_before_v.clear();
}

void TDBoundedPath::explain_dest_dp(std::vector<Lit>& lits) {

    class Priority {
    public:
        bool operator() (const DijkstraMandatory::tuple& lhs, const DijkstraMandatory::tuple&rhs) const {
            return lhs.cost < rhs.cost;
        }
    };
    typedef DijkstraMandatory::tuple tuple;
    typedef DijkstraMandatory::table_iterator table_iterator;

    
    DijkstraMandatory::table_type table = DijkstraMandatory::table_type(nbNodes(), 
                                                                        DijkstraMandatory::map_type());
    
    std::bitset<BITSET_SIZE> target = earliest_ready_dp->get_target();
    //Initialize Queue:
    std::bitset<BITSET_SIZE> pathD; pathD[dest] = 1;
    std::bitset<BITSET_SIZE> mandD; mandD[dest] = 1;
    tuple initial(dest,w->getMax(), pathD,mandD);
    table[dest][DijkstraMandatory::hash_fn(mandD)] = initial;
    std::priority_queue<tuple, std::vector<tuple>, Priority> q;

    q.push(initial);

    while (!q.empty()) {
        tuple top = q.top(); q.pop();
        int curr = top.node;

        table_iterator it = table[curr].find(DijkstraMandatory::hash_fn(top.mand));
        if ((it->second).cost > top.cost) {
            continue;
        }

        for (unsigned int i = 0 ; i < incident[curr].size(); i++) {
            int e = incident[curr][i];
            if (isNegativeE(e)) continue;
            int other = getTail(e); //Head of e
            if (other == curr)
                continue;            

            bool enqueue = true;
            bool was_mand_other = top.mand[other];
            if (target[other])
                top.mand[other] = 1;

            int arrive_other = depart_to_arrive(e,top.cost) - duration(other);

            it = table[other].find(DijkstraMandatory::hash_fn(top.mand));

            if (it != table[other].end()){ 
                if ((it->second).cost > arrive_other) {
                    enqueue = false; //Better way
                } 
            }


            if (enqueue && isForbiddenE(e)) {

                DijkstraMandatory::table_iterator it = earliest_ready_dp->table[other].begin();
                for ( ; it != earliest_ready_dp->table[other].end(); ++it) {
                    if ((top.mand | (it->second).mand) == target) { //Union
                        int d_tl = (it->second).cost; //inlcudes time spent in hd

                        if (arrive_other < 0 || arrive_other >= d_tl - duration(other)) {
                            lits.push_back(getEdgeVar(e).getValLit());
                            enqueue = false;
                        }   
                    }
                }
            }

            top.mand[other] = was_mand_other;
            if (arrive_other >= 0 && enqueue) {
                tuple copy = top;
                if (target[other]) { //Other is mandatory
                    copy.mand[other] = 1;
                }
                copy.cost = arrive_other;
                copy.path[other] = 1;
                copy.node = other;

                table[other][DijkstraMandatory::hash_fn(copy.mand)] = copy;
                if (other != dest && other != source) {
                    q.push(copy);
                } 
            }
        }
    }

}





TDBoundedPathArrivals::TDBoundedPathArrivals(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                                             vec<BoolView>& _order, vec<BoolView>& _order_opt,
                                             vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                                             vec< vec<int> >& _en, vec< vec<int> >& _ws, vec<int> ds,
                                             IntVar* w, vec<IntVar*> _lowers, vec<IntVar*> _uppers) 
    : TDBoundedPath(_s,_d,_vs,_es,_order,_order_opt,_in,_out,_en,_ws,ds,w), 
    lowers(_lowers), uppers(_uppers) {
    priority = 5;
    if (lowers[0]->setValNotR(0)) lowers[0]->setVal(0,NULL);
    if (lowers[0]->setValNotR(0)) uppers[0]->setVal(0,NULL);


    std::vector< std::vector<int> > en;
    std::vector< std::vector<int> > in;
    std::vector< std::vector<int> > ou;
    std::vector<int> ws;

}

bool TDBoundedPathArrivals::remove_node(int n, Clause* r) {
    assert(!isMandatoryN(n));
    //cout<<"Removed "<<n<<endl;
    getNodeVar(n).setVal(false,r);
    Clause* e = NULL;
    if (so.lazy) {
        vec<Lit> ps; ps.push();
        ps.push(getNodeVar(n).getValLit());
        e = ReasonNew(ps);
    }
    if (lowers[n]->setValNotR(lowers[n]->getMax0()))
        lowers[n]->setVal(lowers[n]->getMax0(),e);
    if (uppers[n]->setValNotR(uppers[n]->getMin0()))
        uppers[n]->setVal(uppers[n]->getMin0(),e);  

    assert(lowers[n]->isFixed());
    assert(uppers[n]->isFixed());
    assert(lowers[n]->getVal() == lowers[n]->getMax0());
    assert(uppers[n]->getVal() == uppers[n]->getMin0());
    
    return !getNodeVar(n).getVal();
}


bool TDBoundedPathArrivals::propagate_arrivals() {

    std::queue<int> q = std::queue<int>(std::deque<int>(fixed_edges.begin(), fixed_edges.end()));
    while (!q.empty()) {
        int e = q.front(); q.pop();

        if(!isMandatoryE(e)) return true;

        int hd = getHead(e);
        int tl = getTail(e);
        //cout<<"Edge ("<<tl<<","<<hd<<") ";
        deque<Lit> ps;
        if (so.lazy) ps.push_back(getEdgeVar(e).getValLit());
        if (lowers[tl]->getMin() == lowers[tl]->getMax()) {
            int ctl = lowers[tl]->getMin() + duration(tl);
            int chd = ctl + weight(e,ctl);
            if (!lowers[hd]->setValNotR(chd)) continue;
            if (so.lazy) ps.push_back(lowers[tl]->getValLit());
            if (lowers[hd]->indomain(chd)) {
                Clause* r = NULL;
                ps.push_front(Lit());
                if (so.lazy) r = ReasonNew(ps);
                //cout<<">>>Setting: lowers["<<hd<<"] = "<<chd;
                lowers[hd]->setVal(chd,r);
                if(fixed_outgoing[hd] != -1)
                    q.push(fixed_outgoing[hd]);
            } else {
                if(so.lazy) ps.push_back(varNEv(lowers[hd],chd)); // != chd
                if(so.lazy) {GiveFailureExplanation(ps); }
                //cout<<">>>Setting: lowers["<<hd<<"] = "<<chd<<" FAILED ";
                return false;
            }
        } else if (uppers[hd]->getMin() == uppers[hd]->getMax()) {
            int chd = uppers[hd]->getMin();
            int ctl = depart_to_arrive(e,chd);
            if (!uppers[tl]->setValNotR(ctl)) continue;
            if (so.lazy) ps.push_back(uppers[hd]->getValLit());
            if (uppers[tl]->indomain(ctl)) {
                Clause* r = NULL;
                ps.push_front(Lit());
                if (so.lazy) r = ReasonNew(ps);
                uppers[tl]->setVal(ctl,r);
                if(fixed_incident[tl] != -1)
                    q.push(fixed_incident[tl]);
                //cout<<">>>Setting: uppers["<<tl<<"] = "<<ctl;
            } else {
                if (so.lazy) ps.push_back(varNEv(uppers[tl],ctl)); // != chd
                if (so.lazy) {GiveFailureExplanation(ps); }
                //cout<<">>>Setting: uppers["<<tl<<"] = "<<ctl<<" FAILED ";
                return false;
            }
        }
        //cout<<"."<<endl;
    } 
    return true;
}


bool TDBoundedPathArrivals::propagate() {
    for (int n = 0; n < nbNodes(); n++) {
        if (!uppers[n]->indomain(uppers[n]->getMin0()) || 
            !lowers[n]->indomain(lowers[n]->getMax0())) {
            if (isForbiddenN(n)) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(getNodeVar(n).getValLit());
                    ps.push_back(uppers[n]->getMinLit());
                    ps.push_back(lowers[n]->getMaxLit());
                    GiveFailureExplanation(ps);
                }
                return false;
            } else if (!isFixedN(n)) {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(uppers[n]->getMinLit());
                    ps.push_back(lowers[n]->getMaxLit());
                    r = ReasonNew(ps);
                }
                getNodeVar(n).setVal(true, r);
            }
        }
    }

    update_explanation();
    update_innodes();
    TDBoundedPath::props++;

    if(!propagate_arrivals())
        return false;
    
    vector<int> far;
    int furthest_node = source;
    find_earliest_ready(far,furthest_node);
    vector<int> too_slow;
    find_latest_arrivals(too_slow);
    
    vector<int> sorted_nodes(nbNodes());
    std::iota(sorted_nodes.begin(), sorted_nodes.end(), 0);
    std::sort(sorted_nodes.begin(), sorted_nodes.end(), sort_arrivals);

    for (int n = 0; n < nbNodes(); n++) {
        assert(earliest_ready[sorted_nodes[n]] >= 0 || isForbiddenN(sorted_nodes[n])); //All reachable
    }
    

    //Proapgate earlieast arrival to a node
    for (unsigned int i = 0; i < sorted_nodes.size(); i++) {
        int n = sorted_nodes[i];
        if (isForbiddenN(n))
            continue;

        int l = earliest_ready[n] - duration(n);
        
        if (l > w->getMax()) {
            if (isMandatoryN(n)) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(getNodeVar(n).getValLit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_far(n,l,ps);
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            } else {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_far(n,l,ps);
                    r = ReasonNew(ps);
                }
                remove_node(n,r);
            }
        } else if (lowers[n]->getMin() < l) {            
            if (lowers[n]->getMax() < l) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(w->getMaxLit());
                    ps.push_back(lowers[n]->getMaxLit());
                    explain_n_too_far(n,l,ps);
                    GiveFailureExplanation(ps);
                }
                return false;
            }

            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(Lit()); 
                ps.push_back(w->getMaxLit());
                explain_n_too_far(n,l,ps);
                //ps = explain_naive(false);
                r = ReasonNew(ps);
            }
            assert(l<= lowers[n]->getMax());
            lowers[n]->setMin(l,r);
        }        
    }

    //cout<<" "<<lowers[10]->getMax()<<" "<<stateN(10)<<" "<<uppers[10]->getMax()<<" "<<__LINE__<<endl;
    std::sort(sorted_nodes.begin(), sorted_nodes.end(), sort_latests);

    //Propagating latests arrivals.
    for (unsigned int i = 0; i < sorted_nodes.size(); i++) {
        int n = sorted_nodes[i];
        if (isForbiddenN(n))
            continue;

        int u = latest_arrivals[n];
        if (u < 0) {
            if (isMandatoryN(n)) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(getNodeVar(n).getValLit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_early(n,u,ps);
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            } else {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    explain_n_too_early(n,u,ps);
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                remove_node(n,r);
            }
        } else if (uppers[n]->getMax() > u){

            if (uppers[n]->getMin() > u) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    ps.push_back(w->getMaxLit());
                    ps.push_back(uppers[n]->getMinLit());
                    explain_n_too_early(n,u,ps);
                    GiveFailureExplanation(ps);
                }
                return false;
            }

            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(Lit()); 
                ps.push_back(w->getMaxLit());
                explain_n_too_early(n,u,ps);
                r = ReasonNew(ps);
            }
            uppers[n]->setMax(u,r);
        }
        
    }



    //Propagating nodes where you arrive later than you can
    for (int n = 0; n < nbNodes(); n++) {
        assert(earliest_ready[n] <= lowers[n]->getMin() + duration(n) || isForbiddenN(n));
        assert(latest_arrivals[n] >= uppers[n]->getMax() || isForbiddenN(n));
        if (isForbiddenN(n)) continue;
        int l = earliest_ready[n] - duration(n);
        int u = latest_arrivals[n];
        if (u < 0)
            continue;

        if (l > u) {
            if (isMandatoryN(n)) {
                if (so.lazy) {
                    vector<Lit> ps;
                    ps.push_back(getNodeVar(n).getValLit());
                    ps.push_back(w->getMaxLit());
                    ps.push_back(lowers[n]->getMinLit());
                    ps.push_back(uppers[n]->getMaxLit());
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            } else {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    ps.push_back(lowers[n]->getMinLit());
                    ps.push_back(uppers[n]->getMaxLit());
                    r = ReasonNew(ps);
                }
                remove_node(n,r);
            }
        }

    }



    for (int n = 0; n < nbNodes(); n++) {
        if (isMandatoryN(n)) {
            if (earliest_ready[n] + w->getMax() - latest_arrivals[n] > 
                earliest_ready[furthest_node] + w->getMax() - latest_arrivals[furthest_node]) {
                furthest_node = n;
            }
        }
    }

    //Not sure why this doesnt work for variable weights (Its the explanation)
    int dist = earliest_ready[furthest_node] + all_constant*(w->getMax() - latest_arrivals[furthest_node]);

    if (w->getMin() < dist) {
        Clause* r = NULL;
        if (so.lazy) {
            vector<Lit> ps; ps.push_back(Lit());
            ps.push_back(getNodeVar(furthest_node).getValLit());
            ps.push_back(lowers[furthest_node]->getMinLit());
            ps.push_back(uppers[furthest_node]->getMaxLit());
            r = ReasonNew(ps);
        }
        w->setMin(dist,r);
    }
    

    /*for (uint i = 0; i < too_slow.size(); i++) {
        int e = too_slow[i];
        int hd = getHead(e);
        int tl = getTail(e);
        if (isForbiddenN(hd) || isForbiddenN(tl)) continue;
        assert(earliest_ready[tl] + 
               weight(e,earliest_ready[tl])
               > latest_arrivals[hd]);

        assert(lowers[tl]->getMin() + duration(tl) + 
               weight(e,lowers[tl]->getMin() + duration(tl))
               > uppers[hd]->getMax());

        if (isMandatoryE(e)) {
            if (so.lazy) {
                vector<Lit> ps;
                ps.push_back(getEdgeVar(e).getValLit());
                ps.push_back(w->getMaxLit());
                ps.push_back(lowers[tl]->getMinLit());
                ps.push_back(uppers[hd]->getMaxLit());
                GiveFailureExplanation(ps);
            }
            return false;
        } else {
            Clause* r = NULL;
            if (so.lazy) {
                vector<Lit> ps; ps.push_back(Lit());
                ps.push_back(w->getMaxLit());
                ps.push_back(lowers[tl]->getMinLit());
                ps.push_back(uppers[hd]->getMaxLit());
                r = ReasonNew(ps);
            }
            getEdgeVar(e).setVal(false,r);
        }
        }*/

    //return true;


    for (int e = 0; e < nbEdges(); e++) {
        if (isSelfLoop(e) || isForbiddenE(e))
            continue;
        if (isSelfLoop(e) || isForbiddenE(e))
            continue;
        
        int hd = getHead(e);
        int tl = getTail(e);
        int s_to_tl = earliest_ready[tl];
      
        if (s_to_tl + weight(e,s_to_tl) > latest_arrivals[hd]) {
            // Cannot get from s to d in time through e.
            if (!getEdgeVar(e).isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.push_back(w->getMaxLit());
                    ps.push_back(lowers[tl]->getMinLit());
                    ps.push_back(uppers[hd]->getMaxLit());
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                getEdgeVar(e).setVal(false,r);
                last_state_e[e] = OUT;
            } else if (getEdgeVar(e).isTrue()) {
                if (so.lazy) {
                    vector<Lit> ps;
                    ps.push_back(getEdgeVar(e).getValLit());
                    ps.push_back(w->getMaxLit());
                    ps.push_back(lowers[tl]->getMinLit());
                    ps.push_back(uppers[hd]->getMaxLit());
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            }
        } else {
            was_in_earliest[e] |= 1;
        }
    }


    //return true;

    // int total = 0;
    // for (int i = 0; i < nbNodes(); i++) {
    //     if (isMandatoryN(i))
    //         total += duration(i);
    // }
    // vector<Lit> ps;
    // if (so.lazy) ps.push_back(w->getMaxLit());
    // for (int i = 0; i < nbNodes(); i++) {
    //     if (!isMandatoryN(i) || i == dest) continue;
    //     int l = -1;
    //     int max = MIN(uppers[i]->getMax(),time_weight[0].size() - 1);
    //     int min = MAX(0,lowers[i]->getMin());
    //     if (fixed_outgoing[i] != -1) {
    //         for (int t = min; t <= max; t++) {
    //             if (l == -1 || weight(fixed_outgoing[i],t) < l)
    //                 l = weight(fixed_outgoing[i],t);
    //         }
    //         if (so.lazy) {
    //             ps.push_back(getNodeVar(i).getValLit());
    //             ps.push_back(lowers[i]->getMinLit());
    //             ps.push_back(uppers[i]->getMaxLit());
    //             ps.push_back(getEdgeVar(fixed_outgoing[i]).getValLit());
    //         }
    //     } else {
    //         for (int j = 0; j < outgoing[i].size(); j++) {
    //             int e = outgoing[i][j];
    //             if (isForbiddenE(e)) continue;
    //             for (int t = min; t <= max; t++) {
    //                 if (l == -1 || weight(e,t) < l) {
    //                     l = weight(e,t);
    //                 }
    //             }
    //         }
    //         if (so.lazy) {
    //             ps.push_back(getNodeVar(i).getValLit());
    //             ps.push_back(lowers[i]->getMinLit());
    //             ps.push_back(uppers[i]->getMaxLit());
    //             for (int j = 0; j < outgoing[i].size(); j++) {
    //                 int e = outgoing[i][j];
    //                 for (int t = min; t <= max; t++) {
    //                     if (weight(e,t) < l)
    //                         ps.push_back(getEdgeVar(e).getValLit()); //Its forbidden!
                        
    //                 }
    //             }
    //         }        
    //     }
    //     if (l > 0)
    //         total += l;
    //     if (total > w->getMax()) {
    //         if(so.lazy) {
    //             GiveFailureExplanation(ps);
    //         }
    //         return false;
    //     } else if (total > w->getMin()){
    //         Clause* r = NULL;
    //         if(so.lazy) {
    //             vector<Lit> psv; psv.push_back(Lit());
    //             psv.insert(psv.end(),ps.begin(), ps.end());
    //             r = ReasonNew(psv);
    //         }
    //         w->setMin(total, r);
    //     }
    // }


    //return true;


    float density = (float)available_edges/(nbNodes()*(nbNodes()-1));
    if (true || density < 0.5) {

        bool FAST_EXPLANATIONS = false; 

        vector<int> depth, low, parent;
        stack<int> arts;
        if (!FAST_EXPLANATIONS) {
        
            if (reachable != NULL) {
                reachable->propagateReachability(); 
            }

            depth = low = parent = vector<int>(nbNodes(),-1);
            vector<bool> visited = vector<bool>(nbNodes(),false);
            vector<bool> is_dom = getBiCC(source, depth, low, visited, parent, arts);

            if(!propagateBefore(arts))
                return false;

            earliest_ready_dp->set_doms(is_dom);
        }

        //double st = wallClockTime();
        bool ok = true;
        int lb = earliest_ready_dp->run(&ok);
        //cout<< wallClockTime() - st<<" "<<lb<<endl;

        if (!ok) {
            if (so.lazy) {
                vector<Lit> ps; 
                fail_expl[0] = getNodeVar(dest).getValLit();
                fail_expl[1] = w->getMaxLit();
                ps.insert(ps.end(), fail_expl.begin(), fail_expl.end());
                ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                //ps = explain_naive(true);
                //cout<<"ExplLen: "<<ps.size()<<"\n";//assert(ps.size()< 100);
                GiveFailureExplanation(ps);
            }
            return false;
        }

        if (!FAST_EXPLANATIONS) {
            if(!propagateDP(arts,low)) {
              return false;
            }
        } else  {
            if (w->getMax() < lb) {
                if (so.lazy) {
                    vector<Lit> ps; 
                    fail_expl[0] = getNodeVar(dest).getValLit();
                    fail_expl[1] = w->getMaxLit();
                    ps.insert(ps.end(), fail_expl.begin(), fail_expl.end());
                    ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                    //ps = explain_naive(true);
                    GiveFailureExplanation(ps);
                }
                return false;
            }

     
            if (w->getMin() < lb) {
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps;
                    prop_expl[1] = w->getMaxLit();
                    ps.insert(ps.end(), prop_expl.begin(), prop_expl.end());
                    ps.insert(ps.end(), earliest_ready_dp->avoided.begin(), earliest_ready_dp->avoided.end());
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                assert(lb <= w->getMax());
                w->setMin(lb,r);
            }

        }
        
    }


    return true;
}


void TDBoundedPathArrivals::explain_n_too_far(int n, int limit, std::vector<Lit>& lits) {
    vector<bool> visited = vector<bool>(nbNodes(),false);
    _explain_n_too_far(n,limit,lits,visited);
}
void TDBoundedPathArrivals::_explain_n_too_far(int n, int limit, 
                                               std::vector<Lit>& lits,
                                               std::vector<bool>& visited) {
    assert(!isForbiddenN(n));

    if (lowers[n]->getMin() >= limit) {
        lits.push_back(lowers[n]->getMinLit());
        return;
    }

    for (uint i = 0; i < incident[n].size(); i++) {
        int e = incident[n][i];
        int hd = getHead(e);
        int tl = getTail(e);
        if (hd == tl) continue;

        if (isForbiddenN(tl)) {
            lits.push_back(getNodeVar(tl).getValLit());
        } else if (isForbiddenE(e) && earliest_ready[tl] + weight(e,earliest_ready[tl]) < limit ) {
            lits.push_back(getEdgeVar(e).getValLit());
        } else if (!visited[tl]) {
            visited[n] = true;
            _explain_n_too_far(tl, limit - weight(e,earliest_ready[tl]), lits, visited);
        }
    }
    return;//*/

    
        

    /*visited[n] = true;
    for (uint i = 0; i < incident[n].size(); i++) {
        int e = incident[n][i];
        int hd = getHead(e);
        int tl = getTail(e);
        if (hd == tl) continue;
        int arrival_hd = earliest_ready[hd] - duration(hd);
        int arrival_tl = earliest_ready[tl] - duration(tl);
        int lit_tl_ready = lowers[tl]->getMin() + duration(tl);

        if (isForbiddenN(tl)) {
            lits.push_back(getNodeVar(tl).getValLit());
        } else if (lit_tl_ready + weight(e,lit_tl_ready) >= limit) {
            //cout << "[["<<tl<<">="<<lowers[tl]->getMin()<<"]] /\\";
            lits.push_back(lowers[tl]->getMinLit());
        } else {
            if(earliest_ready[tl] + weight(e,earliest_ready[tl]) >= limit ) {
                if (!visited[tl]) {
                    //cout<<"RECURSING [X["<<tl<<">="<<arrival_tl<<"]X] <=";
                    explain_n_too_far(tl, arrival_tl, lits);
                }
            } else {
                assert(isForbiddenE(e));
                //cout << "[[ not("<<e<<")"<<"]] /\\";
                lits.push_back(getEdgeVar(e).getValLit());
            }        
        }
        }*/

}

void TDBoundedPathArrivals::explain_n_too_early(int n, int start, std::vector<Lit>& lits) {
    vector<bool> visited = vector<bool>(nbNodes(),false);
    _explain_n_too_early(n,start,lits,visited);
}

void TDBoundedPathArrivals::_explain_n_too_early(int n, int start, 
                                               std::vector<Lit>& lits,
                                               std::vector<bool>& visited) {
    assert(!isForbiddenN(n));


    if (uppers[n]->getMax() <= start) {
        lits.push_back(uppers[n]->getMaxLit());
        return;
    }

    for (uint i = 0; i < outgoing[n].size(); i++) {
        int e = outgoing[n][i];
        int hd = getHead(e);
        int tl = getTail(e);
        if (hd == tl) continue;

        if (isForbiddenN(hd)) {
            lits.push_back(getNodeVar(hd).getValLit());
        } else if (isForbiddenE(e) && depart_to_arrive(e,latest_arrivals[hd]) >= start) {
            lits.push_back(getEdgeVar(e).getValLit());
        } else if (!visited[hd]) {
            visited[n] = true;
            _explain_n_too_early(hd, start + weight(e,start), lits,visited);
            //visited[n] = false;
        }
    }
    return;//*/


    /*visited[n] = true;
    int limit = start + duration(n);
    for (uint i = 0; i < outgoing[n].size(); i++) {
        int e = outgoing[n][i];
        int hd = getHead(e);
        int tl = getTail(e);
        if (hd == tl) continue;
        if (isForbiddenN(hd)) {
            lits.push_back(getNodeVar(hd).getValLit());
        } else if (depart_to_arrive(e,uppers[hd]->getMax()) <= limit) {
            //cout << "[["<<tl<<">="<<uppers[hd]->getMax()<<"]] /\\";
            lits.push_back(uppers[hd]->getMaxLit());
        } else {
            if(depart_to_arrive(e,latest_arrivals[hd]) <= limit) {
                if (!visited[hd]) {
                    //cout<<"RECURSING [X["<<hd<<"<="<<latest_arrivals[hd]<<"]X] <=";
                    explain_n_too_early(hd, latest_arrivals[hd], lits);
                }
            } else {
                assert(isForbiddenE(e));
                //cout << "[[ not("<<e<<")"<<"]] /\\";
                lits.push_back(getEdgeVar(e).getValLit());
            }        
        }
        }*/

}


void TDBoundedPathArrivals::explain_dp(int start, int time, int avoid, 
                                       std::bitset<BITSET_SIZE> target, 
                                       std::unordered_set<Lit>& lits) {


    class Priority {
    public:
        bool operator() (const DijkstraMandatory::tuple& lhs, const DijkstraMandatory::tuple&rhs) const {
            return lhs.cost > rhs.cost;
        }
    };
    typedef DijkstraMandatory::tuple tuple;
    typedef DijkstraMandatory::table_iterator table_iterator;

    
    DijkstraMandatory::table_type table = DijkstraMandatory::table_type(nbNodes(), 
                                                                        DijkstraMandatory::map_type());
    
    //Initialize Queue:
    std::bitset<BITSET_SIZE> pathD; pathD[start] = 1;
    std::bitset<BITSET_SIZE> mandD; mandD[start] = 1;
    tuple initial(start,0, pathD,mandD);
    table[start][DijkstraMandatory::hash_fn(mandD)] = initial;
    std::priority_queue<tuple, std::vector<tuple>, Priority> q;

    q.push(initial);
    while (!q.empty()) {
        tuple top = q.top(); q.pop();
        int curr = top.node;
       
        table_iterator it = table[curr].find(DijkstraMandatory::hash_fn(top.mand));
        if ((it->second).cost < top.cost) {
            continue;
        }

        for (unsigned int i = 0; i < incident[curr].size(); i++) {
            bool enqueue = true;
            int e = incident[curr][i];
            if (isNegativeE(e)) continue;
            int other = getTail(e); //Head of e
            if (other == curr)
                continue;            
            /*if (isForbiddenN(other)){
                lits.insert(getEdgeVar(e).getValLit());
                lits.insert(getNodeVar(other).getValLit());
                enqueue = false;
                continue;
                }*/

            assert(curr==start || 
                   (getUBeforeVPossible(curr,start).isFixed() &&
                    getUBeforeVPossible(curr,start).isTrue()) ||
                   getNodeVar(curr).isFalse());
            assert((getUBeforeVPossible(avoid,curr).isFixed() &&
                   getUBeforeVPossible(avoid,curr).isTrue()) ||
                   getNodeVar(curr).isFalse());

            bool inbetween = (getUBeforeVPossible(avoid,other).isFixed() && 
                getUBeforeVPossible(avoid,other).isTrue() &&
                getUBeforeVPossible(other,start).isFixed() && 
                getUBeforeVPossible(other,start).isTrue()) || 
                other == start || other == avoid;

            if (!inbetween && !getNodeVar(other).isFalse()) {
                //Before
                if (getUBeforeVPossible(other,avoid).isFixed() && 
                    getUBeforeVPossible(other,avoid).isTrue()) {
                    lits.insert(getUBeforeVPossible(other,avoid).getValLit());
                    enqueue = false;
                } else if (getUBeforeVPossible(start,other).isFixed() && 
                           getUBeforeVPossible(start,other).isTrue()) {
                    lits.insert(getUBeforeVPossible(start,other).getValLit());
                    enqueue = false;
                }

                /*assert(isForbiddenE(e));
                lits.insert(getEdgeVar(e).getValLit());
                lits.insert(getUBeforeVPossible(avoid,other).getValLit());
                lits.insert(getUBeforeVPossible(other,start).getValLit());
                if (isMandatoryN(other)) {
                    lits.insert(getUBeforeV(avoid,other).getValLit());
                    lits.insert(getUBeforeV(other,start).getValLit());
                }
                enqueue = false;//*/
            }


            //int arrive_other = depart_to_arrive(e,top.cost) - duration(other);
            int w_e = weight(e,top.cost) + top.cost;


            if (enqueue && isForbiddenE(e)) {

                DijkstraMandatory::table_iterator it = earliest_ready_dp->table[other].begin();
                for ( ; it != earliest_ready_dp->table[other].end(); ++it) {     
                    assert((top.mand | target) == target);
                    if (((top.mand) | (((it->second).mand)&target)) == target) { //Union
                        int d_tl = (it->second).cost; //inlcudes time spent in hd

                        /*if (table[other].count(DijkstraMandatory::hash_fn(top.mand)) > 0) {
                            if (table[other][DijkstraMandatory::hash_fn(top.mand)].cost <= w_e) {
                                enqueue = false;
                                break;
                            } 
                            }*/
                        //if (arrive_other >= d_tl - duration(other)) {
                        if (d_tl + w_e <= time) {
                            lits.insert(getEdgeVar(e).getValLit());
                            enqueue = false;
                        }   
                    }
                }
            }
            if(enqueue == false) continue;


            bool was_mand_other = top.mand[other];
            if (target[other])
                top.mand[other] = 1;

            it = table[other].find(DijkstraMandatory::hash_fn(top.mand));

            if (it != table[other].end()){ 
                if ((it->second).cost <= w_e) {
                    enqueue = false; //Better way
                } 
            }
            top.mand[other] = was_mand_other;

            if (/*arrive_other >= 0 && */enqueue) {
                tuple copy = top;
                if (target[other]) { //Other is mandatory
                    copy.mand[other] = 1;
                }
                copy.cost = w_e;
                copy.path[other] = 1;
                copy.node = other;

                table[other][DijkstraMandatory::hash_fn(copy.mand)] = copy;
                if (other != start && other != avoid) {
                    q.push(copy);
                } 
            }
        }
    }

}

bool TDBoundedPathArrivals::propagateBefore(stack<int> arts) {


    if (arts.size() < 1)
        return true;
    int n = source;

    while (n != dest) {
        int next = arts.top(); arts.pop();
        if (!getUBeforeV(n,next).isFixed()) {
            Clause* r = NULL;
            if(so.lazy) {
                vector<Lit> ps; ps.push_back(Lit());
                std::queue<int> q; q.push(source);
                vector<bool> zone = vector<bool>(nbNodes(),false); //Contains the stuff between source and next
                while (!q.empty()) {
                    int c = q.front(); q.pop();
                    zone[c] = true;
                    for (vector<int>::iterator it = outgoing[c].begin();
                         it != outgoing[c].end(); ++it) {
                        int o = getHead(*it);
                        if (isForbiddenE(*it) || isForbiddenN(o) || 
                            zone[o] || o == next) continue;
                        q.push(o);
                    }                
                }
                q.push(next);
                vector<bool> vis = vector<bool>(nbNodes(),false); 
                while (!q.empty()) {
                    int c = q.front(); q.pop();
                    vis[c] = true;
                    for (vector<int>::iterator it = outgoing[c].begin();
                         it != outgoing[c].end(); ++it) {
                        int o = getHead(*it);
                        if (vis[o] || o == next) continue;
                        if (isForbiddenE(*it) && zone[o])
                            ps.push_back(getEdgeVar(*it).getValLit());
                        q.push(o);
                    }                
                }
                r = Reason_new(ps);
            }
            getUBeforeV(n,next).setVal(true,r);
        } else  if (getUBeforeV(n,next).isFalse()) {
            return makeUBeforeV(n,next);
        }
        //cout<<"N and next"<<n<<" "<<next<<endl;
        assert(getUBeforeV(n,next).isFixed());
        assert(getUBeforeV(n,next).isTrue());
        std::queue<int> q; q.push(n); //BFS
        vector<bool> visited = vector<bool>(nbNodes(),false);

        vec<Lit> domination_explanation;
        while (!q.empty()) {
            domination_explanation.clear();
            int c = q.front(); q.pop();
            visited[c] = true;

            //cout<<" "<<c<<" "<<isFixedN(c)<<endl;
            if (so.lazy && 
                !(getUBeforeVPossible(c,next).isFixed() && getUBeforeVPossible(c,next).isTrue())){
                //All paths to c go through next in G-1
                reachable_inv->explain_dominator(c,next,domination_explanation);
            }
            if (!makeUBeforeV(c,next,domination_explanation))
                    return false;
            if (c != n) {
                if (getUBeforeV(c,n).isFixed() && getUBeforeV(c,n).isTrue()) {
                    if(!makeUBeforeV(c,n)) return false;
                    continue;
                }
                if (so.lazy && 
                    !(getUBeforeVPossible(n,c).isFixed() && getUBeforeVPossible(n,c).isTrue())){
                    //All paths to c go through n: n doms c
                    reachable->explain_dominator(c,n,domination_explanation);
                }
                if (!makeUBeforeV(n,c,domination_explanation))
                    return false;
            }

            for (vector<int>::iterator it = outgoing[c].begin();
                 it != outgoing[c].end(); ++it) {
                int o = getHead(*it);
                if (isForbiddenE(*it) || isForbiddenN(o) || 
                    visited[o] || o == next) continue;
                q.push(o);
            }                
        }
        n = next;
    }
    return true;

}

bool TDBoundedPathArrivals::propagateDP(stack<int> arts, vector<int> low) {

    //cout<<"Call "<<engine.decisionLevel()<<endl;

    int n = source;
    
    bool skip_all = false;//true;
    while (n != dest) {
        set<int> seen;
        vector<bool> seenb = vector<bool>(nbNodes(),false);
        unordered_set<Lit> expl;
        unordered_set<Lit> forbidden_edges;
        int next = arts.top(); arts.pop();

        if (skip_all)
            next = dest;

        assert(isMandatoryN(n));
        if (!isMandatoryN(next)){
            cout<<n<<" "<<next<<endl;
            cout<<available_to_dot()<<endl;
            assert(isMandatoryN(next));
        }

        assert(isMandatoryN(next));
        //cout<<"Next "<<n<<" "<<next<<endl;        
        assert(getUBeforeV(n,next).isFixed() && getUBeforeV(n,next).isTrue());


        DijkstraMandatory::table_iterator it = earliest_ready_dp->side_table[next].begin();
        int new_cost = (it->second).cost - duration(next);

        if (so.lazy) {
            std::queue<int> q; q.push(n); //BFS
            vector<bool> visited = vector<bool>(nbNodes(),false);
            while (!q.empty()) {
                int c = q.front(); q.pop();
                seen.insert(c);
                seenb[c] = 1;

                //assert(c == n || earliest_ready_dp->side_table[c].size() == 0);
                if (isFixedN(c)) {
                    assert(isMandatoryN(c));
                    assert(getUBeforeV(c,next).isFixed() && getUBeforeV(c,next).isTrue());
                    assert(c == n || (getUBeforeV(n,c).isFixed() && getUBeforeV(n,c).isTrue()));
                    expl.insert(getUBeforeV(c,next).getValLit());
                    if (n != c) expl.insert(getUBeforeV(n,c).getValLit());
                }
                visited[c] = true;
                for (vector<int>::iterator it = outgoing[c].begin();
                     it != outgoing[c].end(); ++it) {
                    int o = getHead(*it);
                    if (isForbiddenE(*it) && (skip_all || low[getHead(*it)] == low[c])) {
                        //expl.insert(getEdgeVar(*it).getValLit());
                        forbidden_edges.insert(getEdgeVar(*it).getValLit());
                    }
                    if (isForbiddenE(*it) || isForbiddenN(o) || 
                        visited[o] || o == next) continue;
                    q.push(o);
                }
            }

            std::bitset<BITSET_SIZE> prefix = (earliest_ready_dp->side_table[n].begin()->second).mand;
            std::bitset<BITSET_SIZE> all = (earliest_ready_dp->side_table[next].begin()->second).mand;
            std::bitset<BITSET_SIZE> middle = all & ~prefix; middle[n] = 1; middle[next] = 0;
            for (set<int>::iterator it = seen.begin(); it != seen.end(); ++it) {
                if (isMandatoryN(*it)) {
                    assert(getUBeforeV(*it,next).isFixed() && getUBeforeV(*it,next).isTrue());
                    assert(*it == n || (getUBeforeV(n,*it).isFixed() && getUBeforeV(n,*it).isTrue()));
                    expl.insert(getUBeforeV(*it,next).getValLit());
                    expl.insert(getUBeforeV(n,*it).getValLit());
                    if (earliest_ready_dp->get_target()[*it])
                        expl.insert(getNodeVar(*it).getValLit());
                }
            }
            for (unordered_set<pair<int,int> >::iterator it = earliest_ready_dp->avoided_r.begin();
                 it != earliest_ready_dp->avoided_r.end(); ++it) {
                if (low[it->first] == low[it->second] && low[it->second] == low[n]) {
                    assert(getUBeforeV(it->first,it->second).isFixed());
                    expl.insert(getUBeforeV(it->first,it->second).getValLit());
                }
            }           
            
            expl.insert(getUBeforeV(n,next).getValLit());
            expl.insert(lowers[n]->getMinLit());
            expl.insert(w->getMaxLit());
        }

        if(earliest_ready_dp->side_table[next].size() != 1) { 
            string dot = available_to_dot();
            for (int i = 0; i < nbNodes(); i++) {
                cerr<<i<<": ";
                for (int j = 0; j < nbNodes(); j++) {
                    if (getUBeforeV(j,i).isFixed() && getUBeforeV(j,i).isTrue())
                        cerr<<j<<" "; 
                }
                cerr <<endl;
            }
            cerr<<arts.top()<<endl;
            cout<<dot<<endl;
            
            cout<<earliest_ready_dp->table[next].size()<<endl;
            DijkstraMandatory::table_iterator it = earliest_ready_dp->table[next].begin();
            for ( ; it != earliest_ready_dp->table[next].end(); ++it) {
                cout<< ((it->second).mand) <<endl;
            }
            assert(earliest_ready_dp->table[next].size() == 1);
            exit(0);
        }


        if (lowers[next]->indomain(new_cost)) {
            if (lowers[next]->setMinNotR(new_cost)) { //SET VAL IF ALL NODES IN!
                Clause* r = NULL;
                if (so.lazy) {
                    vector<Lit> ps; ps.push_back(Lit());
                    ps.insert(ps.end(), expl.begin(), expl.end());
                    forbidden_edges.clear();
                    std::bitset<BITSET_SIZE> all = (earliest_ready_dp->side_table[next].begin()->second).mand;
                    all[n] = true;
                    all[next] = true;
                    explain_dp(next,new_cost,n,all,forbidden_edges);
                    ps.insert(ps.end(),forbidden_edges.begin(),forbidden_edges.end());
                    ps.push_back(getNodeVar(next).getValLit());
                    //ps = explain_naive(false);
                    r = ReasonNew(ps);
                }
                lowers[next]->setMin(new_cost,r); //SET VAL IF ALL NODES IN!
            }
        } else {
            if (so.lazy) {
                vector<Lit> ps;
                for (unordered_set<pair<int,int> >::iterator it = earliest_ready_dp->avoided_r.begin();
                     it != earliest_ready_dp->avoided_r.end(); ++it) {
                    if (low[it->first] == low[it->second] && low[it->second] == low[n]) {
                        assert(getUBeforeV(it->first,it->second).isFixed());
                        ps.push_back(getUBeforeV(it->first,it->second).getValLit());
                    }
                }           
                ps.push_back(getUBeforeV(n,next).getValLit());
                ps.push_back(lowers[n]->getMinLit());
                ps.push_back(uppers[next]->getMaxLit());
                ps.push_back(lowers[next]->getMinLit());
                std::bitset<BITSET_SIZE> mid = (earliest_ready_dp->side_table[next].begin()->second).mand;
                DijkstraMandatory::table_iterator it = earliest_ready_dp->table[next].begin();
                while (it != earliest_ready_dp->table[next].end()) {
                    std::bitset<BITSET_SIZE> tmp = (it->second).mand;
                    if ((it->second).cost > uppers[next]->getMax() &&
                        tmp.count() < mid.count()) {
                        mid = tmp; 
                        new_cost = (it->second).cost;
                    }
                    ++it;
                }
                mid[n] = true;
                mid[next] = true;
                for (int i = 0; i < nbNodes(); i++) {
                    if (mid[i]) {
                        assert(i==next ||(preds[next] &(1<<i)) != 0);
                        assert(isMandatoryN(i));
                        ps.push_back(getNodeVar(i).getValLit());
                        ps.push_back(getUBeforeV(i,next).getValLit());
                        ps.push_back(getUBeforeV(n,i).getValLit());
                    }
                }
                forbidden_edges.clear();
                explain_dp(next,new_cost,n,mid,forbidden_edges);
                ps.insert(ps.end(), forbidden_edges.begin(), forbidden_edges.end());
                //ps.insert(ps.end(), expl.begin(), expl.end());
                ps.push_back(getNodeVar(next).getValLit());
                //ps = explain_naive(true);
                GiveFailureExplanation(ps);
            }

            return false;
        }
        

        n = next;
    }
    return true;
}


vector<bool> TDBoundedPathArrivals::getBiCC(int i, vector<int>& depth, 
                                    vector<int>& low, vector<bool>& visited,
                                    vector<int>& parent, 
                                    stack<int>& articulations,
                                    int d) {
    /*visited[i] = true;
    depth[i] = d;
    low[i] = d;
    int childCount = 0;
    bool isArticulation = (i == dest);
    for (int j = 0; j < adj[i].size(); j++) {
        int e = adj[i][j];
        if (isForbiddenE(e)) continue;
        int ni = (getEndnode(e,0) == i) ? getEndnode(e,1) : getEndnode(e,0);
        if (isForbiddenN(ni)) continue;
        if (!visited[ni]) {
            parent[ni] = i;
            getBiCC(ni, depth, low, visited, parent, articulations, d + 1);
            childCount++;
            if (low[ni] >= depth[i])
                isArticulation = true;
            low[i] = low[i] < low[ni] ? low[i] : low[ni];
        } else if (ni != parent[i]) {
            low[i] = low[i] < depth[ni] ? low[i] : depth[ni];
        }
    }
    if ((parent[i] != -1 && isArticulation)) {// || (parent[i] == -1 && childCount > 1))
        articulations.push(i);
        }*/

    //DReachabilityPropagator::FilteredLT lt(this,source,endnodes,incident,outgoing);
    //lt.init();
    //lt.LengauerTarjan::DFS();
    //lt.find_doms();

    vector<bool> doms = vector<bool>(nbNodes(), false);
    int curr = dest;
    while (curr != source) {
        articulations.push(curr);
        doms[curr] = true;
        curr = reachable->getDominatorsAlgorithm()->dominator(curr);
    }
    return doms;
}



class PositionPropagator : public Propagator {
    vector<vector<int> > in;
    vector<vector<int> > ou;
    vector<vector<int> > en;
    vec<BoolView> es;
    vec<IntVar*> pos;
    vector<int> fixed;
public:
    PositionPropagator(vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                       vec< vec<int> >& _en, vec<BoolView>& _es, vec<IntVar*>& _pos) 
        : Propagator(), es(_es) {
        in = vector<vector<int> >(_in.size(), vector<int>());
        for (int i = 0; i < _in.size(); i++)
            for (int j = 0; j < _in[i].size(); j++)
                in[i].push_back(_in[i][j]);

        ou = vector<vector<int> >(_out.size(), vector<int>());
        for (int i = 0; i < _out.size(); i++)
            for (int j = 0; j < _out[i].size(); j++)
                ou[i].push_back(_out[i][j]);
            
        en = vector<vector<int> >(_en.size(), vector<int>());
        for (int i = 0; i < _en.size(); i++)
            for (int j = 0; j < _en[i].size(); j++)
                en[i].push_back(_en[i][j]);

        _pos.copyTo(pos);

        for (int i = 0; i < pos.size(); i++)
            pos[i]->attach(this,i,EVENT_F);
    }

    void wakeup(int i, int c) {
        if (pos[i]->isFixed()) {
            fixed.push_back(i);
            pushInQueue();
        }
    }

    bool propagate() {
        for (uint i = 0; i < fixed.size(); i++) {
            int u = fixed[i];            
            int val = pos[u]->getVal();
            if (val == pos.size()) 
                continue; //No one behind the last!
            
            int count = 0;
            int last = -1;

            vec<Lit> prop; prop.push();
            vec<Lit> fail;
            prop.push(pos[u]->getValLit());
            fail.push(pos[u]->getValLit());
            for (uint j = 0; j < ou[u].size(); j++) {
                int e = ou[u][j];
                int v = en[e][1];
                if (so.lazy) {
                    if (es[e].isFixed() && es[e].isFalse()) {
                        prop.push(es[e].getValLit());
                        fail.push(es[e].getValLit());
                    }
                }

                if (!pos[v]->indomain(val+1)) {
                    if (so.lazy) {
                        prop.push(pos[v]->getLit(val+1,0));
                        fail.push(pos[v]->getLit(val+1,0));
                    }   
                } else {
                    count++;
                    last = v;
                }
            }

            if (count == 0) {
                //Nobody can be val+1
                GiveFailureExplanation(fail);
                return false;
            } else if (count == 1 && !pos[last]->isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    r = Reason_new(prop);
                }
                pos[last]->setVal(val+1, r);
            }
        }

        for (uint i = 0; i < fixed.size(); i++) {
            int u = fixed[i];            
            int val = pos[u]->getVal();
            if (val == 1)
                continue; //Nobody before the first
            int count = 0;
            int last = -1;

            vec<Lit> prop; prop.push();
            vec<Lit> fail;
            prop.push(pos[u]->getValLit());
            fail.push(pos[u]->getValLit());
            for (uint j = 0; j < in[u].size(); j++) {
                int e = in[u][j];
                int v = en[e][0];
                if (so.lazy) {
                    if (es[e].isFixed() && es[e].isFalse()) {
                        prop.push(es[e].getValLit());
                        fail.push(es[e].getValLit());
                    }
                }

                if (!pos[v]->indomain(val-1)) {
                    if (so.lazy) {
                        prop.push(pos[v]->getLit(val-1,0));
                        fail.push(pos[v]->getLit(val-1,0));
                    }   
                } else {
                    count++;
                    last = v;
                }
            }

            if (count == 0) {
                //Nobody can be val-1
                GiveFailureExplanation(fail);
                return false;
            } else if (count == 1 && !pos[last]->isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    r = Reason_new(prop);
                }
                pos[last]->setVal(val-1, r);
            }
        }

        return true;
    }


    void clearPropState() {
        fixed.clear();
        Propagator::clearPropState();
    }
};

class ClosestNextStrategy : public BranchGroup {
    
    vector<int> fixed_nodes;
    int last_dec_level;

    ClosestNextStrategy(vec<Branching*>& _x, VarBranch vb, bool t)
        : BranchGroup(_x,vb,t) {
        last_dec_level = engine.decisionLevel();
    }


public:
    static ClosestNextStrategy* search;
    static TDBoundedPath* bp;
    static ClosestNextStrategy* getClosestNextStrategy(vec<Branching*>& _x, VarBranch vb, bool t) {
        if (search == NULL) {
            search = new ClosestNextStrategy(_x,vb,t);
        }
        return search;
    }

    void setPropagator(TDBoundedPath* _bp) {bp = _bp;}

    bool finished() {
	if (fin) return true;
	for (int i = 0; i < x.size(); i++) {
            if (!x[i]->finished()) {
                return false;
            }
	}
	fin = 1;
	return true;
    }

    bool backtrack() {
        if (last_dec_level >= engine.decisionLevel()) {
            fixed_nodes.resize(engine.decisionLevel());
            last_dec_level = engine.decisionLevel();
            return true;
        }
        last_dec_level = engine.decisionLevel();
        return false;
    }


    DecInfo* branchEarliest() {
        int last_node = -1;
        int max = -1;
        int count = 0;

        vector<int> values(bp->nbNodes());
        std::iota(values.begin(), values.end(), 1);
        vector<int> nodes(bp->nbNodes() + 1, -1);
        nodes[1] = bp->source;
        nodes[nodes.size()-1] = bp->dest;

        for (int i = 0; i < x.size(); i++) {
            if (((IntVar*)x[i])->isFixed()) {
                count++;
                nodes[((IntVar*)x[i])->getVal()] = i + 1;
            }
        }
        if (count == x.size()) {
            fin = true;
            return NULL;
        }


        // for (int i = 0; i < nodes.size(); i++) {
        //     cout<< nodes[i]<<" ";
        // }
        // cout<<endl;


        for (uint i = 2; i < nodes.size(); i++) { 
            //nodes[0] is dummy and nodes[1] == 0
            if(nodes[i] == -1) {
                //no one at position i
                max = i - 1;
                last_node = nodes[max];
                break;
            }
        }

        if (last_node == -1) {
            //There is no "nodes[i] == -1"
            return NULL;
        } 

        int ready = bp->earliest_ready[last_node];

        // cout<<"[1, ";
        // for (int i = 0; i < x.size(); i++){
        //     if (((IntVar*)x[i])->isFixed()) {
        //         cout<< ((IntVar*)x[i])->getVal()<<", ";
        //     } else {
        //         cout <<"?, ";
        //     }            
        // }
        // cout<<"11]"<<endl;


        // for (int i = 0; i < x.size(); i++){
        //     cout<<((IntVar*)x[i])->indomain(max - 1);
        // }
        // cout<<endl;


        int closest = -1;
        int distance = -1;
        for (unsigned int i = 0; i < bp->outgoing[last_node].size(); i++) {
            int e = bp->outgoing[last_node][i];
            if (bp->getEdgeVar(e).isFixed() && bp->getEdgeVar(e).isFalse())
                continue;
            int o = bp->getHead(e);
            if (o == 0 || o > x.size()) //Already fixed, ignore them
                continue;
            //cout<<"Gotta see at least one! "<< o <<" "<<((IntVar*)x[o - 1])->indomain(max + 1)<<endl;
            //assert(((IntVar*)x[o - 1])->indomain(max + 1));

            //What to do if a node is not available? atPosition[0] = ?
            //if (bp->getNodeVar(o).isFixed() && bp->getNodeVar(o).isFalse())
            //    continue;
            if (!((IntVar*)x[o - 1])->isFixed() && ((IntVar*)x[o - 1])->indomain(max + 1)) {
                if (distance == -1 || distance > bp->weight(e,ready)) {
                    distance = bp->weight(e,ready);
                    closest = o;
                }
            }            
        }

        if (closest != -1) {
            //cout<<"Fixing "<< closest<<" to "<<max+1<< "   ("<<engine.decisionLevel()<<")"<<endl;
            return new DecInfo(x[closest - 1], max + 1, 1); //o is at the next position
        }
        assert(finished());
        return NULL;
    }

    DecInfo* branchLatest() {
        int last_node = -1;
        int max = -1;
        int count = 0;

        vector<int> values(bp->nbNodes());
        std::iota(values.begin(), values.end(), 1);
        vector<int> nodes(bp->nbNodes() + 1, -1); //nodes[a] == b -> b is at position a
        nodes[1] = bp->source;
        nodes[nodes.size()-1] = bp->dest;

        for (int i = 0; i < x.size(); i++) {
            if (((IntVar*)x[i])->isFixed()) {
                count++;
                nodes[((IntVar*)x[i])->getVal()] = i + 1;
            }
        }
        if (count == x.size()) {
            fin = true;
            return NULL;
        }


        // for (int i = 0; i < nodes.size(); i++) {
        //     cout<< nodes[i]<<" ";
        // }
        // cout<<endl;


        for (uint i = nodes.size() - 1; i >= 2; i--) { 
            //nodes[0] is dummy and nodes[1] == 0
            if(nodes[i] == -1) {
                //no one at position i
                max = i + 1;
                last_node = nodes[max];
                break;
            }
        }

        if (last_node == -1) {
            //There is no "nodes[i] == -1"
            return NULL;
        } 

        int ready = bp->latest_arrivals[last_node];

        // cout<<"[1, ";
        // for (int i = 0; i < x.size(); i++){
        //     if (((IntVar*)x[i])->isFixed()) {
        //         cout<< ((IntVar*)x[i])->getVal()<<", ";
        //     } else {
        //         cout <<"?, ";
        //     }            
        // }
        // cout<<"11]"<<endl;

        // for (int i = 0; i < x.size(); i++){
        //     cout<<((IntVar*)x[i])->indomain(max - 1);
        // }
        // cout<<endl;

        int closest = -1;
        int distance = -1;
        for (unsigned int i = 0; i < bp->incident[last_node].size(); i++) {
            int e = bp->incident[last_node][i];
            if (bp->getEdgeVar(e).isFixed() && bp->getEdgeVar(e).isFalse())
                continue;
            int o = bp->getTail(e);
            if (o == 0 || o > x.size()) //Already fixed, ignore them
                continue;
            //cout<<"Gotta see at least one! "<< o <<" "<<((IntVar*)x[o - 1])->indomain(max - 1)<<endl;
            //assert(((IntVar*)x[o - 1])->indomain(max - 1));
            //What to do if a node is not available? atPosition[0] = ?
            //if (bp->getNodeVar(o).isFixed() && bp->getNodeVar(o).isFalse())
            //    continue;
            if (!((IntVar*)x[o - 1])->isFixed() && ((IntVar*)x[o - 1])->indomain(max - 1)) {
                if (distance == -1 || distance > bp->weight(e,ready)) {
                    distance = bp->weight(e,ready);
                    closest = o;
                }
            }            
        }

        if (closest != -1) {
            //cout<<"Fixing "<< closest<<" to "<<max-1<< "   ("<<engine.decisionLevel()<<")"<<endl;
            return new DecInfo(x[closest - 1], max - 1, 1); //o is at the next position
        }
        assert(finished());
        return NULL;
    }


    DecInfo* branch() {
        int left = engine.decisionLevel() % 2;
        if (left) {
            return branchEarliest();
        } else {
            return branchLatest();
        }
    }


};
ClosestNextStrategy* ClosestNextStrategy::search = NULL;
TDBoundedPath* ClosestNextStrategy::bp = NULL;




void td_bounded_path_pre(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                         vec<BoolView>& _order, vec<IntVar*> pos,
                         vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
                         vec< vec<int> >& _en, vec<vec< int> >& _ws, vec<int> _ds,IntVar* w) {
    if (_vs[from].setValNotR(true))
        _vs[from].setVal(true,NULL);
    if (_vs[to].setValNotR(true))
        _vs[to].setVal(true,NULL);
#ifndef KF
    path(from,to,_vs,_es,_in,_out,_en);
#endif
#ifdef KF
    std::map< node_id, vec<edge_id> > adj;
    for (int i = 0; i < _in.size(); i++) {
        for (int j = 0; j < _in[i].size(); j++) {
            adj[i].push(_in[i][j]);
        }
        for (int j = 0; j < _out[i].size(); j++) {
            adj[i].push(_out[i][j]);
        }
    }
    GraphPropagator* gp = new GraphPropagator(_vs,_es, _en);
    gp->attachToAll();
#endif
}

void td_bounded_path_post(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
        vec<BoolView>& _order, vec<IntVar*> pos,
        vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
        vec< vec<int> >& _en, vec<vec< int> >& _ws, vec<int> _ds,IntVar* w,
        TDBoundedPath* bp) {
    PositionPropagator* pp = new PositionPropagator(_in,_out,_en, _es,pos);
    if (so.check_prop)
        engine.propagators.push(pp);


    //#define DIFFLOGIC
#ifdef DIFFLOGIC
    DiffLogic* dl = new DiffLogic(_order.size());
    for (int i = 0; i < _vs.size(); i++) {
        for (int j = 0; j < _vs.size(); j++) {
            if (i == j) continue;
            dl->addReifyDiff(&(bp->getUBeforeV(i,j)), pos[i], pos[j], -1);
        }
    }
#endif
}

void td_bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                     vec<BoolView>& _order, vec<BoolView>& _order_opt, vec<IntVar*> pos,
                     vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
                     vec< vec<int> >& _en, vec<vec< int> >& _ws, vec<int> _ds,IntVar* w) {

    td_bounded_path_pre(from, to, _vs, _es, _order, pos, _in, _out, _en, _ws,_ds,w);
    TDBoundedPath* bounded_path_p = new TDBoundedPath(from, to,_vs,_es,
                                                      _order,_order_opt,
                                                      _in,_out,_en,_ws,_ds,w);
    if (so.check_prop)
        engine.propagators.push(bounded_path_p);
    ClosestNextStrategy::bp = bounded_path_p;
    //td_bounded_path_post(from, to, _vs, _es, _order, pos, _in, _out, _en, _ws, _ds, w,bounded_path_p);

}

void td_bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
                     vec<BoolView>& _order, vec<BoolView>& _order_opt, vec<IntVar*> pos,
                     vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
                     vec< vec<int> >& _en, vec<vec< int> >& _ws, vec<int> _ds, //durations
                     IntVar* w, vec<IntVar*> _lowers, vec<IntVar*> _uppers) {

    if (_vs[from].setValNotR(true))
        _vs[from].setVal(true,NULL);
    if (_vs[to].setValNotR(true))
        _vs[to].setVal(true,NULL);

    new PathDeg1(_vs,_es,_in,_out,_en);
    DReachabilityPropagator* dr = dtree(from,_vs,_es,_in,_out,_en);
    DReachabilityPropagator* dr2 = reversedtree(to,_vs,_es,_in,_out,_en);
    //td_bounded_path_pre(from, to, _vs, _es, _order, pos, _in, _out, _en, _ws, _ds,w);
    TDBoundedPathArrivals* bounded_path_p = new TDBoundedPathArrivals(from, to,_vs,_es,
                                                              _order,_order_opt,
                                                              _in,_out,
                                                              _en,_ws,_ds,w,
                                                              _lowers,_uppers);
    bounded_path_p->set_reachable(dr, dr2);
    if (so.check_prop)
        engine.propagators.push(bounded_path_p);
    ClosestNextStrategy::bp = bounded_path_p;
    //td_bounded_path_post(from, to, _vs, _es, _order, pos, _in, _out, _en, _ws, _ds,w, bounded_path_p);

}



/*
void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
    if (var_branch == CLOSESTNEXT_ORDER) {
        engine.branching->add(ClosestNextStrategy::getClosestNextStrategy(x, var_branch, true));
        return;
    }

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
