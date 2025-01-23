#include "core/propagator.h"
#include "support/union_find.h"
#include <iostream>
#include <vector>
#include <queue>          // std::priority_queue

#define VRPTW_DEBUG(level,arg)                                     \
    if(1 < level){ std::cout<<__FILE__<<" "<<__LINE__<<" "<<arg<<std::endl;}

#define MAX(a,b) (a>b?a:b)

using namespace std;


#define reasonToFail(vv)       \
    Clause *expl = Clause_new(vv); \
    expl->temp_expl = 1; \
    sat.rtrail.last().push(expl); \
    sat.confl = expl;

class VRPTWPropagator : public Propagator {



    int nbVisits;
    vec<BoolView> before;
    vec<IntVar*> beginWork;
    vector< vector<int> > travelt;
    vec<int> startt;
    vec<int> endt;
    vec<int> duration;

    enum {BEFORE, NOT_BEFORE, UNK};

    //If a is before b, then return BEF
    int order(int a, int b) {
        if (!before[a*nbVisits+b].isFixed())
            return UNK;
        if (before[a*nbVisits+b].isTrue())
            return BEFORE;
        else
            return NOT_BEFORE;
    }

    //Get the bool view that says whether a is before b
    BoolView& getBefore(int a, int b) {
        return before[a*nbVisits+b];
    }

    std::vector< std::pair<int,int> > bChanged;
    std::vector<int> bWUpChanged;
    std::vector<int> bWLoChanged;
    
public:
    VRPTWPropagator(vec<BoolView>& _before, vec<IntVar*>& _beginWork,
                    vec<int>& _travel, vec<int>& _starts, vec<int>& _ends, 
                    vec<int>& _dur) :
        nbVisits(_starts.size()), before(_before), beginWork(_beginWork),
        startt(_starts),endt(_ends),duration(_dur){

        VRPTW_DEBUG(1,"CONSTRUCTOR");
        assert(before.size() == nbVisits*nbVisits);

        for (int i = 0; i < nbVisits; i++){
            vector<int> tmp;
            for (int j = 0; j < nbVisits; j++) {
                tmp.push_back(_travel[i*nbVisits+j]);
                assert(_travel[i*nbVisits+j] == _travel[j*nbVisits+i]);
            }
            travelt.push_back(tmp);
        }


        for (int i = 0; i < nbVisits*nbVisits; i++)
            before[i].attach(this,i,EVENT_LU);

        for (int i = 0; i < nbVisits; i++) {
            beginWork[i]->attach(this,nbVisits*nbVisits+i,EVENT_LU);
            if (beginWork[i]->getMax() > endt[i])
                beginWork[i]->setMax(endt[i]);
        }

    }



    void wakeup(int i, int c) {
        if (i < nbVisits*nbVisits) {
            if (getBefore(i/nbVisits,i%nbVisits).isTrue()) {
                bWLoChanged.push_back(i/nbVisits);
                bWLoChanged.push_back(i%nbVisits);
                bChanged.push_back(make_pair(i/nbVisits,i%nbVisits));
                pushInQueue();
            }
        } else {
            bWLoChanged.push_back(i-nbVisits*nbVisits);
            pushInQueue();
        }
    }


    //Check if going from i to j is possible.
    //If its not, set it to false.
    //If i goes before j in the current order, then
    //update their bounds
    bool updatePossibleAndFixedOrders(int i, int j) {
        IntVar* x = beginWork[i];
        IntVar* y = beginWork[j];
        int x_max = x->getMax();
        int y_min = y->getMin();
        int x_min = x->getMin();
        int y_max = y->getMax();

        if (y_max < x_min + travelt[i][j] + duration[i]) {
            vec<Lit> ps;  
            if (getBefore(i,j).isTrue()) {
                if (so.lazy) {
                    ps.push(y->getMaxLit()); 
                    ps.push(x->getMinLit());
                    ps.push(getBefore(i,j).getValLit()); 
                    reasonToFail(ps);
                }
                return false;
            } else if (!getBefore(i,j).isFixed()){
                Clause* r = NULL;
                if (so.lazy) { 
                    ps.push();
                    ps.push(y->getMaxLit()); 
                    ps.push(x->getMinLit());
                    r = Reason_new(ps);
                }
                getBefore(i,j).setVal(false,r);
            }
        } else if (getBefore(i,j).isTrue()){
            if (y_min < x_min + travelt[i][j] + duration[i]) {
                Clause* r = NULL;
                if (so.lazy) { 
                    vec<Lit> ps;
                    ps.push();
                    ps.push(getBefore(i,j).getValLit()); 
                    ps.push(x->getMinLit());
                    r = Reason_new(ps);
                }
                y->setMin(x_min + travelt[i][j] + duration[i],r);
            }
            if (x_max > y_max - travelt[i][j] - duration[i]) {
                Clause* r = NULL;
                if (so.lazy) { 
                    vec<Lit> ps;
                    ps.push();
                    ps.push(getBefore(i,j).getValLit()); 
                    ps.push(y->getMaxLit());
                    r = Reason_new(ps);
                }
                x->setMax(y_max - travelt[i][j] - duration[i],r);
            }
        } 
        return true;
    }


    struct PQdata{
        int u;
        int v;
        int d;
        PQdata(int _u, int _v, int _d):u(_u),v(_v),d(_d){}
    };

    struct PQSort {
        bool operator() (struct PQdata i,struct PQdata j) 
        { return (i.d<j.d); }
    } pqsort;



    bool propagate() {
        for (unsigned int c = 0; c < bWLoChanged.size(); c++) {
            int i = bWLoChanged[c];
            for (int j = 0; j < nbVisits; j++) {
                if (i == j) 
                    continue;

                //Extra propagation to ahve a consisten state for the 
                //following more important propagations
                if (getBefore(i,j).isTrue() && getBefore(j,i).isTrue()) {
                    if (so.lazy) {
                        vec<Lit> ps;
                        ps.push(getBefore(i,j).getValLit());
                        ps.push(getBefore(j,i).getValLit());
                        reasonToFail(ps);
                        return false;
                    }
                } else if (getBefore(i,j).isTrue() && !getBefore(j,i).isFixed()) {
                    Clause* r  = NULL;
                    if (so.lazy) {
                        vec<Lit> ps;
                        ps.push();
                        ps.push(getBefore(i,j).getValLit());
                        r = Reason_new(ps);
                    }
                    getBefore(j,i).setVal(false,r);
                } else if (getBefore(j,i).isTrue() && !getBefore(i,j).isFixed()) {
                    Clause* r  = NULL;
                    if (so.lazy) {
                        vec<Lit> ps;
                        ps.push();
                        ps.push(getBefore(j,i).getValLit());
                        r = Reason_new(ps);
                    }
                    getBefore(i,j).setVal(false,r);
                }

                //*
                if (!updatePossibleAndFixedOrders(i,j))
                    return false;
                if (!updatePossibleAndFixedOrders(j,i))
                    return false;
                //*/
            }
        }


        for (unsigned int c = 0; c < bChanged.size(); c++) {
            int a = bChanged[c].first;
            int b = bChanged[c].second;
            int maxIndex = MAX(a,b);
            int durs = 0;
            vec<Lit> ps; 
            if (so.lazy) {ps.push();}
            vector<int> between;
            vector<PQdata> orderedEdges;
            between.push_back(a);
            if (so.lazy) {ps.push(getBefore(a,b).getValLit());}
            for (int x = 0; x < nbVisits; x++) {
                if (x == a || !getBefore(x,b).isTrue()) 
                    continue;

                //We look at things that are undecided and we can infer

                //Earliest time I can get to X from X
                int arrive_x = beginWork[a]->getMin() + duration[a] + travelt[a][x];
                //Earliest time I can get to A from X
                int arrive_a = beginWork[x]->getMin() + duration[x] + travelt[x][a];

                // Can a be before x?
                if (arrive_x <= beginWork[x]->getMax()) {
                    //If so, can x be before a?
                    if (arrive_a <= beginWork[a]->getMax()) {
                        //a can be before x and x can be before a. Nothing to do.
                    } else {
                        //a can be before x, but x can't be befora a, so:
                        if (getBefore(a,x).isFalse()) {
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push(beginWork[a]->getMaxLit());
                                ps.push(beginWork[x]->getMinLit());
                                ps.push(getBefore(a,b).getValLit());  
                                ps.push(getBefore(x,b).getValLit());
                                ps.push(getBefore(a,x).getValLit());
                                reasonToFail(ps);
                            }
                            return false;
                        }

                        if(!getBefore(a,x).isFixed()) {
                            //a has to be before x
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,b).getValLit());
                                ps.push(getBefore(x,b).getValLit());
                                ps.push(beginWork[a]->getMaxLit());
                                ps.push(beginWork[x]->getMinLit());
                                r = Reason_new(ps);
                            }
                            getBefore(a,x).setVal(true,r);
                        }
                        //Additionaly update LBs
                        if (beginWork[x]->getMin() < arrive_x) {
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,x).getValLit());
                                ps.push(beginWork[a]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            beginWork[x]->setMin(arrive_x,r);
                        }
                    }
                } else {
                    //a cannot be before x
                    //Can x be before a?
                    if (arrive_a <= beginWork[a]->getMax()) {
                        //x can be before a, and a cannot be before x, so:
                        if (getBefore(x,a).isFalse()) {
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push(beginWork[a]->getMinLit());
                                ps.push(beginWork[x]->getMaxLit());
                                ps.push(getBefore(a,b).getValLit());  
                                ps.push(getBefore(x,b).getValLit());
                                ps.push(getBefore(x,a).getValLit());
                                reasonToFail(ps);
                            }
                            return false;
                        }


                        if (!getBefore(x,a).isFixed()) {
                            //a has to be before x
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,b).getValLit());
                                ps.push(getBefore(x,b).getValLit());
                                ps.push(beginWork[a]->getMinLit());
                                ps.push(beginWork[x]->getMaxLit());
                                r = Reason_new(ps);
                            }
                            getBefore(x,a).setVal(true,r);
                        }
                        //Additionaly update LBs
                        if (beginWork[a]->getMin() < arrive_a)  {
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(x,a).getValLit());
                                ps.push(beginWork[x]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            beginWork[a]->setMin(arrive_a,r);
                        }
                    } else {
                        //None can be before each other, so we fail:
                        if (so.lazy) {
                            vec<Lit> ps;
                            ps.push(beginWork[a]->getMinLit());
                            ps.push(beginWork[x]->getMinLit());
                            ps.push(beginWork[a]->getMaxLit());
                            ps.push(beginWork[x]->getMaxLit());
                            ps.push(getBefore(a,b).getValLit());  
                            ps.push(getBefore(x,b).getValLit());
                            reasonToFail(ps);
                        }
                        return false;
                    }
                }

                if (getBefore(a,x).isTrue() && getBefore(x,b).isTrue()) {
                    for (unsigned int k = 0; k < between.size(); k++)
                        orderedEdges.push_back(PQdata(between[k],x,travelt[between[k]][x]));
                    between.push_back(x);
                    durs += duration[x];
                    if (so.lazy) {
                        ps.push(getBefore(x,b).getValLit());
                        ps.push(getBefore(a,x).getValLit());
                    }
                    maxIndex = MAX(maxIndex,x);
                }

            }


            //Look for MST
            for (unsigned int k = 0; k < between.size(); k++)
                orderedEdges.push_back(PQdata(between[k],b,travelt[between[k]][b]));
            between.push_back(b);
            std::sort (orderedEdges.begin(), orderedEdges.end(), pqsort);
            UF<int> uf(maxIndex+1);
            unsigned int count = 0;
            int it = 0;
            int time = 0;
            while (count < between.size() - 1) {
                if (!uf.connected(orderedEdges[it].u, orderedEdges[it].v)) {
                    time += orderedEdges[it].d;
                    count++;
                }
                it++;
            }

            if (beginWork[b]->getMin() < (durs+time+beginWork[a]->getMin())) {
                //cout <<"MIN " << beginWork[b]->getMin() <<" "<< (durs+time+beginWork[a]->getMin())<<endl;
                Clause* r = NULL;
                if (so.lazy) {
                    ps.push(beginWork[a]->getMinLit());
                    r = Reason_new(ps);
                }
                beginWork[b]->setMin(durs+time+beginWork[a]->getMin(),r);
            }
            
        }

        return true;
    }




    void wakeup2(int i, int c) {
        VRPTW_DEBUG(1,"WAKEUP "<<i<<" "<<c);
        
        //'before' changed
        if (i < nbVisits*nbVisits) {
            //i%nbVisits is before i/nbVisits
            if (getBefore(i/nbVisits,i%nbVisits).isTrue()) {
                bChanged.push_back( make_pair(i/nbVisits, i%nbVisits));
            }
        } else {
            if (c & EVENT_L)
                bWLoChanged.push_back(i-nbVisits*nbVisits);
            else if (c & EVENT_U)
                bWUpChanged.push_back(i-nbVisits*nbVisits);
        }

        pushInQueue();
    }


    bool propagate2() {
        VRPTW_DEBUG(1,"PROPAGATE");
        for (unsigned int i = 0; i < bChanged.size(); i++) {
            if (!propagateOrder(bChanged[i].first, bChanged[i].second))
                return false;
        }
        for (unsigned int i = 0; i < bWLoChanged.size(); i++) {
            if (!propagateBeginLater(bWLoChanged[i]))
                return false;
        }
        for (unsigned int i = 0; i < bWUpChanged.size(); i++) {
            if (!propagateBeginEarlier(bWUpChanged[i]))
                return false;
        }


        return true;
    }

    //propagate that a is before b
    bool propagateBefore(int a, int b) {
        VRPTW_DEBUG(1,"PropagateBefore");

        int earliestEnd = beginWork[a]->getMin() + duration[a];

        if (earliestEnd+travelt[a][b] > beginWork[b]->getMax()) {
            if(so.lazy) {
                vec<Lit> ps;
                ps.push(beginWork[a]->getMinLit());
                ps.push(beginWork[b]->getMaxLit());
                ps.push(getBefore(a,b).getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        }
        //Updating lower bound of the time the task at b can start
        if (beginWork[b]->getMin() < earliestEnd+travelt[a][b]) {
            Clause* r = NULL;
            if (so.lazy) {
                vec<Lit> ps;
                ps.push();
                ps.push(beginWork[a]->getMinLit());
                ps.push(getBefore(a,b).getValLit());
                r = Reason_new(ps);
            }
            beginWork[b]->setMin(earliestEnd+travelt[a][b],r);
        }
        if (beginWork[a]->getMax() > beginWork[b]->getMax() - duration[a] - travelt[a][b]) {
            Clause* r = NULL;
            if (so.lazy) {
                vec<Lit> ps;
                ps.push();
                ps.push(beginWork[b]->getMaxLit());
                ps.push(getBefore(a,b).getValLit());
                r = Reason_new(ps);
            }
            beginWork[a]->setMax(beginWork[b]->getMax() - duration[a] - travelt[a][b],r);
        }
        return true;
        //Trying to reduce the domain of hte different positions
        //where a can be, knowing that a is before b
        //We check where a fits or doesn't fit in the chain of things
        //that are before b
        for (int x = 0; x < nbVisits; x++) {
            if (x == a || order(x,b) != BEFORE) 
                continue;

            //Assume that 'a before x' or 'x before a' are a legal 
            //assignment.
            //If they aren't, we would detect in another propagation.
            //We look at things that are undecided and we can infer
            if (order(a,x) == UNK) {
                int earliestEndX = beginWork[x]->getMin() + duration[x];
                // Can a be before x?
                if (earliestEnd+travelt[a][x] <= beginWork[x]->getMax()) {
                    //If so, can x be before a?
                    if (earliestEndX+travelt[a][x] <= beginWork[a]->getMax()) {
                        //a can be before x and x can be before a. Nothing to do.
                    } else {
                        //a can be before x, but x can't be befora a, so:
                        if(!getBefore(a,x).isFixed()) {
                            //a has to be before x
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,b).getValLit());
                                ps.push(getBefore(x,b).getValLit());
                                //a didn't fit after x:
                                ps.push(beginWork[x]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            getBefore(a,x).setVal(true,r);
                        }
                        //Additionaly update LBs
                        if (beginWork[x]->getMin() < earliestEnd + travelt[a][x]) {
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,x).getValLit());
                                ps.push(beginWork[a]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            beginWork[x]->setMin(earliestEnd+travelt[a][x],r);
                        }
                    }
                } else {
                    //a cannot be before x
                    //Can x be before a?
                    if (earliestEndX+travelt[a][x] <= beginWork[a]->getMax()) {
                        //x can be before a, and a cannot be before x, so:
                        if (!getBefore(x,a).isFixed()) {
                            //a has to be before x
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(a,b).getValLit());
                                ps.push(getBefore(x,b).getValLit());
                                //x didn't fit after a:
                                ps.push(beginWork[a]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            getBefore(x,a).setVal(true,r);
                        }
                        //Additionaly update LBs
                        if (beginWork[a]->getMin() < earliestEndX+travelt[a][x])  {
                            Clause* r = NULL;
                            if (so.lazy) {
                                vec<Lit> ps;
                                ps.push();
                                ps.push(getBefore(x,a).getValLit());
                                ps.push(beginWork[x]->getMinLit());  
                                r = Reason_new(ps);
                            }
                            beginWork[a]->setMin(earliestEndX+travelt[a][x],r);
                        }
                    } else {
                        //None can be before each other, so we fail:
                        if (so.lazy) {
                            vec<Lit> ps;
                            ps.push(beginWork[a]->getMinLit());
                            ps.push(beginWork[x]->getMinLit());
                            ps.push(getBefore(a,b).getValLit());  
                            ps.push(getBefore(x,b).getValLit());
                            Clause *expl = Clause_new(ps);
                            expl->temp_expl = 1;
                            sat.rtrail.last().push(expl);
                            sat.confl = expl;
                        }
                        return false;
                    }
                }
            }
        }
        return true;
    }

    //Propagate consequences of the order a,b or b,a
    bool propagateOrder(int a, int b) {
        if (a == b)
            return true;
        VRPTW_DEBUG(1,"PropagateOrder");
        
        //Check if I can actually get from a to b
        if (getBefore(a,b).isTrue()) {
            return propagateBefore(a,b);
            
        } else if (order(a,b) == NOT_BEFORE) {
            //We cannot do this, because we dont know if a and be are even 
            //on the same route!!
        }

        return true;
    }

    //Propagate that the time when a visit starts has changed and can only start later
    bool propagateBeginLater(int visit) {
        VRPTW_DEBUG(1,"PropagateBeginLater "<<visit<<" "<<beginWork.size());

        //We need to look if I can still get from visit to the visits after me
        //(i.e. the ones where before[visits,i] holds

        int earliestEnd = beginWork[visit]->getMin() + duration[visit];
        for (int i = 0; i < nbVisits; i++) {
            if (i == visit)
                continue;
            if (order(visit,i) == BEFORE) {
                if (earliestEnd+travelt[visit][i] > beginWork[i]->getMax()) {
                    if(so.lazy) {
                        vec<Lit> ps;
                        ps.push(beginWork[visit]->getMinLit());
                        ps.push(beginWork[i]->getMaxLit());
                        ps.push(getBefore(visit,i).getValLit());
                        Clause *expl = Clause_new(ps);
                        expl->temp_expl = 1;
                        sat.rtrail.last().push(expl);
                        sat.confl = expl;
                    }
                    return false;
                } else {
                    if (beginWork[i]->getMin() < earliestEnd+travelt[visit][i]) {
                        Clause* r = NULL;
                        if (so.lazy) {
                            vec<Lit> ps;
                            ps.push();
                            ps.push(beginWork[visit]->getMinLit());
                            ps.push(getBefore(visit,i).getValLit());
                            r = Reason_new(ps);
                        }
                        beginWork[i]->setMin(earliestEnd+travelt[visit][i],r);
                    }
                }
            } else if (order(visit,i) == UNK){ 
                //Extra propagation: find visits that I can't make after visit
                if (earliestEnd+travelt[visit][i] > beginWork[i]->getMax()) {
                    Clause* r = NULL;
                    if (so.lazy) {
                        vec<Lit> ps;
                        ps.push();
                        ps.push(beginWork[visit]->getMinLit());
                        ps.push(beginWork[i]->getMaxLit());
                        r = Reason_new(ps);
                    }
                    getBefore(visit,i).setVal(false,r);
                }
            } 
        }

        return true;
    }
    
    //Propagate that the time when a visit can start has changed to an earlier time 
    bool propagateBeginEarlier(int visit) {
        VRPTW_DEBUG(1,"PropagateBeginEarlier "<<visit<<" "<<beginWork.size());

        //We need to look for visits that are before visit, and see if visit
        // can still be after them.

        for (int i = 0; i < nbVisits; i++) {
            if (i == visit)
                continue;
            int earliestEndI = beginWork[i]->getMin() + duration[i];
            if (order(i,visit) == BEFORE) {
                if (earliestEndI+travelt[i][visit] > beginWork[visit]->getMax()) {
                    if(so.lazy) {
                        vec<Lit> ps;
                        ps.push(beginWork[i]->getMinLit());
                        ps.push(beginWork[visit]->getMaxLit());
                        ps.push(getBefore(i,visit).getValLit());
                        Clause *expl = Clause_new(ps);
                        expl->temp_expl = 1;
                        sat.rtrail.last().push(expl);
                        sat.confl = expl;
                    }
                    return false;
                } else {
                    if (beginWork[visit]->getMin() < earliestEndI+travelt[i][visit]) {
                        Clause* r = NULL;
                        if (so.lazy) {
                            vec<Lit> ps;
                            ps.push();
                            ps.push(beginWork[i]->getMinLit());
                            ps.push(getBefore(i,visit).getValLit());
                            r = Reason_new(ps);
                        }
                        beginWork[visit]->setMin(earliestEndI+travelt[i][visit],r);
                    }
                }
            } else if (order(i,visit) == UNK){ 
                //Extra propagation: find visits that I can't make before visit anymore
                if (earliestEndI+travelt[i][visit] > beginWork[visit]->getMax()) {
                    Clause* r = NULL;
                    if (so.lazy) {
                        vec<Lit> ps;
                        ps.push();
                        ps.push(beginWork[i]->getMinLit());
                        ps.push(beginWork[visit]->getMaxLit());
                        ps.push(beginWork[visit]->getMaxLit());
                        r = Reason_new(ps);
                    }
                    getBefore(i,visit).setVal(false,r);
                }
            } 
        }

        return true;
    }


    void clearPropState() {
        VRPTW_DEBUG(1,"CLEARPROPSTATE");
        Propagator::clearPropState();
        bChanged.clear();
        bWUpChanged.clear();
        bWLoChanged.clear();
    }

};



void vrptw(vec<BoolView>& before, vec<IntVar*>& beginWork,
           vec<int>& travel, vec<int>& starts, vec<int>& ends, vec<int>& dur) {

    new VRPTWPropagator(before,beginWork,travel,starts,ends,dur);
}
