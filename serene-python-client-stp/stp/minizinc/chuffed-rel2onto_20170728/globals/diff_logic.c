#include "core/propagator.h"
#include "support/misc.h"
#include "globals/diff_logic.h"

using namespace std;

    // Whether binary priority queue should be used instead of a linear
    // operation for the shortest path calculations
#define DLUSEBINPRIOQUEUE 1

#define DLDEBUGMSG 0
#define DLMSG(...) do { if (DLDEBUGMSG) {fprintf(stderr, "DLLOG %4d: ",  __LINE__); fprintf(stderr, __VA_ARGS__);} } while (0)

/*
 * General function declarations
 */

static void submit_conflict_explanation(vec<Lit> & expl);
static Clause * get_reason_for_update(vec<Lit> & expl);
static inline Lit getNegGeqLit(IntVar * v, int val);
static inline Lit getNegLeqLit(IntVar * v, int val);

static bool doPropagation(DifferenceLogic * diff);


typedef struct {
    IntVar * _var;    // Variable
    int      _id;     // Unique ID of the variable
    int      _index;  // Internal unique index of the variable
    int      _pi;     // Value of the valid potential function
} DLNode;

typedef struct {
    DLNode * _node;     // Target node
    Tint   * _weight;   // Edge weight
    Tint   * _consId;   // Id of difference logic constraint
} DLEdge;

typedef struct {
    Tint  *  _size;     // Size of the array in _edges
    int      _cap;      // Capacity of the array in edges
    DLEdge * _edges;    // Array of edges
} DLEdgeContainer;

typedef enum {
    DLPi = 0,
    DLDelta,
    DLSigma,
    DLLambda
} DLConsLabel;

typedef enum {
    DLConsPure = 0,
    DLConsReif,
    DLConsHalf
} DLConsType;

    // Difference logic constraint of different type
    //  - always true:        x - y <= d
    //  - reified:      b <-> x - y <= d
    //  - half-reified: b  -> x - y <= d
typedef struct {
    BoolView * _b;
    IntVar   * _x;
    IntVar   * _y;
    int        _d;
    DLConsType   _type;
    Tint      * _prev;
    Tint      * _next;
    Tint      * _label;
} DLCons;

typedef struct {
    Tint    _size;     // Size of the array '_cons'
    int    _cap;      // Capacity of the array '_cons'
    DLCons * _cons;     // Array of all difference logic constraints
} DLConsContainer;

typedef struct {
    int   _size;
    int   _cap;
    int * _array;
} DLIntContainer;

struct DLTempCons {
    BoolView   * _b;
    IntVar     * _x;
    IntVar     * _y;
    int          _d;
    DLConsType   _t;
    DLTempCons(BoolView * b, IntVar * x, IntVar * y, int d, DLConsType t) : _b(b), _x(x), _y(y), _d(d), _t(t) {}
};

#define DLARRAYINCR 100

// Global Difference (Logic) Constraint
//
class DifferenceLogic : public Propagator {
public:
    //vec<IntVar*>  _nodes;
    
    DLNode          * _nodes0;      // Nodes in the graph
    DLEdgeContainer * _succ0;       // Outgoing edges
    DLEdgeContainer * _pred0;       // Ingoing edges
    DLConsContainer   _cons0;       // Difference logic constraints
    vec<DLTempCons>   _tempCons;    // Temporary storage of recently added constraints
    vec<int>          _tempBind;    // Temporary storage of recently bind (half)-reified constraints

    Tint     _size;    // Number of nodes/variables
    int      _cap;     // Capacity of the array '_nodes0'
    
    // Maintainance of the constraint states
    //
    Tint _piFirst;     // Assigned and propagated constraints
    Tint _piLast;      // Assigned and propagated constraints
    Tint _deltaFirst;  // Implied constraints from constraints in '_PI'
    Tint _deltaLast;   // Implied constraints from constraints in '_PI'
    Tint _sigmaFirst;  // Assigned constraints, but not propagated yet
    Tint _sigmaLast;   // Assigned constraints, but not propagated yet
    Tint _lambdaFirst; // Unassigned constraints
    Tint _lambdaLast;  // Unassigned constraints
    
    // Containers
    DLIntContainer _changeLB;
    DLIntContainer _changeUB;
    
    bool _expl_lift;    // Whether explanation should be lifted

    DifferenceLogic(int numItems) {
        DLMSG("Creating global difference constraint: numItems = %d\n", numItems);

        // Avoidance of negative capacity
        numItems = max(numItems, 0);
 
        // TODO Adjusting the priority
        priority = 2;
        
        // XXX Does such a parameter exist in chuffed?
        //_idempotent = true;

        //_nodes  = NULL;
        _nodes0 = NULL;
        _succ0  = NULL;
        _pred0  = NULL;
        _cons0._cap  = 0;
        _cons0._cons = NULL;
        _cons0._size = 0;
        _cap    = numItems;
        _size = 0;
    
        _changeLB._array = NULL;
        _changeLB._cap   = 0;
        _changeLB._size  = 0;
        _changeUB._array = NULL;
        _changeUB._cap   = 0;
        _changeUB._size  = 0;

    
        if (_cap > 0) {
            // Allocating memory
            _nodes0 = (DLNode *)          malloc(_cap * sizeof(DLNode         ));
            _succ0  = (DLEdgeContainer *) malloc(_cap * sizeof(DLEdgeContainer));
            _pred0  = (DLEdgeContainer *) malloc(_cap * sizeof(DLEdgeContainer));
        
            // Check whether memory allocation was successful
            if (_nodes0 == NULL || _succ0 == NULL || _pred0 == NULL) {
                ERROR("DifferenceLogic: Out of memory!");
            }
        
            // Copying elements to the C struct
            for (int i = 0; i < _cap; i++) {
                // Node initialisations
                _nodes0[i]._var = NULL;
                _nodes0[i]._id  = -1;
                _nodes0[i]._index = i;
                _nodes0[i]._pi  = 0;
            
                // Edge initialisations
                _succ0 [i]._edges = NULL;
                _succ0 [i]._cap   = 0;
                _succ0 [i]._size  = NULL;
                _pred0 [i]._edges = NULL;
                _pred0 [i]._cap   = 0;
                _pred0 [i]._size  = NULL;
            }
        }
        
        _piFirst     = -1;
        _piLast      = -1;
        _deltaFirst  = -1;
        _deltaLast   = -1;
        _sigmaFirst  = -1;
        _sigmaLast   = -1;
        _lambdaFirst = -1;
        _lambdaLast  = -1;
        
        _expl_lift   = false;
    }

    ~DifferenceLogic() {
        if (_nodes0 != NULL) free(_nodes0);
        if (_succ0 != NULL) {
            for (int i = 0; i < _size; i++) {
                if (_succ0[i]._size  != NULL) delete _succ0[i]._size;
                if (_succ0[i]._edges != NULL) {
                    assert(_succ0[i]._edges != NULL);
                    for (int j = 0; j < _succ0[i]._cap; j++) {
                        if (_succ0[i]._edges[j]._weight != NULL)
                            free(_succ0[i]._edges[j]._weight);
                        if (_succ0[i]._edges[j]._consId != NULL)
                            free(_succ0[i]._edges[j]._consId);
                    }
                    free(_succ0[i]._edges);
                }
            }
            free(_succ0);
        }
        if (_pred0 != NULL) {
            for (int i = 0; i < _size; i++) {
                if (_pred0[i]._size  != NULL) delete _pred0[i]._size;
                if (_pred0[i]._edges != NULL) {
                    assert(_pred0[i]._edges != NULL);
                    for (int j = 0; j < _pred0[i]._cap; j++) {
                        if (_pred0[i]._edges[j]._weight != NULL)
                            free(_pred0[i]._edges[j]._weight);
                        if (_pred0[i]._edges[j]._consId != NULL)
                            free(_pred0[i]._edges[j]._consId);
                    }
                    free(_pred0[i]._edges);
                }
            }
            free(_pred0);
        }
        if (_cons0._cons != NULL) {
            for (int i = 0; i < _cons0._cap; i++) {
                if (_cons0._cons[i]._label != NULL) free(_cons0._cons[i]._label);
                if (_cons0._cons[i]._next  != NULL) free(_cons0._cons[i]._next );
                if (_cons0._cons[i]._prev  != NULL) free(_cons0._cons[i]._prev );
            }
            free(_cons0._cons);
        }
        if (_changeLB._array != NULL) free(_changeLB._array);
        if (_changeUB._array != NULL) free(_changeUB._array);
    }


    // Wake up
    // TODO _cap is not static! Thus, it can't be use for subscription/wake-up
    void wakeup(int i, int c) {
        DLMSG("Entering wakeup of propagator %p with %d and %d\n", this, i, c);
        if (i < _cap) {
            // Bound update of an integer variable
            if ((c & EVENT_L) == EVENT_L) {
                DLMSG("\tLB change of x(%d)\n", i);
                queueChangeLB(i);
            }
            if ((c & EVENT_U) == EVENT_U) {
                DLMSG("\tUB change of x(%d)\n", i);
                queueChangeUB(i);
            }
        } 
        else {
            // Fixation of a Boolean variable
            const int k = i - _cap;
            if (_cons0._cons[k]._type == DLConsReif) {
                const BoolView * b = _cons0._cons[k]._b;
                DLMSG("\tBoolean fixation of reified constraint %d\n", k);
                DLMSG("\t\tb (%p): true %d; false %d\n", b, b->isTrue(), b->isFalse());
                bindReifDiff(k);
            } 
            else {
                assert(_cons0._cons[k]._type == DLConsHalf);
                const BoolView * b = _cons0._cons[k]._b;
                DLMSG("\tBoolean fixation of half-reified constraint %d\n", k);
                DLMSG("\t\tb (%p): true %d; false %d\n", b, b->isTrue(), b->isFalse());
                bindImplyDiff(k);
            }
        }
        pushInQueue();
        DLMSG("Leaving wakeup\n");
    }

    // Propagation
    bool propagate() {
        return doPropagation(this);
    }
	
    // Clearing the propagation state
    void clearPropState() {
        _tempCons.clear();
        _tempBind.clear();
		in_queue = false;
	}

    // Queueing the addition of difference logic constraints
    void addDifference(IntVar * x, IntVar * y, const int d) {
        DLMSG("Add x(%d) - y(%d) <= %d\n", x->var_id, y->var_id, d);
        _tempCons.push(DLTempCons(NULL, x, y, d, DLConsPure));
        pushInQueue();
    }
    void addReifyDifference(BoolView * b, IntVar * x, IntVar * y, const int d) {
        DLMSG("Add b(%p) <-> x(%d) - y(%d) <= %d\n", b, x->var_id, y->var_id, d);
        _tempCons.push(DLTempCons(b, x, y, d, DLConsReif));
        pushInQueue();
    }
    void addImplyDifference(BoolView * b, IntVar * x, IntVar * y, const int d) {
        DLMSG("Add b(%p) -> x(%d) - y(%d) <= %d\n", b, x->var_id, y->var_id, d);
        _tempCons.push(DLTempCons(b, x, y, d, DLConsHalf));
        pushInQueue();
    }

    void queueChangeLB(const int k);
    void queueChangeUB(const int k);

    void bindReifDiff(const int k);
    void bindImplyDiff(const int k);
};

/*******************************************************************************
 Function declarations
 ******************************************************************************/

typedef struct {
    int _key;
    int _id;
} DLPair;

typedef struct {
    int    _size;
    int    _cap;
    DLPair * _queue;
} DLBinPrioQueue;

static DLBinPrioQueue * newBinPrioQueue(const int cap);
static void deleteBinPrioQueue(DLBinPrioQueue * queue);
static inline bool isEmptyBinPrioQueue(DLBinPrioQueue * queue);
static int popBinPrioQueue(DLBinPrioQueue * queue);
static void insertItemInBinPrioQueue(DLBinPrioQueue * queue, const int id, const int key);
static void decreaseKeyInBinPrioQueue(DLBinPrioQueue * queue, const int id, const int newkey);
static void heapifyBinPrioQueue(DLBinPrioQueue * queue, int i);
static inline void moveItemUpwardInBinPrioQueue(DLBinPrioQueue * queue, int i);
static inline void swapItemsInBinPrioQueue(DLBinPrioQueue * queue, const int i, const int j);


static bool inContainer(const int k, const DLIntContainer * cont);
static void addToContainer(const int k, DLIntContainer * cont);

static int getNodeIndex(DifferenceLogic * diff, IntVar * x);

static int getEdge(DifferenceLogic * diff, const int x, const int y);
static int getEdgeAux(DLEdgeContainer * x_cont, const int y);

static int addConstraint(DifferenceLogic * diff, BoolView * b, IntVar * x, IntVar * y, int d, DLConsType t, DLConsLabel l);
static bool doCottonMaler(DifferenceLogic * diff, const int x, const int y, const int d, const int id);

static void labelLambdaConsAsSigma(DifferenceLogic * diff, const int indexCons);
static void labelSigmaLambdaConsAsDelta(DifferenceLogic * diff, const int indexCons);

static inline void analyse_implication_by_bounds(DifferenceLogic * diff, IntVar * x, IntVar * y, const int d, vec<Lit> & expl);

static void printGraph(DifferenceLogic * diff);


/*******************************************************************************
 Class member functions
 ******************************************************************************/

void 
DifferenceLogic::queueChangeLB(const int k)
{
    DLMSG("queueChangeLB %d (%d new lb: %d)\n", k, _nodes0[k]._id, _nodes0[k]._var->getMin());
    // Add 'k' to queue
    if (!inContainer(k, &_changeLB)) 
        addToContainer(k, &_changeLB);
}
void
DifferenceLogic::queueChangeUB(const int k)
{
    DLMSG("queueChangeUB %d (%d new ub: %d)\n", k, _nodes0[k]._id, _nodes0[k]._var->getMax());
    // Add 'k' to queue
    if (!inContainer(k, &_changeUB)) 
        addToContainer(k, &_changeUB);
}

void 
DifferenceLogic::bindReifDiff(const int k)
{
    assert(0 <= k && k < _cons0._size);
    // Run consistency check and add edge
    DLCons cons = _cons0._cons[k];
    if (*(cons._label) == DLLambda) {
        _tempBind.push(k);
        // Change label to Sigma (assigned constraints, but not propagated or checked)
        labelLambdaConsAsSigma(this, k);
    }
    DLMSG("_tempBind.size %d\n", _tempBind.size());
}

void
DifferenceLogic::bindImplyDiff(const int k)
{
    assert(0 <= k && k < _cons0._size);
    DLCons cons = _cons0._cons[k];
    if (*(cons._label) == DLLambda) {
        if (cons._b->isTrue()) {
            _tempBind.push(k);
            // Change label to Sigma (assigned constraints, but not propagated or checked)
            labelLambdaConsAsSigma(this, k);
        }
        else {
            // XXX Maybe, an own label for half-reified constraints that are not implied
            labelSigmaLambdaConsAsDelta(this, k);
        }
    }
}

/*******************************************************************************
 Container Operations
 ******************************************************************************/

static void resizeIntContainer(DLIntContainer * cont)
{
    const int newCap = cont->_cap + DLARRAYINCR;
    int * newArray = NULL;
    assert(newCap > cont->_cap);
    
    if (cont->_cap == 0) {
        assert(cont->_array == NULL);
        newArray = (int *) malloc(newCap * sizeof(int));
    }
    else {
        newArray = (int *) realloc(cont->_array, newCap * sizeof(int));
    }
    if (newArray == NULL) {
        ERROR("DifferenceLogic: Out of memory!");
    }
    
    cont->_array = newArray;
    cont->_cap   = newCap;
}

static bool inContainer(const int k, const DLIntContainer * cont)
{
    // XXX Check can be reduced to O(1) by marking the node
    for (int i = 0; i < cont->_size; i++) {
        if (cont->_array[i] == k) return true;
    }
    return false;
}

static void addToContainer(const int k, DLIntContainer * cont)
{
    if (cont->_size >= cont->_cap) {
        resizeIntContainer(cont);
    }
    cont->_array[(cont->_size)++] = k;
}

static void resetIntContainers(DifferenceLogic * diff)
{
    diff->_changeLB._size = 0;
    diff->_changeUB._size = 0;
}

/*******************************************************************************
 Constraint operations
 ******************************************************************************/

static void resizeConsContainer(DifferenceLogic * diff)
{
    DLMSG("Entering resizeConsContainer\n");

    DLCons * newCons = NULL;
    int newCap = diff->_cons0._cap + DLARRAYINCR;
    assert(newCap > diff->_cons0._cap);
    if (diff->_cons0._cap == 0) {
        newCons = (DLCons *) malloc(newCap * sizeof(DLCons));
        diff->_cons0._size = 0;
    }
    else {
        newCons = (DLCons *) realloc(diff->_cons0._cons, newCap * sizeof(DLCons));
    }
    
    if (newCons == NULL) {
        ERROR("DifferenceLogic: Out of memory!");
    }
    
    // Initialisation
    for (int i = diff->_cons0._cap; i < newCap; i++) {
        newCons[i]._b     = NULL;
        newCons[i]._x     = NULL;
        newCons[i]._y     = NULL;
        newCons[i]._d     = 0;
        newCons[i]._prev  = NULL;
        newCons[i]._next  = NULL;
        newCons[i]._type  = DLConsPure;
        newCons[i]._label = NULL;
    }
    
    // Updates
    diff->_cons0._cons = newCons;
    diff->_cons0._cap  = newCap;
    
    DLMSG("Leaving resizeConsContainer\n");
}

static int addConstraint(DifferenceLogic * diff, BoolView * b, IntVar * x, IntVar * y, int d, DLConsType t, DLConsLabel l)
{
    DLMSG("Entering addConstraint: size %d; cap %d\n", (int) diff->_cons0._size, diff->_cons0._cap);
    const int index = diff->_cons0._size;
    
    if (index >= diff->_cons0._cap) {
        resizeConsContainer(diff);
    }
    
    assert(index < diff->_cons0._cap);
    
    DLCons * cons = diff->_cons0._cons;
    cons[index]._b    = b;
    cons[index]._x    = x;
    cons[index]._y    = y;
    cons[index]._d    = d;
    cons[index]._type = t;
    
    if (cons[index]._prev == NULL) {
        assert(cons[index]._next == NULL && cons[index]._label == NULL);
        cons[index]._prev  = (Tint *) malloc(sizeof(Tint));
        cons[index]._next  = (Tint *) malloc(sizeof(Tint));
        cons[index]._label = (Tint *) malloc(sizeof(Tint));
        if (cons[index]._prev == NULL || cons[index]._next == NULL || cons[index]._label == NULL) {
            ERROR("DifferenceLogic: Out of memory!");
        }
        *(cons[index]._prev ) = -1;
        *(cons[index]._next ) = -1;
        *(cons[index]._label) =  l;
    }
    
    assert(cons[index]._prev  != NULL);
    assert(cons[index]._next  != NULL);
    assert(cons[index]._label != NULL);
    
    // Adding constraint to the corresponding list
    switch (l) {
        case DLPi:
            if (diff->_piLast == -1) {
                diff->_piFirst = index;
            }
            else {
                const int prev = diff->_piLast;
                *(cons[index]._prev) = prev;
                *(cons[prev ]._next) = index;
            }
            diff->_piLast = index;
            break;
        case DLDelta:
            if (diff->_deltaLast == -1) {
                diff->_deltaFirst = index;
            }
            else {
                const int prev = diff->_deltaLast;
                *(cons[index]._prev) = prev;
                *(cons[prev ]._next) = index;
            }
            diff->_deltaLast = index;
            break;
        case DLSigma:
            if (diff->_sigmaLast == -1) {
                diff->_sigmaFirst = index;
            }
            else {
                const int prev = diff->_sigmaLast;
                *(cons[index]._prev) = prev;
                *(cons[prev ]._next) = index;
            }
            diff->_sigmaLast = index;
            break;
        case DLLambda:
            if (diff->_lambdaLast == -1) {
                diff->_lambdaFirst = index;
            }
            else {
                const int prev = diff->_lambdaLast;
                *(cons[index]._prev) = prev;
                *(cons[prev ]._next) = index;
            }
            diff->_lambdaLast = index;
            break;
    }
    // Updating the label
    if (*(cons[index]._label) != l) {
        *(cons[index]._label) = l;
    }

    // Updating the number of constraints in 'diff->_cons0._cons'
    diff->_cons0._size = index + 1;
    
    DLMSG("Leaving addConstraint\n");

    return index;
}


/*******************************************************************************
 Node operations
 ******************************************************************************/

static void resizeNodeContainer(DifferenceLogic * diff)
{
    printf("ResizeNodeContainer\n");
    DLNode          * newNodes = NULL;
    DLEdgeContainer * newSucc  = NULL;
    DLEdgeContainer * newPred  = NULL;
    
    int newCap = diff->_cap + DLARRAYINCR;
    
    if (diff->_cap == 0) {
        newNodes = (DLNode *)          malloc(newCap * sizeof(DLNode         ));
        newSucc  = (DLEdgeContainer *) malloc(newCap * sizeof(DLEdgeContainer));
        newPred  = (DLEdgeContainer *) malloc(newCap * sizeof(DLEdgeContainer));
    }
    else {
        newNodes = (DLNode *)          realloc(diff->_nodes0, newCap * sizeof(DLNode         ));
        newSucc  = (DLEdgeContainer *) realloc(diff->_succ0,  newCap * sizeof(DLEdgeContainer));
        newPred  = (DLEdgeContainer *) realloc(diff->_pred0,  newCap * sizeof(DLEdgeContainer));
    }
    
    if (newNodes == NULL || newSucc == NULL || newPred == NULL) {
        ERROR("DifferenceLogic: Out of memory!");
    }
    
    for (int i = diff->_size; i < newCap; i++) {
        newSucc[i]._cap   = 0;
        newSucc[i]._edges = NULL;
        newSucc[i]._size  = NULL;
        newPred[i]._cap   = 0;
        newPred[i]._edges = NULL;
        newPred[i]._size  = NULL;
    }
    
    diff->_nodes0 = newNodes;
    diff->_succ0  = newSucc;
    diff->_pred0  = newPred;
    diff->_cap    = newCap;
}

static int addNode(DifferenceLogic * diff, IntVar * x)
{
    DLMSG("Add node %d (index %d)\n", x->var_id, (int) diff->_size);
    const int index = diff->_size;
    
    // Check whether the capacity is sufficient
    if (index >= diff->_cap) {
        resizeNodeContainer(diff);
    }

    assert(index < diff->_cap);

    // Initialisations
    diff->_nodes0[index]._var   = x;
    diff->_nodes0[index]._id    = x->var_id;
    diff->_nodes0[index]._index = index;
    diff->_nodes0[index]._pi    = 0;
    
    // Subscript variable
    if (!(diff->_nodes0[index]._var->isFixed())) {
        diff->_nodes0[index]._var->attach(diff, index, EVENT_L); // Lower bound change
        diff->_nodes0[index]._var->attach(diff, index, EVENT_U); // Upper bound change
        DLMSG("Add subscription for x (%d)\n", x->var_id);
    }
    
    // Updating the size
    diff->_size = index + 1;
    
    return index;
}

static int getNodeIndex(DifferenceLogic * diff, IntVar * x)
{
    DLMSG("Get node index %d\n", x->var_id);
    int i = 0;
    const int idX = x->var_id;
    // Search whether the node 'x' exists in the graph
    // TODO Building a Hash table
    for (i = 0; i < diff->_size; i++) {
        if (diff->_nodes0[i]._id == idX) {
            return i;
        }
    }
    // Node 'x' does not exist in the graph
    return addNode(diff, x);
}

/*******************************************************************************
 Edge operations
 ******************************************************************************/

    // Increasing the edge container
    //
static void resizeEdgeContainer(DifferenceLogic * diff, DLEdgeContainer * edgeCont)
{
    DLEdge * newEdges = NULL;
    const int cap = edgeCont->_cap;
    int newCap = cap + DLARRAYINCR;

    assert(newCap > cap);
    
    if (cap > 0) {
        assert(edgeCont->_size != NULL);
        newEdges = (DLEdge *) realloc(edgeCont->_edges, newCap * sizeof(DLEdge));
    }
    else {
        assert(cap == 0);
        assert(edgeCont->_size  == NULL);
        assert(edgeCont->_edges == NULL);
        newEdges = (DLEdge *) malloc(newCap * sizeof(DLEdge));
        edgeCont->_size = new Tint(0);
    }
    
    if (newEdges == NULL || edgeCont->_size == NULL) {
        ERROR("DifferenceLogic: Out of memory!");
    }
    
    for (int i = cap; i < newCap; i++) {
        newEdges[i]._node   = NULL;
        newEdges[i]._weight = NULL;
        newEdges[i]._consId = NULL;
    }
    
    edgeCont->_edges = newEdges;
    edgeCont->_cap   = newCap;
    
}


    // Adding a backtrackable edge
    //
static void addEdgeAux(DifferenceLogic * diff, DLEdgeContainer * x_cont, const int x, const int y, const int d, const int id)
{
    // Check whether there already exists an edge (x,y,d') with d < d'
    const int indexEdge = getEdgeAux(x_cont, y);
    if (indexEdge >= 0) {
        if (*(x_cont->_edges[indexEdge]._weight) > d) {
            *(x_cont->_edges[indexEdge]._weight) = d;
            *(x_cont->_edges[indexEdge]._consId) = id;
        }
        return ;
    }
    
    // Check whether the array of edges must be increased
    if (x_cont->_cap == 0 || x_cont->_cap <= *(x_cont->_size)) {
        resizeEdgeContainer(diff, x_cont);
    }
    
    // Adding the edge
    int index = *(x_cont->_size);
    x_cont->_edges[index]._node = &diff->_nodes0[y];
    if (x_cont->_edges[index]._weight == NULL) {
        assert(x_cont->_edges[index]._consId == NULL);
        x_cont->_edges[index]._weight = (Tint *) malloc(sizeof(Tint));
        x_cont->_edges[index]._consId = (Tint *) malloc(sizeof(Tint));
        if (x_cont->_edges[index]._weight == NULL || x_cont->_edges[index]._consId == NULL) {
            ERROR("DifferenceLogic: Out of memory!");
        }
        *(x_cont->_edges[index]._weight) = d;
        *(x_cont->_edges[index]._consId) = id;
    }
    else {
        *(x_cont->_edges[index]._weight) = d;
        *(x_cont->_edges[index]._consId) = id;
    }
    
    // Updating the size
    *(x_cont->_size) = ++index;
}

static void addEdge(DifferenceLogic * diff, const int x, const int y, const int d, const int id)
{
    //DLEdgeContainer x_cont = diff->_succ0[x];
    // Adding edge to the successor list
    addEdgeAux(diff, &(diff->_succ0[x]), x, y, d, id);
    // Adding edge to the predecessor list
    addEdgeAux(diff, &(diff->_pred0[y]), y, x, d, id);
}

static int getEdge(DifferenceLogic * diff, const int x, const int y)
{
    return getEdgeAux(&(diff->_succ0[x]), y);
}

static int getEdgeAux(DLEdgeContainer * x_cont, const int y)
{
    if (x_cont->_cap == 0) return -1;
    const int size = *(x_cont->_size);
    for (int i = 0; i < size; i++) {
        const int index  = x_cont->_edges[i]._node->_index;
        if (index == y) return i;
    }
    return -1;
}

/*******************************************************************************
 Consistency Checks
 ******************************************************************************/

static void analyse_inconsistency(DifferenceLogic * diff, vec<Lit> & expl, const int * branching, const int * prev_node, const int x, const int y);
static bool checkReducedCosts(DifferenceLogic * diff);
static bool checkSuccessors(DifferenceLogic * diff);
static bool checkPredecessors(DifferenceLogic * diff);
static void testGraph(DifferenceLogic * diff);

static bool doCottonMaler(DifferenceLogic * diff, const int x, const int y, const int d, const int id)
{
    DLMSG("Entering doCottonMaler\n");

    const int size = diff->_size;
    // Pre-conditions
    //  - Nodes x and y are already inserted in the graph
    assert(0 <= x && x < size);
    assert(0 <= y && y < size);
    
    int * gamma     = NULL;
    int * pi_new    = NULL;
    int * backtrace = NULL;
    int * prev_node = NULL;

    int gamma_y = diff->_nodes0[x]._pi + d - diff->_nodes0[y]._pi;

    if (gamma_y < 0) {

#if DLUSEBINPRIOQUEUE
        DLBinPrioQueue * queue = newBinPrioQueue(size);
#endif
        // Memory allocations
        gamma     = (int *) alloca(size * sizeof(int));
        pi_new    = (int *) alloca(size * sizeof(int));
        backtrace = (int *) alloca(size * sizeof(int));
        prev_node = (int *) alloca(size * sizeof(int));
        
        // Check whether memory allocation was successful
        if (gamma == NULL || pi_new == NULL || backtrace == NULL || prev_node == NULL) {
            ERROR("DifferenceLogic: Out of memory");
        }
        
        // Initialisations
        for (int i = 0; i < size; i++) {
            gamma [i]    = 0;
            pi_new[i]    = diff->_nodes0[i]._pi;
            backtrace[i] = INT_MIN;;
            prev_node[i] = INT_MIN;;
        }
        gamma[y] = gamma_y;
        backtrace[y] = id;
        prev_node[y] = x;
        int s = y;

#if DLUSEBINPRIOQUEUE
        insertItemInBinPrioQueue(queue, y, gamma[y]);

        while (!isEmptyBinPrioQueue(queue) && gamma[x] == 0) {
            s = popBinPrioQueue(queue);
#else
        while (gamma[s] < 0 && gamma[x] == 0) {
#endif
            //DLMSG("\tnode %d (%d)\n", s, diff->_nodes0[s]._id);

            // Storing new values
            pi_new[s] = diff->_nodes0[s]._pi + gamma[s];
            gamma[s] = 0;
            
            // Iterating over all successors
            if (diff->_succ0[s]._cap > 0) {
                for (int tt = 0; tt < *(diff->_succ0[s]._size); tt++) {
                    const int t = diff->_succ0[s]._edges[tt]._node->_index;
                    if (pi_new[t] == diff->_nodes0[t]._pi) {
                        const int weight = *(diff->_succ0[s]._edges[tt]._weight);
                        const int gamma_t = pi_new[s] + weight - pi_new[t];
                        if (gamma[t] > gamma_t) {
                            backtrace[t] = *(diff->_succ0[s]._edges[tt]._consId);
                            prev_node[t] = s;
#if DLUSEBINPRIOQUEUE
                            if (gamma[t] >= 0) {
                                // Node 't' is not in the queue
                                insertItemInBinPrioQueue(queue, t, gamma_t);
                            } else {
                                // Node 't' is in the queue
                                decreaseKeyInBinPrioQueue(queue, t, gamma_t);
                            }
#endif
                            gamma[t] = gamma_t;
                        }
                    }
                }
            }
            
#if DLUSEBINPRIOQUEUE == 0
            // Selection of the node with the minimal gamma value
            s = 0;
            for (int i = 1; i < size; i++) {
                if (gamma[i] < gamma[s]) s = i;
            }
#endif
        }
        // End of while loop
#if DLUSEBINPRIOQUEUE
        deleteBinPrioQueue(queue);
#endif
        
        // Check consistency
        if (gamma[x] < 0) {
            vec<Lit> expl;
            if (so.lazy) {
                analyse_inconsistency(diff, expl, backtrace, prev_node, x, y);
            }
            resetIntContainers(diff);
            // Submitting of the conflict explanation
            submit_conflict_explanation(expl);
            return false;
        }
        
        // Copy pi-function
        for (int i = 0; i < size; i++) {
            diff->_nodes0[i]._pi = pi_new[i];
        }
    }
    
    // Add edge temporarily
    addEdge(diff, x, y, d, id);
    
    // Add nodes for bounds propagation
    diff->queueChangeLB(x);
    diff->queueChangeUB(y);

    assert(checkReducedCosts(diff));
    assert(checkSuccessors(diff));
    assert(checkPredecessors(diff));
    //testGraph(diff);
    
    DLMSG("Leaving doCottonMaler\n");

    return true;
}

static void analyse_update_lb(DifferenceLogic * diff, vec<Lit> & expl, const int x, const int y, const int d, const int id, const int newLB) {
    assert(x >= 0 && y >= 0 && id >= 0);
    const BoolView * b = diff->_cons0._cons[id]._b;
    switch (diff->_cons0._cons[id]._type) {
    case DLConsHalf:
        assert(b->isTrue());
    case DLConsReif:
        assert(b->isFixed());
        expl.push(b->getValLit());
        break;
    case DLConsPure:
        break;
    }
    expl.push(getNegGeqLit(diff->_nodes0[x]._var, newLB + d));
}

static void analyse_update_ub(DifferenceLogic * diff, vec<Lit> & expl, const int x, const int y, const int d, const int id, const int newUB) {
    assert(x >= 0 && y >= 0 && id >= 0);
    const BoolView * b = diff->_cons0._cons[id]._b;
    switch (diff->_cons0._cons[id]._type) {
    case DLConsHalf:
        assert(b->isTrue());
    case DLConsReif:
        assert(b->isFixed());
        expl.push(b->getValLit());
        break;
    case DLConsPure:
        break;
    }
    expl.push(getNegLeqLit(diff->_nodes0[y]._var, newUB - d));
}

static void analyse_inconsistency(DifferenceLogic * diff, vec<Lit> & expl, const int * backtrace, const int * prev_node, const int x, const int y) {
    int s = x;
    do {
        assert(s >= 0);
        const int consId = backtrace[s];
        assert(consId >= 0);
        switch (diff->_cons0._cons[consId]._type) {
        case DLConsHalf:
            assert(diff->_cons0._cons[consId]._b->isTrue());
        case DLConsReif:
            assert(diff->_cons0._cons[consId]._b->isFixed());
            expl.push(diff->_cons0._cons[consId]._b->getValLit());
            break;
        case DLConsPure:
            break;
        }
        s = prev_node[s];
    } while (s != x);
}

static void analyse_implication(DifferenceLogic * diff, vec<Lit> & expl, const int * backtrace, const int * prev_node, const int x) {
    int s = x;
    do {
        assert(s >= 0);
        const int consId = backtrace[s];
        assert(consId >= 0);
        switch (diff->_cons0._cons[consId]._type) {
        case DLConsHalf:
            assert(diff->_cons0._cons[consId]._b->isTrue());
        case DLConsReif:
            assert(diff->_cons0._cons[consId]._b->isFixed());
            expl.push(diff->_cons0._cons[consId]._b->getValLit());
            break;
        case DLConsPure:
            break;
        }
        s = prev_node[s];
    } while (s >= 0);
}

/*******************************************************************************
 Check for Implications
 ******************************************************************************/

static void labelLambdaConsAsSigma(DifferenceLogic * diff, const int indexCons)
{
    assert(*(diff->_cons0._cons[indexCons]._label) == DLLambda);
    DLMSG("Constraint %d: LAMBDA -> SIGMA\n", indexCons);
    // Labelled constraint as assigned and implied
    const int prev = *(diff->_cons0._cons[indexCons]._prev);
    const int next = *(diff->_cons0._cons[indexCons]._next);
    DLMSG("\tLAMBDA: prev %d; next %d;\n", prev, next);

    // Updating the reference of the previous item
    if (prev >= 0) {
        *(diff->_cons0._cons[prev]._next) = next;
    }
    else {
        diff->_lambdaFirst = next;
    }

    // Updating the reference of the next item
    if (next >= 0) {
        *(diff->_cons0._cons[next]._prev) = prev;
    }
    else {
        diff->_lambdaLast = prev;
    }
    
    // Attaching the constraint to the SIGMA list
    const int last = diff->_sigmaLast;
    if (last >= 0) {
        *(diff->_cons0._cons[last]._next) = indexCons;
    }
    else {
        diff->_sigmaFirst = indexCons;
    }
    diff->_sigmaLast  = indexCons;

    *(diff->_cons0._cons[indexCons]._prev ) = last;
    *(diff->_cons0._cons[indexCons]._next ) = -1;
    *(diff->_cons0._cons[indexCons]._label) = DLSigma;
}

static void labelSigmaConsAsPi(DifferenceLogic * diff, const int indexCons)
{
    assert(*(diff->_cons0._cons[indexCons]._label) == DLSigma);
    DLMSG("Constraint %d: SIGMA -> PI\n", indexCons);
    // Labelled constraint as assigned and implied
    const int prev = *(diff->_cons0._cons[indexCons]._prev);
    const int next = *(diff->_cons0._cons[indexCons]._next);
    DLMSG("\tprev %d; next %d;\n", prev, next);

    // Updating the reference of the previous item
    if (prev >= 0) {
        *(diff->_cons0._cons[prev]._next) = next;
    }
    else {
        diff->_sigmaFirst = next;
    }

    // Updating the reference of the next item
    if (next >= 0) {
        *(diff->_cons0._cons[next]._prev) = prev;
    }
    else {
        diff->_sigmaLast = prev;
    }
    
    // Attaching the constraint to the PI list
    const int last = diff->_piLast;
    if (last >= 0) {
        *(diff->_cons0._cons[last]._next) = indexCons;
    }
    else {
        diff->_piFirst = indexCons;
    }
    diff->_piLast  = indexCons;

    *(diff->_cons0._cons[indexCons]._prev ) = last;
    *(diff->_cons0._cons[indexCons]._next ) = -1;
    *(diff->_cons0._cons[indexCons]._label) = DLPi;
}

static void labelSigmaLambdaConsAsDelta(DifferenceLogic * diff, const int indexCons)
{
    assert(
        *(diff->_cons0._cons[indexCons]._label) == DLSigma ||
        *(diff->_cons0._cons[indexCons]._label) == DLLambda
    );
    if (*(diff->_cons0._cons[indexCons]._label) == DLSigma)
        DLMSG("Constraint %d: SIGMA -> DELTA\n", indexCons);
    else
        DLMSG("Constraint %d: LAMBDA -> DELTA\n", indexCons);
    // Labelled constraint as assigned and implied
    const int prev = *(diff->_cons0._cons[indexCons]._prev);
    const int next = *(diff->_cons0._cons[indexCons]._next);
    const int intLabel = *(diff->_cons0._cons[indexCons]._label);
    const DLConsLabel label = (DLConsLabel) intLabel;
    
    // Updating the reference of the previous item
    if (prev >= 0) {
        *(diff->_cons0._cons[prev]._next) = next;
    }
    else if (label == DLSigma) {
        diff->_sigmaFirst = next;
    }
    else if (label == DLLambda) {
        diff->_lambdaFirst = next;
    }
    
    // Updating the reference of the next item
    if (next >= 0) {
        *(diff->_cons0._cons[next]._prev) = prev;
    }
    else if (label == DLSigma) {
        diff->_sigmaLast = prev;
    }
    else if (label == DLLambda) {
        diff->_lambdaLast = prev;
    }
    
    // Attaching the constraint to the assigned and implied list
    const int last = diff->_deltaLast;
    if (last >= 0) {
        *(diff->_cons0._cons[last]._next) = indexCons;
    }
    else {
        diff->_deltaFirst = indexCons;
    }
    diff->_deltaLast  = indexCons;

    *(diff->_cons0._cons[indexCons]._prev ) = last;
    *(diff->_cons0._cons[indexCons]._next ) =   -1;
    *(diff->_cons0._cons[indexCons]._label) = DLDelta;
}

static bool checkImplication(
    DifferenceLogic * diff, const int * distX, const int * backtraceX, const int * prevNodeX, 
    const int * distY, const int * backtraceY, const int * prevNodeY, const int indexConsXY, 
    const int indexX, const int indexY, const int dXY, int indexCons
)
{
    DLMSG("Entering checkImplication\n");
    assert(indexConsXY >= 0);

    // Iterating over undecided difference logic constraints
    // reachable from the constraint at the index indexCons
    while (indexCons >= 0) {
        const int indexU    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._x);
        const int indexV    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._y);
        const int dUV       = diff->_cons0._cons[indexCons]._d;
        const int rcD_xy    = diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi;
        const int rcD_uv    = diff->_nodes0[indexU]._pi - diff->_nodes0[indexV]._pi;
        const int indexConsNext = *(diff->_cons0._cons[indexCons]._next);
        const DLConsType  type = diff->_cons0._cons[indexCons]._type;
        BoolView * b = diff->_cons0._cons[indexCons]._b;
        
        assert(*(diff->_cons0._cons[indexCons]._label) == DLLambda);
        assert(type == DLConsReif || type == DLConsHalf);
        assert(!b->isFixed());

        DLMSG("\tCHECK Constraint %d: b (%p) (<)-> x(%d) - y(%d) <= %d\n", indexCons, b, indexU, indexV, dUV);
        DLMSG("\tCHECK(implied): distX[%d] %d + dXY %d + rcD_xy %d + distY[%d] %d - rcD_uv %d <= dUV %d\n", indexU, distX[indexU], dXY, rcD_xy, indexV, distY[indexV], rcD_uv, dUV);

        // Check length of paths:
        // 1. u ~~~> x --> y ~~~> v  <=  dUV     (constraint is implied    )
        // 2. v ~~~> x --> y ~~~> u  <= -dUV - 1 (constraint is not implied)
        // NOTE the distance in distX and distY are the reduced cost ones, but
        // not dXY!
        if (distX[indexU] < INT_MAX && distY[indexV] < INT_MAX
            && distX[indexU] + dXY + rcD_xy + distY[indexV] - rcD_uv <= dUV) {
            // Constraint (u - v <= dUV) is implied
            // Assign constraint
            if (diff->_cons0._cons[indexCons]._type == DLConsReif) {
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    // Explain constraint x --> y
                    switch (diff->_cons0._cons[indexConsXY]._type) {
                    case DLConsHalf:
                        assert(diff->_cons0._cons[indexConsXY]._b->isTrue());
                    case DLConsReif:
                        assert(diff->_cons0._cons[indexConsXY]._b->isFixed());
                        expl.push(diff->_cons0._cons[indexConsXY]._b->getValLit());
                        break;
                    case DLConsPure:
                        break;
                    }
                    // Explain constraints on the path u ~~~> x
                    analyse_implication(diff, expl, backtraceX, prevNodeX, indexU);
                    // Explain constraints on the path y ~~~> v
                    analyse_implication(diff, expl, backtraceY, prevNodeY, indexV);
                    // Create the reason for the update
                    reason = get_reason_for_update(expl);
                }
                DLMSG("\tConstraint b %p (<)-> x(%d) - y(%d) <= %d is implied\n", b, indexU, indexV, dUV);
                DLMSG("\tSet b %p to TRUE\n", b);
                DLMSG("\t\tdistX[%d] %d; distY[%d] %d; dXY %d; rcD_xy %d; rcD_uv %d; dUV %d\n", indexU, distX[indexU], indexV, distY[indexV], dXY, rcD_xy, rcD_uv, dUV);
                if (! b->setVal(true, reason)) {
                    resetIntContainers(diff);
                    return false;
                }
            }
            // Labelled constraint as assigned and implied
            labelSigmaLambdaConsAsDelta(diff, indexCons);
        }
        else if (distX[indexV] < INT_MAX && distY[indexU] < INT_MAX
                 && distX[indexV] + dXY + rcD_xy + distY[indexU] + rcD_uv <= -dUV -1) {
                DLMSG("\tConstraint b %p (<)-> x(%d) - y(%d) <= %d is NOT implied\n", b, indexU, indexV, dUV);
            // Negated constraint ( v - u <= -dUV - 1) is implied
            // Assign constraint
            if (diff->_cons0._cons[indexCons]._type == DLConsReif
                || diff->_cons0._cons[indexCons]._type == DLConsHalf) {
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    // Explain constraint x --> y
                    switch (diff->_cons0._cons[indexConsXY]._type) {
                    case DLConsHalf:
                        assert(diff->_cons0._cons[indexConsXY]._b->isTrue());
                    case DLConsReif:
                        assert(diff->_cons0._cons[indexConsXY]._b->isFixed());
                        expl.push(diff->_cons0._cons[indexConsXY]._b->getValLit());
                        break;
                    case DLConsPure:
                        break;
                    }
                    // Explain constraints on the path v ~~~> x
                    analyse_implication(diff, expl, backtraceX, prevNodeX, indexV);
                    // Explain constraints on the path y ~~~> u
                    analyse_implication(diff, expl, backtraceY, prevNodeY, indexU);
                    // Create the reason for the update
                    reason = get_reason_for_update(expl);
                }
                DLMSG("\tConstraint b %p (<)-> x(%d) - y(%d) <= %d is NOT implied\n", b, indexU, indexV, dUV);
                DLMSG("\tSet b %p to FALSE\n", b);
                if (! b->setVal(false, reason)) {
                    resetIntContainers(diff);
                    return false;
                }
            }
            // Labelled constraint as assigned and implied
            labelSigmaLambdaConsAsDelta(diff, indexCons);
        }
        indexCons = indexConsNext;
    }
    DLMSG("Leaving checkImplication\n");

    return true;
}

static inline bool isConsImpliedByBounds(const IntVar * x, const IntVar * y, const int d)
{
    if (x->getMax() - y->getMin() <= d || y->getMax() - x->getMin() < -d) {
        // 'x - y <= d' or 'not(x - y <= d)' is implied
        return true;
    }
    return false;
}

static bool checkImplicationByBounds(DifferenceLogic * diff, int indexCons)
{
    DLMSG("Entering checkImplicationByBounds\n");

    while (indexCons >= 0) {
        BoolView          * b    = diff->_cons0._cons[indexCons]._b;
        IntVar            * x    = diff->_cons0._cons[indexCons]._x;
        IntVar            * y    = diff->_cons0._cons[indexCons]._y;
        const int           d    = diff->_cons0._cons[indexCons]._d;
        const DLConsType    t    = diff->_cons0._cons[indexCons]._type;
        const int           intL = *(diff->_cons0._cons[indexCons]._label);
        const DLConsLabel   l    = (DLConsLabel) intL;

        const int indexConsNext = *(diff->_cons0._cons[indexCons]._next);
        
        assert(l == DLLambda || l == DLSigma);
        
        if (t == DLConsReif)
            DLMSG("\tindexCons %d: b %p <-> x[%d, %d] - y[%d, %d]) <= %d\n", indexCons, b, x->getMin(), x->getMax(), y->getMin(), y->getMax(), d);
        else if (t == DLConsHalf)
            DLMSG("\tindexCons %d: b %p -> x[%d, %d] - y[%d, %d]) <= %d\n", indexCons, b, x->getMin(), x->getMax(), y->getMin(), y->getMax(), d);
        else
            DLMSG("\tindexCons %d: x[%d, %d] - y[%d, %d]) <= %d\n", indexCons, x->getMin(), x->getMax(), y->getMin(), y->getMax(), d);
        assert(t == DLConsPure || !b->isFixed());

        if (x->getMax() - y->getMin() <= d) {
            // 'x - y <= d' is implied
            DLMSG("\t\tImplied\n");
            if (t == DLConsReif) {
                // 'b <->  x - y <= d'
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    // Generate explanation
                    analyse_implication_by_bounds(diff, x, y, d, expl);
                    reason = get_reason_for_update(expl);
                }
                if (! b->setVal(true, reason)) {
                    resetIntContainers(diff);
                    return false;
                }
            }
            // Label constraint to 'DLDelta'
            labelSigmaLambdaConsAsDelta(diff, indexCons);
            //if (l == DLLambda)
            //    labelLambdaConsAsSigma(diff, indexCons);
        }
        else if (x->getMin() - y->getMax() > d) {
            // 'not(x - y <= d)' is implied
            assert(t != DLConsPure);
            DLMSG("\t\tNot implied: fixed %d; true %d; false %d\n", b->isFixed(), b->isTrue(), b->isFalse());
            // 'b <->  x - y <= d' or ' b ->  x - y <= d'
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                // Generate explanation
                analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                reason = get_reason_for_update(expl);
            }
            if (! b->setVal(false, reason)) {
                resetIntContainers(diff);
                return false;
            }
            DLMSG("\t\tNot implied: fixed %d; true %d; false %d\n", b->isFixed(), b->isTrue(), b->isFalse());
            // Label constraint to 'DLDelta'
            // XXX Label constraint as 'DLSigma', because the consequences aren't 
            // calculated yet?
            labelSigmaLambdaConsAsDelta(diff, indexCons);
            //if (l == DLLambda)
            //    labelLambdaConsAsSigma(diff, indexCons);
        }
        indexCons = indexConsNext;
    }
    DLMSG("Leaving checkImplicationByBounds\n");
    
    return true;
}

/*******************************************************************************
 Shortest Path Calculations
 ******************************************************************************/


static void doDijkstraWithReducedCost(DifferenceLogic * diff, DLEdgeContainer * cont, int * dist, int * backtrace, int * prev_node, const int source, const int consId, const bool fwd)
{
    DLMSG("Entering doDijkstraWithReducedCost\n");
    const int size = diff->_size;
    int x = source;
    bool visited[size];
#if DLUSEBINPRIOQUEUE
    DLBinPrioQueue * queue = newBinPrioQueue(max(size >> 3, 16));
#endif
    
    for (int i = 0; i < size; i++) {
        dist   [i] = INT_MAX;
        visited[i] = false;
        backtrace[i] = INT_MIN;
        prev_node[i] = INT_MIN;
    }

    // Distance to the source is zero
    dist[source] = 0;
    backtrace[source] = consId;
#if DLUSEBINPRIOQUEUE
    insertItemInBinPrioQueue(queue, source, 0);
    
    while (!isEmptyBinPrioQueue(queue)) {
        x = popBinPrioQueue(queue);
#else
    while (x >= 0) {
#endif
        //DLMSG("\tcurrent node %d (%d); dist %d\n", x, diff->_nodes0[x]._id, dist[x]);
        const int pi_x = diff->_nodes0[x]._pi;
        // Mark 'x' as visited
        visited[x] = true;
        
        // Update the distances to the neighbours of 'x'
        if (cont[x]._cap > 0) {
            for (int ii = 0; ii < *(cont[x]._size); ii++) {
                const int i    = cont[x]._edges[ii]._node->_index;
                const int pi_i = cont[x]._edges[ii]._node->_pi;
                const int d_xi = *(cont[x]._edges[ii]._weight);
                const int rcD  = (fwd ? pi_x - pi_i : pi_i - pi_x) + d_xi;
                const int dist_i = dist[x] + rcD;
                //DLMSG("\t\tneighbour %d: dist[i] %d; dist_i %d\n", i, dist[i], dist_i);
                //DLMSG("\t\t\tpi_x %d; pi_i %d; d_xi %d; rcD %d;\n", pi_x, pi_i, d_xi, rcD);
                //if (rcD < 0) printGraph(diff);
                assert(rcD >= 0);
                if (dist[i] > dist_i) {
                    prev_node[i] = x;
                    backtrace[i] = *(cont[x]._edges[ii]._consId);
#if DLUSEBINPRIOQUEUE
                    if (dist[i] == INT_MAX) {
                        insertItemInBinPrioQueue(queue, i, dist_i);
                    }
                    else {
                        decreaseKeyInBinPrioQueue(queue, i, dist_i);
                    }
#endif
                    dist[i] = dist_i;
                }
            }
        }

#if DLUSEBINPRIOQUEUE == 0
        // Retrieving the next node
        x = -1;
        int smallest = INT_MAX;
        for (int i = 0; i < size; i++) {
            if (dist[i] < smallest && visited[i] == false) {
                x = i;
            }
        }
#endif
    }

#if DLUSEBINPRIOQUEUE
    deleteBinPrioQueue(queue);
#endif
    
    DLMSG("Leaving doDijkstraWithReducedCost\n");
}

static bool doBoundsByDijkstraWithReducedCostLB(DifferenceLogic * diff, DLEdgeContainer * cont, const int * changed, const int sizeChanged, int * dist)
{
    // Check whether a bounds propagation must be executed
    //
    if (sizeChanged <= 0) return true;
    
    DLMSG("Entering doBoundsByDijkstraWithReducedCostLB\n");

    const int size = diff->_size;
    int  x        = -1;
    int  pi_v0    = INT_MIN;
    bool visited[size];
    int  backtrace[size];
    int  prev_node[size];
#if DLUSEBINPRIOQUEUE
    DLBinPrioQueue * queue = newBinPrioQueue(min(sizeChanged << 1, size));
#endif
    
    for (int i = 0; i < size; i++) {
        dist   [i] = INT_MAX;
        visited[i] = false;
        backtrace[i] = INT_MIN;
        prev_node[i] = INT_MIN;
    }
    
    for (int ii = 0; ii < sizeChanged; ii++) {
        const int i = changed[ii];
        const int lb_i = diff->_nodes0[i]._var->getMin();
        const int pi_i = diff->_nodes0[i]._pi;
        pi_v0 = max(pi_v0, lb_i + pi_i);
        dist[i] = -pi_i - lb_i;
    }

//    printGraph(diff);
    
    for (int ii = 0; ii < sizeChanged; ii++) {
        const int i = changed[ii];
        dist[i] += pi_v0;
        assert(dist[i] >= 0);
#if DLUSEBINPRIOQUEUE
        insertItemInBinPrioQueue(queue, i, dist[i]);
#else
        if (x < 0 || dist[x] > dist[i]) x = i;
#endif
    }

#if DLUSEBINPRIOQUEUE
    while (!isEmptyBinPrioQueue(queue)) {
        x = popBinPrioQueue(queue);
#else
    while (x >= 0) {
#endif
        const int pi_x = diff->_nodes0[x]._pi;
        // Mark 'x' as visited
        visited[x] = true;

        // Calculating the new lower bound
        const int newLB = pi_v0 - pi_x - dist[x];
        assert(newLB >= diff->_nodes0[x]._var->getMin());
        
        // Updating the new lower bound
        if (newLB > diff->_nodes0[x]._var->getMin()) {
            DLMSG("New LB %d (id %d): %d -> %d\n", x, diff->_nodes0[x]._id, diff->_nodes0[x]._var->getMin(), newLB);
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                // Generation of the explanation
                const int y  = prev_node[x];
                const int id = *(cont[y]._edges[backtrace[x]]._consId);
                const int d  = *(cont[y]._edges[backtrace[x]]._weight);
                analyse_update_lb(diff, expl, y, x, d, id, newLB);
                reason = get_reason_for_update(expl);
            }
            if (!diff->_nodes0[x]._var->setMin(newLB, reason)) {
                resetIntContainers(diff);
                return false;
            }
            // If the variables has holes in the domain then it has to be queued up again
            assert(diff->_nodes0[x]._var->getMin() >= newLB);
            if (diff->_nodes0[x]._var->getMin() > newLB)
                diff->queueChangeLB(x);
        }
        
        // Propagating the new lower bound to its successors
        if (cont[x]._cap > 0) {
            for (int ii = 0; ii < *(cont[x]._size); ii++) {
                const DLNode * node_i = cont[x]._edges[ii]._node;
                const int i = node_i->_index;
                const int rcD = pi_x + *(cont[x]._edges[ii]._weight) - node_i->_pi;
                const int dist_i = dist[x] + rcD;
                const int d_v0i = pi_v0 - node_i->_var->getMin() - node_i->_pi;
                if (dist_i < d_v0i) {
                    assert(visited[i] == false);
                    // New lower bound for node 'i'
                    if (dist[i] > dist_i) {
                        backtrace[i] = ii;
                        prev_node[i] = x;
#if DLUSEBINPRIOQUEUE
                        if (dist[i] == INT_MAX) {
                            insertItemInBinPrioQueue(queue, i, dist_i);
                        }
                        else {
                            decreaseKeyInBinPrioQueue(queue, i, dist_i);
                        }
#endif
                        dist[i] = dist_i;
                    }
                }
            }
        }
    
#if DLUSEBINPRIOQUEUE == 0
        // Retrieving the next node
        x = -1;
        for (int i = 0; i < size; i++) {
            if (visited[i] == false && ((x < 0 && dist[i] < INT_MAX) || dist[i] < dist[x])) {
                x = i;
            }
        }
#endif
    }

#if DLUSEBINPRIOQUEUE
    deleteBinPrioQueue(queue);
#endif
    DLMSG("Leaving doBoundsByDijkstraWithReducedCostLB\n");

    return true;
}

static bool doBoundsByDijkstraWithReducedCostUB(DifferenceLogic * diff, DLEdgeContainer * cont, const int * changed, const int sizeChanged, int * dist)
{
    // Check whether a bounds propagation must be executed
    //
    if (sizeChanged <= 0) return true;
    
    DLMSG("Entering doBoundsByDijkstraWithReducedCostUB (size %d)\n", sizeChanged);

    const int size = diff->_size;
    int  x        = -1;
    int  pi_v0    = INT_MAX;
    bool visited[size];
    int  backtrace[size];
    int  prev_node[size];

#if DLUSEBINPRIOQUEUE
    DLBinPrioQueue * queue = newBinPrioQueue(min(sizeChanged << 1, size));
#endif
    
    for (int i = 0; i < size; i++) {
        dist   [i] = INT_MAX;
        visited[i] = false;
        backtrace[i] = INT_MIN;
        prev_node[i] = INT_MIN;
    }
    
    for (int ii = 0; ii < sizeChanged; ii++) {
        const int i = changed[ii];
        const int ub_i = diff->_nodes0[i]._var->getMax();
        const int pi_i = diff->_nodes0[i]._pi;
        pi_v0 = min(pi_v0, ub_i + pi_i);
        assert(0 <= i && i < size);
        dist[i] = pi_i + ub_i;
        DLMSG("\tUB changed: %2d (id %2d)\n", i, diff->_nodes0[i]._id);
    }
    
    for (int ii = 0; ii < sizeChanged; ii++) {
        const int i = changed[ii];
        dist[i] -= pi_v0;
        assert(dist[i] >= 0);
#if DLUSEBINPRIOQUEUE
        insertItemInBinPrioQueue(queue, i, dist[i]);
#else
        if (x < 0 || dist[x] > dist[i]) x = i;
#endif
    }
    
    //printGraph(diff);
#if DLUSEBINPRIOQUEUE
    while (!isEmptyBinPrioQueue(queue)) {
        x = popBinPrioQueue(queue);
#else
    while (x >= 0) {
#endif
        assert(x >= 0 && x < size);

        const int pi_x = diff->_nodes0[x]._pi;
        // Mark 'x' as visited
        visited[x] = true;
        
        // Calculating the new bound
        const int newUB = dist[x] + pi_v0 - pi_x;
        assert(newUB <= diff->_nodes0[x]._var->getMax());
        DLMSG("\tVisit %2d (id %2d): newUB %d <= %d oldUB\n", x, diff->_nodes0[x]._id, newUB, diff->_nodes0[x]._var->getMax());
        
        // Updating the new bound
        if (newUB < diff->_nodes0[x]._var->getMax()) {
            DLMSG("New UB %2d (id %2d): %d -> %d\n", x, diff->_nodes0[x]._id, diff->_nodes0[x]._var->getMax(), newUB);
            //if (diff->_nodes0[x]._id == 30) {
            //    
            //    for (int z = diff->_nodes0[x]._var->getMin(); z <= diff->_nodes0[x]._var->getMax(); z++) {
            //        fprintf(stderr, " (%d: %d), ", z, diff->_nodes0[x]._var->indomain(z));
            //    }
            //    fprintf(stderr, "\n");
            //}
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                // Generation of the explanation
                const int y  = prev_node[x];
                assert(0 <= y && y < size);
                assert(0 <= backtrace[x] && backtrace[x] < *(cont[y]._size));
                const int id = *(cont[y]._edges[backtrace[x]]._consId);
                const int d  = *(cont[y]._edges[backtrace[x]]._weight);
                analyse_update_ub(diff, expl, x, y, d, id, newUB);
                reason = get_reason_for_update(expl);
            }
            if (!diff->_nodes0[x]._var->setMax(newUB, reason)) {
                resetIntContainers(diff);
                return false;
            }
            // If the variables has holes in the domain then it has to be queued up again
            assert(diff->_nodes0[x]._var->getMax() <= newUB);
            if (diff->_nodes0[x]._var->getMax() < newUB)
                diff->queueChangeUB(x);
            DLMSG("\t-> max %d\n", diff->_nodes0[x]._var->getMax());
        }
        
        // Propagating the new bound to its successors
        if (cont[x]._cap > 0) {
            for (int ii = 0; ii < *(cont[x]._size); ii++) {
                const DLNode * node_i = cont[x]._edges[ii]._node;
                const int i = node_i->_index;
                const int rcD = node_i->_pi + *(cont[x]._edges[ii]._weight) - pi_x;
                const int dist_i = dist[x] + rcD;
                const int d_iv0 = node_i->_pi + node_i->_var->getMax() - pi_v0;
                DLMSG("\tNeighbour: %2d (id %2d)\n", i, node_i->_id);
                assert(0 <= i && i < size);
                if (dist_i < d_iv0) {
                    DLMSG("\t\t-> queue up\n");
                    assert(visited[i] == false);
                    // New bound for node 'i'
                    if (dist[i] > dist_i) {
                        backtrace[i] = ii;
                        prev_node[i] = x;
#if DLUSEBINPRIOQUEUE
                        if (dist[i] == INT_MAX) {
                            insertItemInBinPrioQueue(queue, i, dist_i);
                        }
                        else {
                            decreaseKeyInBinPrioQueue(queue, i, dist_i);
                        }
#endif
                        dist[i] = dist_i;
                    }
                }
            }
        }
        
#if DLUSEBINPRIOQUEUE == 0
        // Retrieving the next node
        x = -1;
        for (int i = 0; i < size; i++) {
            if (visited[i] == false && ((x < 0 && dist[i] < INT_MAX) || dist[i] < dist[x])) {
                x = i;
            }
        }
#endif
    }
    
#if DLUSEBINPRIOQUEUE
    deleteBinPrioQueue(queue);
#endif
    DLMSG("Leaving doBoundsByDijkstraWithReducedCostUB\n");

    return true;
}

static bool checkSuccessors(DifferenceLogic * diff)
{
    for (int i = 0; i < diff->_size; i++) {
        if (diff->_succ0[i]._cap > 0) {
            for (int jj = 0; jj < *(diff->_succ0[i]._size); jj++) {
                const int j = diff->_succ0[i]._edges[jj]._node->_index;
                const int w = *(diff->_succ0[i]._edges[jj]._weight);
                if (diff->_pred0[j]._cap > 0) {
                    int kk = 0;
                    for (; kk < *(diff->_pred0[j]._size); kk++) {
                        const int k = diff->_pred0[j]._edges[kk]._node->_index;
                        const int z = *(diff->_pred0[j]._edges[kk]._weight);
                        if (k == i) {
                            if (w != z) {
                                fprintf(stderr, "ERROR: Weight of successor and predecessor edge are different!\n");
                                printGraph(diff);
                                return false;
                            }
                            break;
                        }
                    }
                    if (kk >= *(diff->_pred0[j]._size)) {
                        fprintf(stderr, "ERROR: No predecessor %d for successor %d\n", i, j);
                        printGraph(diff);
                        return false;
                    }
                }
                else {
                    fprintf(stderr, "ERROR: No predecessor %d for successor %d\n", i, j);
                    printGraph(diff);
                    return false;
                }
            }
        }
    }
    return true;
}

static bool checkPredecessors(DifferenceLogic * diff)
{
    for (int i = 0; i < diff->_size; i++) {
        if (diff->_pred0[i]._cap > 0) {
            for (int jj = 0; jj < *(diff->_pred0[i]._size); jj++) {
                const int j = diff->_pred0[i]._edges[jj]._node->_index;
                const int w = *(diff->_pred0[i]._edges[jj]._weight);
                if (diff->_succ0[j]._cap > 0) {
                    int kk = 0;
                    for (; kk < *(diff->_succ0[j]._size); kk++) {
                        const int k = diff->_succ0[j]._edges[kk]._node->_index;
                        const int z = *(diff->_succ0[j]._edges[kk]._weight);
                        if (k == i) {
                            if (w != z) {
                                fprintf(stderr, "ERROR: Weight of successor and predecessor edge are different!\n");
                                printGraph(diff);
                                return false;
                            }
                            break;
                        }
                    }
                    if (kk >= *(diff->_succ0[j]._size)) {
                        fprintf(stderr, "ERROR: No predecessor %d for successor %d\n", j, i);
                        printGraph(diff);
                        return false;
                    }
                }
                else {
                    fprintf(stderr, "ERROR: No predecessor %d for successor %d\n", j, i);
                    printGraph(diff);
                    return false;
                }
            }
        }
    }
    return true;
}

static bool checkReducedCosts(DifferenceLogic * diff)
{
    for (int i = 0; i < diff->_size; i++) {
        if (diff->_succ0[i]._cap > 0) {
            const int pi_i = diff->_nodes0[i]._pi;
            for (int jj = 0; jj < *(diff->_succ0[i]._size); jj++) {
                const int j = diff->_succ0[i]._edges[jj]._node->_index;
                const int w = *(diff->_succ0[i]._edges[jj]._weight);
                const int pi_j = diff->_nodes0[j]._pi;
                const int rdC = pi_i - pi_j + w;
                if (rdC < 0) {
                    fprintf(stderr, "ERROR: Reduced cost is negative for %d -(%d)-> %d\n", i, w, j);
                    printGraph(diff);
                    return false;
                }
            }
        }
    }
    return true;
}

static void testGraph(DifferenceLogic * diff)
{
    for (int i = 0; i < diff->_size; i++) {
        IntVar * x = diff->_nodes0[i]._var;
        if (diff->_succ0[i]._cap > 0) {
            for (int jj = 0; jj < *(diff->_succ0[i]._size); jj++) {
                const int j = diff->_succ0[i]._edges[jj]._node->_index;
                const int w = *(diff->_succ0[i]._edges[jj]._weight);
                IntVar * y = diff->_nodes0[j]._var;
                if (x->getMax() > y->getMax() + w) {
                    printGraph(diff);
                    printf("%d -(%d)-> %d\n", i, w, j);
                }
                assert(x->getMax() <= y->getMax() + w);
                assert(x->getMin() <= y->getMin() + w);
            }
        }
    }
}

static void printGraph(DifferenceLogic * diff)
{
    fprintf(stderr, "#### GRAPH ####\n");
    for (int i = 0; i < diff->_size; i++) {
        fprintf(stderr, "node %d (%u): pi %d; dom [%d,%d]", diff->_nodes0[i]._index, diff->_nodes0[i]._id, diff->_nodes0[i]._pi, diff->_nodes0[i]._var->getMin(), diff->_nodes0[i]._var->getMax());
        if (diff->_succ0[i]._cap > 0) {
            fprintf(stderr, " succ:");
            for (int jj = 0; jj < *(diff->_succ0[i]._size); jj++) {
                const int j = diff->_succ0[i]._edges[jj]._node->_index;
                const int w = *(diff->_succ0[i]._edges[jj]._weight);
                fprintf(stderr, " -(%d)-> %d;", w, j);
            }
        }
        if (diff->_pred0[i]._cap > 0) {
            fprintf(stderr, "pred:");
            for (int jj = 0; jj < *(diff->_pred0[i]._size); jj++) {
                const int j = diff->_pred0[i]._edges[jj]._node->_index;
                const int w = *(diff->_pred0[i]._edges[jj]._weight);
                fprintf(stderr, " <-(%d)- %d;", w, j);
            }
        }
        fprintf(stderr, "\n");
    }
}

/*******************************************************************************
 Adding queued constraints to the propagator
 ******************************************************************************/


static void analyse_implication_by_PI(DifferenceLogic * diff, const int * backtrace, const int * prev_node, const int indexX, const int indexY, vec<Lit> & expl)
{
    DLMSG("Entering analyse_implication_by_PI\n");
    int s = indexY;
    while (s != indexX) {
        DLMSG("\ts = %d\n", s);
        const int consId = backtrace[s];
        DLMSG("\tconsId = %d\n", consId);
        switch (diff->_cons0._cons[consId]._type) {
        case DLConsHalf:
            assert(diff->_cons0._cons[consId]._b->isTrue());
        case DLConsReif:
            assert(diff->_cons0._cons[consId]._b->isFixed());
            expl.push(diff->_cons0._cons[consId]._b->getValLit());
            break;
        case DLConsPure:
            break;
        }
        s = prev_node[s];
    }
    DLMSG("Leaving analyse_implication_by_PI\n");
}

    // x - y <= d is implied
    //
static inline void analyse_implication_by_bounds(DifferenceLogic * diff, IntVar * x, IntVar * y, const int d, vec<Lit> & expl)
{
    assert(x->getMax() - y->getMin() <= d);
    const int lift   = (diff->_expl_lift ? d - x->getMax() + y->getMin() : 0);
    const int lift_x = min(x->getMax0() - x->getMax(), lift / 2);
    const int lift_y = lift - lift_x;
    assert(lift >= 0);
    expl.push(getNegLeqLit(x, x->getMax() + lift_x));
    expl.push(getNegGeqLit(y, y->getMin() - lift_y));
}

    // x - y <= d
static bool addQueuedPure(DifferenceLogic * diff, IntVar * x, IntVar * y, const int d)
{
    DLMSG("Entering addQueuedPure: x(%d) - y(%d) <= %d\n", x->var_id, y->var_id, d);
    DLMSG("\tImplication by bounds\n");
    // Is x - y <= d implied by bounds?
    // XXX [AS] Commented because constraint might be not implied by PI
    //if (x->getMax() - y->getMin() <= d) 
    //    return true;
    // Is not(x - y <= d) implied by bounds?
    if (y->getMax() - x->getMin() < -d) {
        // Inconsistency detected
        vec<Lit> expl;
        if (so.lazy) {
            analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
        }
        submit_conflict_explanation(expl);
        return false;
    }

    DLMSG("\tRetrieve node index\n");
    // Is implied by PI?
    const int indexX = getNodeIndex(diff, x);
    const int indexY = getNodeIndex(diff, y);

    DLMSG("\tImplication by PI\n");
    if (diff->_succ0[indexX]._size > 0 && diff->_pred0[indexY]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'x'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexX, INT_MIN, true);
        // Is implied by PI
        if (dist[indexY] < INT_MAX && dist[indexY] + diff->_nodes0[indexY]._pi - diff->_nodes0[indexX]._pi <= d) return true;
    }
    // Is negated constraint implied by PI?
    if (diff->_succ0[indexY]._size > 0 && diff->_pred0[indexX]._size > 0) {
        DLMSG("\tsize %d\n", (int) diff->_size);
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'y'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexY, INT_MIN, true);
        if (dist[indexX] < INT_MAX && dist[indexX] + diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi < -d) {
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
            }
            submit_conflict_explanation(expl);
            return false;
        }
    }

    DLMSG("\tAdd constraints to database\n");
    // Add constraint to propagator and label it with SIGMA
    const int indexCons = addConstraint(diff, NULL, x, y, d, DLConsPure, DLSigma);

    DLMSG("\tPerform consistency check\n");
    // Check consistency and add edge to the graph
    if (! doCottonMaler(diff, indexX, indexY, d, indexCons)) return false;

    return true;
}

    // b <-> x - y <= d
static bool addQueuedReif(DifferenceLogic * diff, BoolView * b, IntVar * x, IntVar * y, const int d)
{
    // Is x - y <= d implied by bounds?
    if (x->getMax() - y->getMin() <= d) {
        if (b->isFixed()) {
            if (b->isFalse()) {
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_bounds(diff, x, y, d, expl);
                    expl.push(b->getValLit());
                }
                submit_conflict_explanation(expl);
                return false;
            }
            return true;
        } else {
            // Set b to true
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, x, y, d, expl);
                reason = get_reason_for_update(expl);
            }
            if (! b->setVal(true, reason)) return false;
            return true;
        }
    }
    // Is not(x - y <= d) implied by bounds?
    if (y->getMax() - x->getMin() < -d) {
        if (b->isFixed()) {
            if (b->isTrue()) {
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                    expl.push(b->getValLit());
                }
                submit_conflict_explanation(expl);
                return false;
            }
            return true;
        } else {
            // Set b to false
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                reason = get_reason_for_update(expl);
            }
            if (! b->setVal(false, reason)) return false;
            return true;
        }
    }
    // Is implied by PI
    const int indexX = getNodeIndex(diff, x);
    const int indexY = getNodeIndex(diff, y);

    if (diff->_succ0[indexX]._size > 0 && diff->_pred0[indexY]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'x'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexX, INT_MIN, true);
        // Is implied by PI
        if (dist[indexY] < INT_MAX && dist[indexY] + diff->_nodes0[indexY]._pi - diff->_nodes0[indexX]._pi <= d) {
            if (b->isFixed()) {
                if (b->isFalse()) {
                    vec<Lit> expl;
                    if (so.lazy) {
                        analyse_implication_by_PI(diff, backtrace, prev_node, indexX, indexY, expl);
                        expl.push(b->getValLit());
                    }
                    submit_conflict_explanation(expl);
                    return false;
                }
                return true;
            } else {
                // Set 'b' to true
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexX, indexY, expl);
                    reason = get_reason_for_update(expl);
                }
                if (! b->setVal(true, reason)) return false;
                return true;
            }
        }
    }

    // Is negated constraint implied by PI?
    if (diff->_succ0[indexY]._size > 0 && diff->_pred0[indexX]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'y'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexY, INT_MIN, true);
        if (dist[indexX] < INT_MAX && dist[indexX] + diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi < -d) {
            if (b->isFixed()) {
                if (b->isTrue()) {
                    vec<Lit> expl;
                    if (so.lazy) {
                        analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                        expl.push(b->getValLit());
                    }
                    submit_conflict_explanation(expl);
                    return false;
                }
                return true;
            } else {
                // Set 'b' to false
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                    reason = get_reason_for_update(expl);
                }
                if (! b->setVal(false, reason)) return false;
                return true;
            }
        }
    }
    
    if (b->isFixed()) {
        // Add constraint to propagator and label it with SIGMA
        const int indexCons = addConstraint(diff, b, x, y, d, DLConsReif, DLSigma);

        // Check consistency and add edge to the graph
        if (b->isTrue()) {
            if (! doCottonMaler(diff, indexX, indexY, d, indexCons)) return false;
        } else {
            if (! doCottonMaler(diff, indexY, indexX, -d - 1, indexCons)) return false;
        }
    } else {
        // Add constraint to propagator and label it with LAMBDA
        const int indexCons = addConstraint(diff, b, x, y, d, DLConsReif, DLLambda);
        // Add subscription
        b->attach(diff, diff->_cap + indexCons, EVENT_LU);
        DLMSG("Add subscription for b (%p)\n", b);
    }

    return true;
}

    // b -> x - y <= d
static bool addQueuedHalf(DifferenceLogic * diff, BoolView * b, IntVar * x, IntVar * y, const int d)
{
    if (b->isFixed() && b->isFalse()) return true;

    // Is x - y <= d implied by bounds?
    if (x->getMax() - y->getMin() <= d) {
        assert(!b->isFixed() || b->isTrue());
        return true;
    }
    // Is not(x - y <= d) implied by bounds?
    if (y->getMax() - x->getMin() < -d) {
        if (b->isFixed()) {
            assert(b->isTrue());
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                expl.push(b->getValLit());
            }
            submit_conflict_explanation(expl);
            return false;
        } else {
            // Set b to false
            Clause * reason = NULL;
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                reason = get_reason_for_update(expl);
            }
            if (! b->setVal(false, reason)) return false;
            return true;
        }
    }
    
    // Is constraint implied by PI?
    const int indexX = getNodeIndex(diff, x);
    const int indexY = getNodeIndex(diff, y);

    if (diff->_succ0[indexX]._size > 0 && diff->_pred0[indexY]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'x'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexX, INT_MIN, true);
        // Is implied by PI
        if (dist[indexY] < INT_MAX && dist[indexY] + diff->_nodes0[indexY]._pi - diff->_nodes0[indexX]._pi <= d) {
            assert(!b->isFixed() || b->isTrue());
            return true;
        }
    }

    // Is negated constraint implied by PI?
    if (diff->_succ0[indexY]._size > 0 && diff->_pred0[indexX]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'y'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexY, INT_MIN, true);
        if (dist[indexX] < INT_MAX && dist[indexX] + diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi < -d) {
            if (b->isFixed()) {
                assert(b->isTrue());
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                    expl.push(b->getValLit());
                }
                submit_conflict_explanation(expl);
                return false;
            } else {
                // Set 'b' to false
                Clause * reason = NULL;
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                    reason = get_reason_for_update(expl);
                }
                if (! b->setVal(false, reason)) return false;
                return true;
            }
        }
    }
    
    if (b->isFixed()) {
        assert(b->isTrue());
        // Add constraint to propagator and label it with SIGMA
        const int indexCons = addConstraint(diff, b, x, y, d, DLConsHalf, DLSigma);

        // Check consistency and add edge to the graph
        if (! doCottonMaler(diff, indexX, indexY, d, indexCons)) return false;
    } else {
        // Add constraint to propagator and label it with LAMBDA
        const int indexCons = addConstraint(diff, b, x, y, d, DLConsHalf, DLLambda);
        // Add subscription
        b->attach(diff, diff->_cap + indexCons, EVENT_LU);
        DLMSG("Add subscription for b (%p)\n", b);
    }

    return true;
}


static bool addQueuedConstraints(DifferenceLogic * diff)
{
    if (diff->_tempCons.size() <= 0) return true;

    DLMSG("Entering addQueuedConstraints\n");
    for (int i = 0; i < diff->_tempCons.size(); i++) {
        BoolView  * b = diff->_tempCons[i]._b;
        IntVar    * x = diff->_tempCons[i]._x;
        IntVar    * y = diff->_tempCons[i]._y;
        const int   d = diff->_tempCons[i]._d;

        switch (diff->_tempCons[i]._t) {
        case DLConsPure:
            if (!addQueuedPure(diff, x, y, d)) 
                return false;
            break;
        case DLConsReif:
            if (!addQueuedReif(diff, b, x, y, d)) 
                return false;
            break;
        case DLConsHalf:
            if (!addQueuedHalf(diff, b, x, y, d)) 
                return false;
            break;
        }
    }
    diff->_tempCons.clear();

    DLMSG("Leaving addQueuedConstraints\n");

    return true;
}

    // b <-> x - y <= d
static bool bindQueuedReif(DifferenceLogic * diff, const int indexCons)
{
    BoolView  * b = diff->_cons0._cons[indexCons]._b;
    IntVar    * x = diff->_cons0._cons[indexCons]._x;
    IntVar    * y = diff->_cons0._cons[indexCons]._y;
    const int   d = diff->_cons0._cons[indexCons]._d;

    assert(b->isFixed());
    assert(*(diff->_cons0._cons[indexCons]._label) == DLSigma);

    DLMSG("constraint b %p (<)-> x[%d, %d] - y[%d, %d] <= %d\n", b, x->getMin(), x->getMax(), y->getMin(), y->getMax(), d);

    // Is x - y <= d implied by bounds?
    if (x->getMax() - y->getMin() <= d) {
        if (b->isFalse()) {
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, x, y, d, expl);
                expl.push(b->getValLit());
            }
            submit_conflict_explanation(expl);
            return false;
        }
        // XXX [AS] Commented because constraint might be not implied by PI
        // (see Thm. 2 in Feydy et al. 2008)
        labelSigmaLambdaConsAsDelta(diff, indexCons);
        return true;
    }
    // Is not(x - y <= d) implied by bounds?
    if (y->getMax() - x->getMin() < -d) {
        if (b->isTrue()) {
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
                expl.push(b->getValLit());
            }
            submit_conflict_explanation(expl);
            return false;
        }
        // XXX [AS] Commented because constraint might be not implied by PI
        // (see Thm. 2 in Feydy et al. 2008)
        labelSigmaLambdaConsAsDelta(diff, indexCons);
        return true;
    }
    // Is implied by PI
    const int indexX = getNodeIndex(diff, x);
    const int indexY = getNodeIndex(diff, y);

    if (diff->_succ0[indexX]._size > 0 && diff->_pred0[indexY]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'x'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexX, INT_MIN, true);
        // Is implied by PI
        if (dist[indexY] < INT_MAX && dist[indexY] + diff->_nodes0[indexY]._pi - diff->_nodes0[indexX]._pi <= d) {
            if (b->isFalse()) {
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexX, indexY, expl);
                    expl.push(b->getValLit());
                }
                submit_conflict_explanation(expl);
                return false;
            }
            labelSigmaLambdaConsAsDelta(diff, indexCons);
            return true;
        }
    }

    // Is negated constraint implied by PI?
    if (diff->_succ0[indexY]._size > 0 && diff->_pred0[indexX]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'y'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexY, INT_MIN, true);
        if (dist[indexX] < INT_MAX && dist[indexX] + diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi < -d) {
            if (b->isTrue()) {
                vec<Lit> expl;
                if (so.lazy) {
                    analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                    expl.push(b->getValLit());
                }
                submit_conflict_explanation(expl);
                return false;
            }
            labelSigmaLambdaConsAsDelta(diff, indexCons);
            return true;
        }
    }
    
    // Check consistency and add edge to the graph
    if (b->isTrue()) {
        if (! doCottonMaler(diff, indexX, indexY, d, indexCons)) return false;
    } else {
        if (! doCottonMaler(diff, indexY, indexX, -d - 1, indexCons)) return false;
    }

    // XXX [AS] Consequences have not be computed for this constraint!!!
    // XXX [AS] Should it be not relabelled?
    // Relabeling of the constraint
    //labelSigmaConsAsPi(diff, indexCons);

    return true;
}


    // b -> x - y <= d
static bool bindQueuedHalf(DifferenceLogic * diff, const int indexCons)
{
    BoolView  * b = diff->_cons0._cons[indexCons]._b;
    IntVar    * x = diff->_cons0._cons[indexCons]._x;
    IntVar    * y = diff->_cons0._cons[indexCons]._y;
    const int   d = diff->_cons0._cons[indexCons]._d;

    assert(b->isFixed() && b->isTrue());
    assert(*(diff->_cons0._cons[indexCons]._label) == DLSigma);

    // Is x - y <= d implied by bounds?
    // XXX [AS] Commented because constraint might be not implied by PI
    // (see Thm. 2 in Feydy et al. 2008)
    if (x->getMax() - y->getMin() <= d) {
        labelSigmaLambdaConsAsDelta(diff, indexCons);
        return true;
    }

    // Is not(x - y <= d) implied by bounds?
    if (y->getMax() - x->getMin() < -d) {
        vec<Lit> expl;
        if (so.lazy) {
            analyse_implication_by_bounds(diff, y, x, -d - 1, expl);
            expl.push(b->getValLit());
        }
        printf("N len %d;\n", expl.size());
        submit_conflict_explanation(expl);
        return false;
    }
    
    // Is constraint implied by PI?
    const int indexX = getNodeIndex(diff, x);
    const int indexY = getNodeIndex(diff, y);

    if (diff->_succ0[indexX]._size > 0 && diff->_pred0[indexY]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'x'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexX, INT_MIN, true);
        // Is implied by PI
        if (dist[indexY] < INT_MAX && dist[indexY] + diff->_nodes0[indexY]._pi - diff->_nodes0[indexX]._pi <= d) {
            labelSigmaLambdaConsAsDelta(diff, indexCons);
            return true;
        }
    }

    // Is negated constraint implied by PI?
    if (diff->_succ0[indexY]._size > 0 && diff->_pred0[indexX]._size > 0) {
        const int size = (int) diff->_size;
        int dist[size], backtrace[size], prev_node[size];
        // Single shortest path calculation from in the reduced cost graph starting from 'y'
        doDijkstraWithReducedCost(diff, diff->_succ0, dist, backtrace, prev_node, indexY, INT_MIN, true);
        if (dist[indexX] < INT_MAX && dist[indexX] + diff->_nodes0[indexX]._pi - diff->_nodes0[indexY]._pi < -d) {
            vec<Lit> expl;
            if (so.lazy) {
                analyse_implication_by_PI(diff, backtrace, prev_node, indexY, indexX, expl);
                expl.push(b->getValLit());
            }
            printf("O len %d;\n", expl.size());
            submit_conflict_explanation(expl);
            return false;
        }
    }
    
    // Check consistency and add edge to the graph
    if (! doCottonMaler(diff, indexX, indexY, d, indexCons)) 
        return false;
    
    return true;
}


static bool bindQueuedConstraints(DifferenceLogic * diff)
{
    if (diff->_tempBind.size() <= 0) return true;

    DLMSG("Entering bindQueuedConstraints\n");
    for (int ii = 0; ii < diff->_tempBind.size(); ii++) {
        const int   i = diff->_tempBind[ii];

        assert(diff->_cons0._cons[i]._type != DLConsPure);

        if (diff->_cons0._cons[i]._type == DLConsReif) {
            DLMSG("Reified constraint %d\n", i);
            if (!bindQueuedReif(diff, i)) return false;
        } else {
            assert(diff->_cons0._cons[i]._type == DLConsHalf);
            if (!bindQueuedHalf(diff, i)) return false;
        }
    }
    diff->_tempBind.clear();
    DLMSG("Leaving bindQueuedConstraints\n");

    return true;
}

/*******************************************************************************
 Some Sanity Checks
 ******************************************************************************/

static bool checkBoundsPure(DifferenceLogic * diff, const int indexCons)
{
    assert(diff->_cons0._cons[indexCons]._type == DLConsPure);
    const IntVar * x = diff->_cons0._cons[indexCons]._x;
    const IntVar * y = diff->_cons0._cons[indexCons]._y;
    const int      d = diff->_cons0._cons[indexCons]._d;
    const int x_lb = x->getMin();
    const int x_ub = x->getMax();
    const int y_lb = y->getMin();
    const int y_ub = y->getMax();

    if (x_lb > y_lb + d || x_ub > y_ub + d) {
        DLMSG("ERROR cons %d: x(%d) [%d, %d] - y(%d) [%d, %d] <= %d\n", indexCons, x->var_id, x_lb, x_ub, y->var_id, y_lb, y_ub, d);
        return false;
    }

    return true;
}

static bool checkBoundsReif(DifferenceLogic * diff, const int indexCons)
{
    assert(diff->_cons0._cons[indexCons]._type == DLConsReif);
    const DLCons cons = diff->_cons0._cons[indexCons];
    const BoolView * b = cons._b;
    
    if (!b->isFixed())
        return true;

    const bool isTrue = b->isTrue();
    const IntVar   * x = (isTrue ? cons._x : cons._y);
    const IntVar   * y = (isTrue ? cons._y : cons._x);
    const int        d = (isTrue ? cons._d : -cons._d - 1);
    const int x_lb = x->getMin();
    const int x_ub = x->getMax();
    const int y_lb = y->getMin();
    const int y_ub = y->getMax();

    if (x_lb > y_lb + d || x_ub > y_ub + d) {
        DLMSG("ERROR cons %d: b [true %d] (%p) <-> x(%d) [%d, %d] - y(%d) [%d, %d] <= %d\n", indexCons, isTrue, b, x->var_id, x_lb, x_ub, y->var_id, y_lb, y_ub, d);
        return false;
    }

    return true;
}

static bool checkBoundsHalf(DifferenceLogic * diff, const int indexCons)
{
    assert(diff->_cons0._cons[indexCons]._type == DLConsHalf);
    const DLCons cons = diff->_cons0._cons[indexCons];
    const BoolView * b = cons._b;
    
    if (!b->isTrue())
        return true;
    
    const IntVar   * x = cons._x;
    const IntVar   * y = cons._y;
    const int        d = cons._d;
    const int x_lb = x->getMin();
    const int x_ub = x->getMax();
    const int y_lb = y->getMin();
    const int y_ub = y->getMax();

    if (x_lb > y_lb + d || x_ub > y_ub + d) {
        DLMSG("ERROR cons %d: b [true 1] (%p) <-> x(%d) [%d, %d] - y(%d) [%d, %d] <= %d\n", indexCons, b, x->var_id, x_lb, x_ub, y->var_id, y_lb, y_ub, d);
        return false;
    }

    return true;
}

static bool checkBounds(DifferenceLogic * diff, int indexCons)
{
    while (indexCons >= 0) {
        const DLCons cons = diff->_cons0._cons[indexCons];
        bool val = true;

        switch (cons._type) {
        case DLConsPure:
            val = checkBoundsPure(diff, indexCons);
            break;
        case DLConsReif:
            val = checkBoundsReif(diff, indexCons);
            break;
        case DLConsHalf:
            val = checkBoundsHalf(diff, indexCons);
            break;
        }
        
        if (!val)
            return false;
        indexCons = *(cons._next);
    }
    return true;
}

/*******************************************************************************
 Main Propagation Loop
 ******************************************************************************/

static bool doPropagation(DifferenceLogic * diff)
{
    DLMSG("%%------------------------------%%\n");
    DLMSG("Entering propagation (%p); bindSize %d\n", diff, diff->_tempBind.size());

    //printGraph(diff);

    int * distX      = NULL;    // Length of the shortest path to node 'x'
    int * distY      = NULL;    // Length of the shortest path from node 'y'
    int * prevNodeX  = NULL;
    int * prevNodeY  = NULL;
    int * backtraceX = NULL;
    int * backtraceY = NULL;
    
    if (diff->_sigmaFirst < 0 && diff->_changeLB._size < 1 && diff->_changeUB._size < 1 && diff->_tempCons.size() < 0) {
        // Nothing to do
        return true;
    }
    assert(checkSuccessors(diff));
    assert(checkPredecessors(diff));

    // Binding of the queued constraints
    //
    if (!bindQueuedConstraints(diff)) 
        return false;

    // Addition of the queued constraints
    //
    if (!addQueuedConstraints(diff)) 
        return false;
    
    // Allocating space
    //
    distX      = (int *) alloca(diff->_size * sizeof(int));
    distY      = (int *) alloca(diff->_size * sizeof(int));
    
    if (distX == NULL || distY == NULL) {
        ERROR("Out of memory");
    }

    // Bounds propagation
    //
    while (diff->_changeLB._size > 0) {
        const int sizeLB = diff->_changeLB._size;
        diff->_changeLB._size = 0;
        if (!doBoundsByDijkstraWithReducedCostLB(diff, diff->_succ0, diff->_changeLB._array, sizeLB, distX)) {
            return false;
        }
    }
    while (diff->_changeUB._size > 0) {
        const int sizeUB = diff->_changeUB._size;
        diff->_changeUB._size = 0;
        if (!doBoundsByDijkstraWithReducedCostUB(diff, diff->_pred0, diff->_changeUB._array, sizeUB, distY)) {
            return false;
        }
    }

    assert(checkBounds(diff, diff->_piFirst));
    assert(checkBounds(diff, diff->_deltaFirst));
    assert(checkReducedCosts(diff));
    
    // Check for implied constraints by bounds
    //
    //checkImplicationByBounds(diff, diff->_sigmaFirst );
    checkImplicationByBounds(diff, diff->_lambdaFirst);
    
    // Propagation of all assigned constraints that have not propagated yet
    //
    if (diff->_lambdaFirst >= 0) {

        prevNodeX  = (int *) alloca(diff->_size * sizeof(int));
        prevNodeY  = (int *) alloca(diff->_size * sizeof(int));
        backtraceX = (int *) alloca(diff->_size * sizeof(int));
        backtraceY = (int *) alloca(diff->_size * sizeof(int));
        
        if (prevNodeX == NULL || prevNodeY == NULL || backtraceX == NULL || backtraceY == NULL) {
            ERROR("DifferenceLogic: Out of memory");
        }

        while (diff->_sigmaFirst >= 0) {
            const int indexCons = diff->_sigmaFirst;
            const DLConsType t  = diff->_cons0._cons[indexCons]._type;
            int indexX;
            int indexY;
            int dXY;

            switch (t) {
            case DLConsReif:
                assert(diff->_cons0._cons[indexCons]._b->isFixed());
                if (diff->_cons0._cons[indexCons]._b->isFalse()) {
                    indexX    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._y);
                    indexY    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._x);
                    dXY       = -1 - diff->_cons0._cons[indexCons]._d;
                    break;
                }
            case DLConsHalf:
                assert(diff->_cons0._cons[indexCons]._b->isTrue());
            case DLConsPure:
                indexX    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._x);
                indexY    = getNodeIndex(diff, diff->_cons0._cons[indexCons]._y);
                dXY       = diff->_cons0._cons[indexCons]._d;
                break;
            }

            DLMSG("Implication via constraint %d: x(%d) - y(%d) <= %d (SIGMA)\n", indexCons, indexX, indexY, dXY);
            if (t == DLConsReif) {
                const BoolView * b = diff->_cons0._cons[indexCons]._b;
                DLMSG("\tb (%p) true %d; false %d; <-> ...\n", b, b->isTrue(), b->isFalse());
            }

            // Calculating shortest path to 'x'
            doDijkstraWithReducedCost(diff, diff->_pred0, distX, backtraceX, prevNodeX, indexX, indexCons, false);
            // Calculating shortest path from 'y'
            doDijkstraWithReducedCost(diff, diff->_succ0, distY, backtraceY, prevNodeY, indexY, indexCons, true);

            // XXX Implication of SIGMA constraints are already checked in bind/addQueuedConstraints
            //// Check for implication of assigned constraints
            //if (!checkImplication(diff, distX, backtraceX, prevNodeX, distY, backtraceY, prevNodeY, dXY, *(diff->_cons0._cons[indexCons]._next))) {
            //    return false;
            //}

            // Check for implication of unassigned constraints
            if (!checkImplication(diff, distX, backtraceX, prevNodeX, distY, backtraceY, prevNodeY, indexCons, indexX, indexY, dXY, diff->_lambdaFirst)) {
                return false;
            }

            // Relabel constraint
            labelSigmaConsAsPi(diff, indexCons);
        }
    } else {
        while (diff->_sigmaFirst >= 0) {
            const int indexCons = diff->_sigmaFirst;
            // Relabel constraint
            labelSigmaConsAsPi(diff, indexCons);
        }
    }
    
    //testGraph(diff);
    
    resetIntContainers(diff);

    DLMSG("Leaving doPropagation\n");
    
    return true;
}

/*******************************************************************************
 Binary Queue
 ******************************************************************************/

#define DLPARENT(i) (i >> 1)
#define DLLEFT(i) (i << 1)
#define DLRIGHT(i) ((i << 1) + 1)

static DLBinPrioQueue * newBinPrioQueue(const int cap)
{
    if (cap < 1) {
        ERROR("DifferenceLogic: Must be initialised with a positve capacity");
    }
    DLBinPrioQueue * queue = NULL;
    queue = (DLBinPrioQueue *) malloc(sizeof(DLBinPrioQueue));
    if (queue == NULL) {
        ERROR("DifferenceLogic: Out of memory");
    }
    // Initialise
    queue->_size  = 0;
    queue->_cap   = 0;
    queue->_queue = NULL;
    
    queue->_queue = (DLPair *) malloc((cap + 1) * sizeof(DLPair));
    if (queue->_queue == NULL) {
        ERROR("DifferenceLogic: Out of memory");
    }
    
    queue->_cap  = cap + 1;
    queue->_size = 1;
    
    return queue;
}

static void deleteBinPrioQueue(DLBinPrioQueue * queue)
{
    if (queue != NULL) {
        if (queue->_queue != NULL) {
            free(queue->_queue);
        }
        free(queue);
    }
}

static void resizeBinPrioQueue(DLBinPrioQueue * queue, const int newCap)
{
    assert(queue != NULL && newCap > queue->_cap);
    DLPair * newPair = NULL;
    
    newPair = (DLPair *) realloc(queue->_queue, newCap * sizeof(DLPair));
    if (newPair == NULL) {
        ERROR("DifferenceLogic: Out of memory");
    }
    queue->_queue = newPair;
    queue->_cap   = newCap;
}

static inline bool isEmptyBinPrioQueue(DLBinPrioQueue * queue)
{
    assert(queue != NULL);
    return (queue->_size < 2);
}

static int popBinPrioQueue(DLBinPrioQueue * queue)
{
    if (queue == NULL || queue->_size <= 1) {
        ERROR("DifferenceLogic: Invalid pop operation");
    }
    const int first = queue->_queue[1]._id;
    
    // Removal of first element
    queue->_size--;
    queue->_queue[1]._id  = queue->_queue[queue->_size]._id;
    queue->_queue[1]._key = queue->_queue[queue->_size]._key;
    
    // Heapifying the queue
    heapifyBinPrioQueue(queue, 1);
    
    return first;
}

static void insertItemInBinPrioQueue(DLBinPrioQueue * queue, const int id, const int key)
{
    assert(queue != NULL);
    
    if (queue->_size >= queue->_cap) {
        resizeBinPrioQueue(queue, queue->_cap << 1);
    }
    assert(queue->_queue != NULL);
    queue->_queue[queue->_size]._id  = id;
    queue->_queue[queue->_size]._key = key;
    queue->_size++;
    
    moveItemUpwardInBinPrioQueue(queue, queue->_size - 1);
}

static void decreaseKeyInBinPrioQueue(DLBinPrioQueue * queue, const int id, const int newKey)
{
    assert(queue != NULL && queue->_size > 1 && queue->_queue != NULL);
    // Search item in O(n)
    int i;
    for (i = 1; i < queue->_size; i++) {
        if (queue->_queue[i]._id == id)
            break;
    }
    if (i >= queue->_size) {
        ERROR("DifferenceLogic: Key was not found");
    }
    if (queue->_queue[i]._key > newKey) {
        queue->_queue[i]._key = newKey;
        moveItemUpwardInBinPrioQueue(queue, i);
    }
}

static void heapifyBinPrioQueue(DLBinPrioQueue * queue, int i)
{
    int l, r, extr;
    
    while (true) {
        l = DLLEFT(i);
        r = DLRIGHT(i);
        
        if (l < queue->_size && queue->_queue[l]._key < queue->_queue[i]._key) {
            extr = l;
        }
        else {
            extr = i;
        }
        
        if (r < queue->_size && queue->_queue[r]._key < queue->_queue[extr]._key) {
            extr = r;
        }
        
        if (extr != i) {
            swapItemsInBinPrioQueue(queue, extr, i);
            i = extr;
        }
        else {
            break;
        }
    }
}

static inline void moveItemUpwardInBinPrioQueue(DLBinPrioQueue * queue, int i)
{
    int pI = DLPARENT(i);
    while (i > 1 && queue->_queue[pI]._key > queue->_queue[i]._key) {
        swapItemsInBinPrioQueue(queue, pI, i);
        i  = pI;
        pI = DLPARENT(i);
    }
}

static inline void swapItemsInBinPrioQueue(DLBinPrioQueue * queue, const int i, const int j)
{
    // Swapping the keys
    int tmp = queue->_queue[i]._key;
    queue->_queue[i]._key = queue->_queue[j]._key;
    queue->_queue[j]._key = tmp;
    
    // Swapping the ids
    tmp = queue->_queue[i]._id;
    queue->_queue[i]._id = queue->_queue[j]._id;
    queue->_queue[j]._id = tmp;
}

/*******************************************************************************
 Definition of the general functions
 ******************************************************************************/


static 
void submit_conflict_explanation(vec<Lit> & expl) {
	Clause * reason = NULL;
	if (so.lazy) {
		reason = Reason_new(expl.size());
		int i = 0;
		for (; i < expl.size(); i++) { (*reason)[i] = expl[i]; }
	}
	sat.confl = reason;
}

static
Clause * get_reason_for_update(vec<Lit> & expl) {
	Clause* reason = Reason_new(expl.size() + 1);
	for (int i = 1; i <= expl.size(); i++) {
		(*reason)[i] = expl[i-1];
	}
	return reason;
}


	// Wrapper to get the negated literal -[[v <= val]] = [[v >= val + 1]]
    //
static inline 
Lit getNegLeqLit(IntVar * v, int val) { 
	//return v->getLit(val + 1, 2); 
	return (INT_VAR_LL == v->getType() ? v->getMaxLit() : v->getLit(val + 1, 2));
}

	// Wrapper to get the negated literal -[[v >= val]] = [[ v <= val - 1]]
static inline 
Lit getNegGeqLit(IntVar * v, int val) { 
	//return v->getLit(val - 1, 3); 
	return (INT_VAR_LL == v->getType() ? v->getMinLit() : v->getLit(val - 1, 3));
}

/*******************************************************************************
 * DiffLogic members
 ******************************************************************************/

DiffLogic::DiffLogic(int numItems)
{
    diff = new DifferenceLogic(numItems);
}

DiffLogic::~DiffLogic()
{
    diff->~DifferenceLogic();
}

void DiffLogic::addDiff(IntVar * x, IntVar * y, const int d)
{
    getNodeIndex(diff, x);
    getNodeIndex(diff, y);
    diff->addDifference(x, y, d);
}

void DiffLogic::addReifyDiff(BoolView * b, IntVar * x, IntVar * y, const int d)
{
    getNodeIndex(diff, x);
    getNodeIndex(diff, y);
    diff->addReifyDifference(b, x, y, d);
}

void DiffLogic::addImplyDiff(BoolView * b, IntVar * x, IntVar * y, const int d)
{
    getNodeIndex(diff, x);
    getNodeIndex(diff, y);
    diff->addImplyDifference(b, x, y, d);
}

/*******************************************************************************
 * Model interface
 ******************************************************************************/

DiffLogic * diff_logic(int numItems)
{
    return  new DiffLogic(numItems);
}
