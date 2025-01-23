
#include <cassert>
#include <vector>
#include "../globals/graph_propagator.h"

using namespace std;

class BitOperations {
public:
    //***********************************************************************************
    // METHODS
    //***********************************************************************************

    // LCA typical operations

    /**
     * Get the lowest common ancestor of x and y in a complete binary tree
     *
     * @param x a node
     * @param y a node
     * @return the lowest common ancestor of x and y in a complete binary tree
     */
    static int binaryLCA(int x, int y) {
        if (x == y) {
            return x;
        }
        int exclusive_or = x ^ y;
        int idx = getMaxExp(exclusive_or);
        assert(idx != -1);
        return replaceBy1and0sFrom(x, idx);
    }

    /**
     * @param x   value/node
     * @param idx index to place the 1 followed by zeroes
     * @return a new int that values x until idx (excluded) and 1(000...) then
     */
    static int replaceBy1and0sFrom(int x, int idx) {
        x = ((unsigned int)x) >> (idx + 1);
        x = x << 1;
        x++;
        x = x << (idx);
        return x;
    }

    // Exponents getters

    /**
     * @param x a node
     * @return the index of the last 1-bit, starting from 0
     *         0 return -1 if no bit is set to 1
     */
    static int getMaxExp(int x) {
        int exp = -1;
        while (x > 0) {
            exp++;
            x /= 2;
        }
        return exp;
    }

    /**
     * @param x node
     * @param j value
     * @return the index of the last 1-bit which is lower than j, starting from 0
     *         return -1 if no such bit exists
     */
    static int getMaxExpBefore(int x, int j) {
        x %= pow(2, j);
        return getMaxExp(x);
    }

    /**
     * @param x a node
     * @return the index of the first 1-bit, starting from 0
     *         return -1 if no such bit exists
     */
    static int getFirstExp(int x) {
        if (x == 0) {
            return -1;
        }
        int exp = 0;
        while (x % 2 == 0) {
            exp++;
            x /= 2;
        }
        return exp;
    }

    /**
     * @param x a node
     * @param y a node
     * @param i a value
     * @return the index of the first 1-bit in both x and y, which is greater or equal to i,
     *         return -1 if no such bit exists
     */
    static int getFirstExpInBothXYfromI(int x, int y, int i) {
        x = ((unsigned int)x) >> i;
        y = ((unsigned int)y) >> i;
        if ((x & y) == 0) { // x and y have no 1-bit >=i in common
            return -1;
        }
        while (x % 2 == 0 || y % 2 == 0) {
            i++;
            x /= 2;
            y /= 2;
        }
        return i;
    }

    // power

    /**
     * @param x a node
     * @param pow must be >= 0
     * @return x^pow
     */
    static int pow(int x, int pow) {
        assert(pow >= 0);
        if (pow == 0) {
            return 1;
        }
        pow--;
        int xp = x;
        while (pow > 0) {
            pow--;
            xp *= x;
        }
        return xp;
    }

};




class LCAGraphManager {
public:
    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    //
    int root;
    int nbNodes, nbActives;
    vector<vector<int> > children;
    //
    int* father;
    int* nodeOfDfsNumber;
    int* dfsNumberOfNode;
    //
    int *I, *L, *h, *A, *htmp;
    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    LCAGraphManager(int nb) {
        nbNodes = nb;
        vector<vector<int> > successors;
        father = new int[nbNodes];
        nodeOfDfsNumber = new int[nbNodes];
        dfsNumberOfNode = new int[nbNodes];
        htmp = new int[nbNodes];
        A = new int[nbNodes];
        I = new int[nbNodes];
        L = new int[nbNodes];
        h = new int[nbNodes];
    }

    ~LCAGraphManager() {
        delete[] father;
        delete[] nodeOfDfsNumber;
        delete[] dfsNumberOfNode;
        delete[] I;
        delete[] L;
        delete[] h;
        delete[] A;
        delete[] htmp;
    }

    void preprocess(int r, vector<vector<int> >& child, int graph_nodes) {
        root = r;
        children = child;
        nbActives = graph_nodes;
        initParams();
        proceedFirstDFS();
        performLCAPreprocessing();
    }

    //***********************************************************************************
    // QUERIES
    //***********************************************************************************

    int getLCA(int x, int y) {
        return nodeOfDfsNumber[getDFS_LCA(dfsNumberOfNode[x], dfsNumberOfNode[y])];
    }

    //***********************************************************************************
    // INITIALIZATION
    //***********************************************************************************

    void initParams() {
        for (int i = 0; i < nbNodes; i++) {
            dfsNumberOfNode[i] = -1;
            father[i] = -1;
            A[i] = -1;
        }
    }

    /**
     * perform a dfs in graph to label nodes
     */
    void proceedFirstDFS() {
        vector<vector<int>::iterator> iterator;
        for(int i = 0; i < nbNodes; i++){
            iterator.push_back(children[i].begin());
        }
        int i = root;
        int k = 0;
        father[k] = k;
        dfsNumberOfNode[root] = k;
        nodeOfDfsNumber[k] = root;
        int j;
        k++;
        while (true) {
            if (iterator[i] != children[i].end()) {
                j = *(iterator[i]);
                iterator[i]++;
                if (dfsNumberOfNode[j] == -1) {
                    father[k] = dfsNumberOfNode[i];
                    dfsNumberOfNode[j] = k;
                    nodeOfDfsNumber[k] = j;
                    i = j;
                    k++;
                }
            }else{
                if (i == root) {
                    break;
                }else {
                    i = nodeOfDfsNumber[father[dfsNumberOfNode[i]]];
                }
            }
        }
        assert(k == nbActives);
        for (; k < nbNodes; k++) {
            father[k] = -1;
        }
    }

    //***********************************************************************************
    // LCA  attention : numerotation 1 - n (et non 0 - n-1) pour les manipulations de bit
    //***********************************************************************************

    /**
     * LCA PREPROCESSING O(m+n) by Chris Lewis
     * 1.	Do a depth first traversal of the general tree to assign 
     depth-first search numbers to the nodes. For each node set a pointer to its parent.
     * 2.	Using a linear time bottom up algorithm, compute I(v) for each 
     node. For each k such that I(v) = k for some v, set L(k) to point to the head of the run containing k.
     * (=>I(v) pointe sur le dernier element, L(I(v)) vers le premier)
     * o	The head of a run is identified when computing I values. v is 
     identified as the head of its run if the I value of v's parent is not I(v).
     * o	After this step, the head of a run containing an arbitrary node 
     v can be located in constant time. First compute I(v) then look up the value L(I(v)).
     * 3.	Given a complete binary tree with node-depth ceiling(log n)-1, 
     map each node v in the general tree to I(v) in the binary tree (Fig 4).
     * 4.	For each node v in the general tree create on O(log n) bit number 
     A v. Bit A v(i) is set to 1 if and only if node v has an ancestor
     * in the general tree that maps to height i in the binary tree. i.e. 
     iff v has an ancestor u such that h(I(u)) = i.
    */
    void performLCAPreprocessing() {
        // step 1 : DFS already done
        // step 2
        for (int i = nbActives - 1; i >= 0; i--) {
            h[i] = BitOperations::getFirstExp(i + 1);
            assert(h[i] != -1);
            htmp[i] = h[i];
            I[i] = i;
            L[i] = i;
            int sucInRun = -1;
            vector<int>& nei = children[nodeOfDfsNumber[i]];
            int s;
            vector<int>::iterator k = nei.begin();           
            for (; k != nei.end(); ++k) {
                s = dfsNumberOfNode[*k];
                if (i != s && father[s] == i && htmp[s] > htmp[i]) {
                    htmp[i] = htmp[s];
                    sucInRun = s;
                }
            }
            if (sucInRun != -1) {
                I[i] = I[sucInRun];
                L[I[i]] = i;
            }
        }
        // step 3 : mapping to a binary tree : the binary tree is virtual here so there is nothing to do
        //step 4
        // A[0] = I[0];
        int exp = BitOperations::getFirstExp(I[0] + 1);
        assert(exp != -1);
        A[0] = BitOperations::pow(2, exp);
        for (int i = 0; i < nbActives; i++) {
            A[i] = A[father[i]];
            if (I[i] != I[father[i]]) {
                exp = BitOperations::getFirstExp(I[i] + 1);
                assert(exp != -1);
                A[i] += BitOperations::pow(2, exp);
            }
        }
    }

    /**
     * Get the lowest common ancestor of two nodes in O(1) time
     * Query by Chris Lewis
     * 1.	Find the lowest common ancestor b in the binary tree of nodes I(x) and I(y).
     * 2.	Find the smallest position j &ge; h(b) such that both numbers A x and A y have 1-bits in position j.
     * This gives j = h(I(z)).
     * 3.	Find node x', the closest node to x on the same run as z:
     * a.	Find the position l of the right-most 1 bit in A x
     * b.	If l = j, then set x' = x {x and z are on the same run in the general graph} and go to step 4.
     * c.	Find the position k of the left-most 1-bit in A x that is to the right of position j.
     * Form the number consisting of the bits of I(x) to the left of the position k,
     * followed by a 1-bit in position k, followed by all zeros. {That number will be I(w)}
     * Look up node L(I(w)), which must be node w. Set node x' to be the parent of node w in the general tree.
     * 4.	Find node y', the closest node to y on the same run as z using the approach described in step 3.
     * 5.	If x' < y' then set z to x' else set z to y'
     *
     * @param x node dfs number
     * @param y node dfs number
     * @return the dfs number of the lowest common ancestor of a and b in the dfs tree
     */
    int getDFS_LCA(int x, int y) {
        // trivial cases
        if (x == y || x == father[y]) {
            return x;
        }
        if (y == father[x]) {
            return y;
        }
        // step 1
        int b = BitOperations::binaryLCA(I[x] + 1, I[y] + 1);
        // step 2
        int hb = BitOperations::getFirstExp(b);
        assert(hb != -1);
        int j = BitOperations::getFirstExpInBothXYfromI(A[x], A[y], hb);
        assert(j != -1);
        // step 3 & 4
        int xPrim = closestFrom(x, j);
        int yPrim = closestFrom(y, j);
        // step 5
        if (xPrim < yPrim) {
            return xPrim;
        }
        return yPrim;
    }

    int closestFrom(int x, int j) {
        // 3.a
        int l = BitOperations::getFirstExp(A[x]);
        assert(l != -1);
        if (l == j) {    // 3.b
            return x;
        } else {        // 3.c
            int k = BitOperations::getMaxExpBefore(A[x], j);
            int IW = I[x] + 1;
            if (k != -1) { // there is at least one 1-bit at the right of j
                IW = BitOperations::replaceBy1and0sFrom(IW, k);
            } else {
                assert(false);
            }
            IW--;
            return father[L[IW]];
        }
    }

    //***********************************************************************************
    // ACCESSORS
    //***********************************************************************************

    /**
     * Get the parent of x in the dfs tree
     *
     * @param x the focused node
     * @return the parent of x in the dfs tree
     */
    int getParentOf(int x) {
        return nodeOfDfsNumber[father[dfsNumberOfNode[x]]];
    }

};
