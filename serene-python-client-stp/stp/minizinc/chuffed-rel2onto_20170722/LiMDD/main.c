//#include "MDD.h"
//#include "LIA_commons.h"


/*int main() {

int newVar = 0;
int K = 15;

	vector<li> coeffs;
	vector<li> domains;
        vector<vector<int> > lits;

	coeffs.push_back(3);
	coeffs.push_back(2);
	coeffs.push_back(5);

	domains.push_back(4);
	domains.push_back(2);
	domains.push_back(3);

	MDD mdd;
	mdd.defineConstraint(coeffs,domains);

	mdd.newRoot(K);

	mdd.printMDD();


vector<vector<int> > newClauses;
  SimpMerge simpMerge;
  vector<vector<int> > l2(lits);
  vector<int> c2(coeffs);

  if ( K < 0 ) {
    newClauses.push_back(vector<int>(0));
    return 0;
  }

  for (uint i = 0; i < l2.size(); i++) {
    if ( c2[i]*l2[i].size() > K ) {
      newClauses.push_back(vector<int>(1, l2[i][K/c2[i]]));
      l2[i].resize(K/c2[i]);
      if (l2[i].size() == 0 ) {
  	if ( i < l2.size()-1 ) {
  	  l2[i].swap(l2.back());
  	  c2[i] = c2.back();
  	}
  	l2.pop_back();
  	c2.pop_back();
  	i--;
      }
    }
  }

  if ( l2.size() == 0 ) return 0;

  uint s=0;
  for (uint i = 0; i < l2.size(); i++) s+=c2[i]*l2[i].size();
  if ( s <= K ) return 0;

  uint nV = newVar;
  LIA_Commons::sort(l2, c2, false);

  vector<vector<int> > l3;
  vector<int> c3;

  for (uint i = 0; i < l2.size(); i++) {
    uint ini = i;
    while( i < l2.size()-1 && c2[i] == c2[i+1] ) i++;
    if (c2[i] == 0 ) continue;
    vector<int> V(l2[ini].size());
    for (uint j =0; j < l2[ini].size(); j++) V[j]=-l2[ini][j];
    for (uint j = ini+1; j <= i; j++) {
      vector<int> aux;
      vector<int> aux2(l2[j].size());
      for (uint k =0; k < l2[j].size(); k++) aux2[k]=-l2[j][k];
      simpMerge.createNetwork(V, aux2, aux, K/(c2[ini])+1, nV, newClauses);
      V = aux;
    }
    for (uint j =0; j < V.size(); j++) V[j]=-V[j];
    while ( V.size() * c2[ini] > K ) {
      newClauses.push_back(vector<int>(1,V.back()));
      V.pop_back();
    }
    l3.push_back(V);
    c3.push_back(c2[ini]);
  }

  newVar=nV;

  s=0;
  for (uint i = 0; i < l3.size(); i++) s+=c3[i]*l3[i].size();
  if ( s <= K ) return 0;

  vector<int> dom(l3.size());
  for(uint i = 0; i < l3.size(); i++) dom[i]=l3[i].size();
  MDD mdd2;
  mdd2.defineConstraint(c3, dom);

  NodeID node;
  NodeID root = mdd2.newRoot(K);
  if ( mdd2.isTerminal(root) ) {
    if (mdd2.isTrue(root)) return 0;
    newClauses.push_back(vector<int>(0));
    return 0;
  }

  node = mdd2.getFirstNode();

  while(true) {
    if (!mdd2.isTerminal(node)) {
      uint nS = mdd2.getNumSons(node);
      if ( mdd2.getSon(node,0) == mdd2.getSon(node, nS-1) ) { // Long edge node.
	if ( mdd2.isTerminal(mdd2.getSon(node,0)) )	mdd2.setTerminal(node, mdd2.isTrue(mdd2.getSon(node,0)) );
	else mdd2.setVar(node,mdd2.getVar(mdd2.getSon(node,0)));
      } else {
	NodeID last = node; // No last.
	for (uint i = 0; i < nS; i++) {
	  NodeID current = mdd2.getSon(node,i);
	  if ( last != current ) {
	    last = current;
	    if (mdd2.isTerminal(current)) {
	      if (!mdd2.isTrue(current)) {
		// Current is the false node. Clause "node -> lit < i" is needed (or, equiv., 'NEG n' OR 'lit <= i-1').
		dassert(i>0);
		newClauses.push_back(vector<int>(2));
		newClauses.back()[0]=-(int)nV;
		newClauses.back()[1]=l3[mdd2.getLevel(node)][i-1];
	      } // No else: if current is the true node, nothing is needed.
	    } else {
	      // General case: "n AND 'lit >= i' -> current"
	      newClauses.push_back(vector<int>());
	      newClauses.back().push_back(-(int)nV);
	      if (i > 0) newClauses.back().push_back(l3[mdd2.getLevel(node)][i-1]);
	      // Note: if i = 0, 'lit >= i' is a tautology
	      newClauses.back().push_back(mdd2.getVar(current));
	    }
	  }
	}
	mdd2.setVar(node, nV++);
      }
    }
    if (mdd2.isLast(node)) break;
    else node = mdd2.nextNode(node);
  }

  dassert(node == root);
  newClauses.push_back(vector<int>(1,mdd2.getVar(root)));
  newVar=nV;

   cout << "**************************" << endl;
   for (uint i = 0; i < newClauses.size(); i++) {
     for (uint j = 0; j < newClauses[i].size(); j++) cout << newClauses[i][j] << " ";
     cout << 0 << endl;
   }


}


*/
