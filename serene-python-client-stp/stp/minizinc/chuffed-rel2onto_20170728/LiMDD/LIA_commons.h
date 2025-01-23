#include <vector>
#include <algorithm>
#include <iostream>
#include <unordered_map>
#include "../core/sat-types.h"

using namespace std;

#ifndef _LIA_COMMONS_
#define _LIA_COMMONS_

namespace LIA_Commons
{

  inline void normalize(vector<vector<Lit> >& lits, vector<int>& coeffs, int& trans, bool log) {
    if (log) {
      for (uint i = 0; i < coeffs.size(); i++) {
	if ( coeffs[i]<0 ) {
	  uint d = 1; for (uint j = 0; j < lits[i].size(); j++) d*=2;
	  d--;
	  coeffs[i] = -coeffs[i];
	  trans += coeffs[i]*d;
	  for (uint j = 0; j < lits[i].size(); j++) lits[i][j]=~lits[i][j];
	}
      }
      return;
    }
    for (uint i = 0; i < coeffs.size(); i++) {
      if ( coeffs[i]<0 ) {
	uint d = lits[i].size();
	coeffs[i] = -coeffs[i];
	trans += coeffs[i]*d;
	for (uint j = 0; j < d/2; j++) {
	  Lit aux = lits[i][j];
	  lits[i][j]=~lits[i][d-j-1];
	  lits[i][d-j-1] = ~aux;
	}
	if ( d%2 ) lits[i][d/2] = ~lits[i][d/2];
      }
    }
  }


  inline void normalize(vector<vector<int> >& lits, vector<int>& coeffs, int& trans, bool log) {
    if (log) {
      for (uint i = 0; i < coeffs.size(); i++) {
	if ( coeffs[i]<0 ) {
	  uint d = 1; for (uint j = 0; j < lits[i].size(); j++) d*=2;
	  d--;
	  coeffs[i] = -coeffs[i];
	  trans += coeffs[i]*d;
	  for (uint j = 0; j < lits[i].size(); j++) lits[i][j]=-lits[i][j];
	}
      }
      return;
    }
    for (uint i = 0; i < coeffs.size(); i++) {
      if ( coeffs[i]<0 ) {
	uint d = lits[i].size();
	coeffs[i] = -coeffs[i];
	trans += coeffs[i]*d;
	for (uint j = 0; j < d/2; j++) {
	  int aux = lits[i][j];
	  lits[i][j]=-lits[i][d-j-1];
	  lits[i][d-j-1] = -aux;
	}
	if ( d%2 ) lits[i][d/2] = -lits[i][d/2];
      }
    }
  }

  struct CmpInd {
    CmpInd(vector<int>& vec) : values(vec) {}
    bool operator() (const int& a, const int& b) const {
      return values[a] < values[b] || (values[a]==values[b] && a < b);
      //return a < b;
    }
    vector<int>& values;
  };

    template<typename T>
  inline void sort(vector<vector<T> >& l, vector<int>& c, bool inv) {
    vector<int> ind(c.size());
    for (uint i = 0; i < c.size(); i++) ind[i]=i;

    std::sort(ind.begin(), ind.end(), CmpInd(c));
    if (inv) {
      vector<int>        newC(c); for (uint i = 0; i < ind.size(); i++) c[i]=newC[ind[i]];
      vector<vector<T> > newL(l); for (uint i = 0; i < ind.size(); i++) l[i]=newL[ind[i]];
    } else {
      vector<int>        newC(c); for (uint i = 0; i < ind.size(); i++) c[ind.size()-i-1]=newC[ind[i]];
      vector<vector<T> > newL(l); for (uint i = 0; i < ind.size(); i++) l[ind.size()-i-1]=newL[ind[i]];
    }
  }

}

#endif /* _LIA_COMMONS_ */
