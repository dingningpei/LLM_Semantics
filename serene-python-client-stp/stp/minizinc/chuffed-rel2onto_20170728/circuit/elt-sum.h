#ifndef __ELT_SUM_H__
#define __ELT_SUM_H__
#include <core/propagator.h>
#include <circuit/circutil.h>

// \sum_{i \in 0..n-1} coeffs_i[x_i] #op k

struct cardstate {
  cardstate(int _n, int _k)
    : n(_n), k(_k)
  { }

  int n;
  int k;
};

struct IndSort
{
  const vec<int>& coeffs;
  bool operator () (int a, int b) const {
    return coeffs[a] < coeffs[b];
  }

  IndSort(const vec<int>& _coeffs)
    : coeffs(_coeffs)
  { }
};

// Assumes non-negative coefficients.
template<class T>
T elt_sum(const T fff, const vec< vec<int> >& coeffs, vec< vec<T> >& vars, IntRelType rel, int k)
{
  assert(coeffs.size() == vars.size());

  typename AutoC<cardstate, T>::cache cache;
  return elt_sumR(cache, fff, coeffs, vars, rel, 0, k);
}

template<class C, class T>
T elt_sumR(C& cache, const T fff, const vec< vec<int> >& coeffs, vec< vec<T> >& vars, IntRelType rel, int n, int k)
{
  // Base cases.
  switch(rel)
  {
    case IRT_GE:
      if(k <= 0)
        return ~fff;
      if(n == vars.size())
        return fff;
      break;

    case IRT_LE:
      if(k < 0)
        return fff;
      if(n == vars.size())
        return ~fff;

    case IRT_EQ:
      if(k < 0)
        return fff;
      if(n == vars.size())
        return (k == 0) ? ~fff : fff;
      break;
    default:
      NEVER;
  }

  assert(n < vars.size());

  // Recursive case -- check the hash table.
  cardstate sig(n, k); 
  
  typename C::iterator it(cache.find(sig));
  if(it != cache.end())
    return (*it).second;
  
  T ret = fff; 

  assert(coeffs[n].size() == vars[n].size());

  for(int ii = 0; ii < vars[n].size(); ii++)
  {
    ret = ret|(vars[n][ii]&elt_sumR(cache, fff, coeffs, vars, rel, n+1, k - coeffs[n][ii]));
  }

  cache[sig] = ret; 
  return ret;
}


// Template parameter U determines whether to construct the monotone MDDs or the full decomposition.
// Indices is the set of values ordered by increasing coefficient.
template<class C, int U>
Lit elt_sum_ltR(C& cache, vec< vec<int> >& indices, vec< vec<int> >& coeffs,
                                          vec<IntVar*>& vars, int n, int k, IntVar* cost)
{
  // Termination. Either we're at a leaf, or have exceeded the max value.
  if(k > cost->getMax())
    return lit_False;
  if(n == vars.size())
    return cost->getLit(k, (U&1) ? 1 : 2);
  
  // Recursive case -- check the hash table.
  cardstate sig(n, k); 
  
  typename C::iterator it(cache.find(sig));
  if(it != cache.end())
    return (*it).second;
  
  vec<Lit> val;
  vec<Lit> dest;
  for(int ii = 0; ii < indices[n].size(); ii++)
  {
//    Lit vlit(vars[n]->getLit(indices[n][ii], (U&1) ? 1 : 2));   
    Lit vlit(vars[n]->getLit(indices[n][ii], 1));
    if(vlit != lit_False)
    {
      Lit dlit(elt_sum_ltR<C,U>(cache, indices, coeffs, vars, n+1, k + coeffs[n][indices[n][ii]],cost));

      val.push(vlit);
      dest.push(dlit);
    }
  }

  assert(dest.size() == val.size());
  Lit ret;
  if(dest.size() == 0)
  {
    ret = lit_False;
  } else {
    ret = Lit(sat.newVar(), 1);

    if(!(U&1))
    {
      sat.addClause(dest[0],~ret); 
    }
    for(int ii = (U&1) ? 0 : 1; ii < dest.size(); ii++)
    {
      vec<Lit> cl;
      if(U&1)
      {
        // val & dest => ret
        cl.push(~val[ii]);
        cl.push(~dest[ii]);
        cl.push(ret);
        sat.addClause(cl);
        
        cl.clear();
      }

      // val & ~dest => ~ret
      cl.push(~val[ii]);
      cl.push(dest[ii]);
      cl.push(~ret);
      sat.addClause(cl);
    }
  }

  cache[sig] = ret;
  return ret;
}

template<int U>
void elt_sum_decomp(vec< vec<int> >& coeffs, vec<IntVar*>& vars, IntRelType rel, IntVar* cost)
{
  assert(coeffs.size() == vars.size());

  for(int ii = 0; ii < vars.size(); ii++)
    vars[ii]->specialiseToEL();

  vec< vec<int> > indices;
  for(int ii = 0; ii < coeffs.size(); ii++)
  {
    indices.push();

    for(int jj = 0; jj < coeffs[ii].size(); jj++)
      indices[ii].push(jj);

    std::sort((int*) indices[ii], ((int*) indices[ii]) + indices[ii].size(), IndSort(coeffs[ii]));
  }
#if 0
  // Assumes coeffs are ordered.
  int lb = 0;
  int ub = 0;
  for(int ii = 0; ii < coeffs.size(); ii++)
  {
    lb += coeffs[ii][0];
    ub += coeffs[ii].last();
  }
  if(cost->setMinNotR(lb))
    cost->setMin(lb);
  if(cost->setMaxNotR(ub))
    cost->setMax(ub);
#endif

  cost->specialiseToEL();

  typename AutoC<cardstate, Lit>::cache cache;
  Lit circ = elt_sum_ltR<AutoC<cardstate, Lit>::cache, U>(cache, indices, coeffs, vars, 0, 0, cost);

  sat.enqueue(circ);
}

#endif
