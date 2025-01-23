#include <vector>
#include "common.h"

using namespace std;

#ifndef _INTERVAL_
#define _INTERVAL_

class Interval {
private:
    typedef unsigned int uint;
    typedef uint Literal;
    typedef uint NodeID;
    typedef uint Var;
    typedef int SelVar;
    typedef int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.
    //typedef long long int li; // Modify this line if arbitrary precision is needed. Basic arithmetic, streaming and comparisson operations are needed.
  li a, b;
  NodeID n;
public:
  inline Interval ( const vector<Interval> &vi, li add, NodeID _n );
  inline Interval ( li _a );
  inline Interval ( bool b, NodeID _n );
  inline Interval ( const Interval& i );
  inline bool operator < ( const Interval &i2 ) const;
  inline bool operator > ( const Interval &i2 ) const;
  inline bool operator == ( const Interval &i2 ) const;
  inline void print () const;
  inline li getA () const { return a; }
  inline li getB () const { return b; }
  inline NodeID getNodeID () const { return n; }
};

////////////////////////////////////////////////////////////////////////////
////////////////////// Interval Class Implementation: //////////////////////
////////////////////////////////////////////////////////////////////////////

inline Interval::Interval ( const vector<Interval> &vi, li add, NodeID _n ):n(_n) {
  //cout << vi.size() << " " << vi[0].a << " " << vi[0].b << " " << n << endl; 
  dassert( vi.size()>0 && vi[0].a <= vi[0].b );
  a=vi[0].a; b=vi[0].b;
  li x = add;
  for (uint i = 1; i < vi.size(); i++){
    li viax = (vi[i].a == LI_MIN? LI_MIN:vi[i].a+x);
    li vibx = (vi[i].b == LI_MAX? LI_MAX:vi[i].b+x);

    dassert( vi[i].a <= vi[i].b && viax <= b && vibx >= a );
    if (viax > a) a = viax;
    if (vibx < b) b = vibx;
    x+=add;
  }
}
inline Interval::Interval ( li _a ):a(_a),b(_a) {}
inline Interval::Interval ( bool _b, NodeID _n ):n(_n) {
  a=( _b ? 0      : LI_MIN );
  b=( _b ? LI_MAX : -1     );
}
inline Interval::Interval ( const Interval& i ):a(i.a),b(i.b),n(i.n) { dassert(a <= b); }
inline bool Interval::operator < (const Interval &i2 ) const { return b < i2.a; }
inline bool Interval::operator > (const Interval &i2 ) const { return a > i2.b; }
inline bool Interval::operator == (const Interval &i2 ) const { return ( b >= i2.a && a <= i2.b); }
inline void Interval::print() const {
  if (a == LI_MIN) cout << "( -inf, "; else cout << "[ " << a << ", ";
  if (b == LI_MAX) cout << "inf )" << endl; else cout << b << " ]" << endl;
}

#endif /* _INTERVAL_ */
