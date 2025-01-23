#if 0
#include "vtree.h"

VTree buildVTree(VTMerger& merger, int nvars)
{
  VTree vt(nvars);
  
  // Apply the merger to nodes 0..n-1.
  std::vector<int>& nodeQ = vt.nodeQ;
  int out_off = merger(vt, nodeQ, 0, nodeQ.size(), 0);

  assert( out_off == 1 );

  vt.root = nodeQ[0];
  nodeQ.clear();

  return vt;
}
#endif
