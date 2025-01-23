#ifndef __CIRCUIT_G_H__
#define __CIRCUIT_G_H__
#include "core/propagator.h"
#include "circuit/NNF.h"

// nnfdecomp.c
//void nnf_decomp(NNF r, vec<BoolView>& xs);
void nnf_decomp(vec<IntVar*>& xs, FDNNF r);
void nnf_decompGAC(vec<IntVar*>& xs, FDNNF r);
#endif
