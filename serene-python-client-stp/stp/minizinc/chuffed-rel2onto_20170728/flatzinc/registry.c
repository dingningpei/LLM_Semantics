/*
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include "flatzinc/flatzinc.h"
#include "core/engine.h"
#include "core/propagator.h"
#include "ldsb/ldsb.h"
#include "globals/mddglobals.h"
#include "mdd/opts.h"
#include "mdd/MDD.h"
#include "mdd/wmdd_prop.h"
#include "mdd/mdd_to_lgraph.h"


namespace FlatZinc {

	Registry& registry(void) {
		static Registry r;
		return r;
	}

	void Registry::post(const ConExpr& ce, AST::Node* ann) {
		std::map<std::string,poster>::iterator i = r.find(ce.id);
		if (i == r.end()) {
			throw FlatZinc::Error("Registry",
				std::string("Constraint ")+ce.id+" not found");
		}
		i->second(ce, ann);
	}

	void Registry::add(const std::string& id, poster p) { r[id] = p;	}


	namespace {

		ConLevel ann2icl(AST::Node* ann) {
			if (ann) {
				if (ann->hasAtom("val")) return CL_VAL;
				if (ann->hasAtom("bounds") ||
						ann->hasAtom("boundsR") ||
						ann->hasAtom("boundsD") ||
						ann->hasAtom("boundsZ")) return CL_BND;
				if (ann->hasAtom("domain"))	return CL_DOM;
			}
			return CL_DEF;
		}

		inline void arg2intargs(vec<int>& ia, AST::Node* arg) {
			AST::Array* a = arg->getArray();
			ia.growTo(a->a.size());
			for (int i=a->a.size(); i--;) ia[i] = a->a[i]->getInt();
		}

		inline void arg2boolargs(vec<bool>& ia, AST::Node* arg) {
			AST::Array* a = arg->getArray();
			ia.growTo(a->a.size());
			for (int i=a->a.size(); i--;) ia[i] = a->a[i]->getBool();
		}

		inline void arg2intvarargs(vec<IntVar*>& ia, AST::Node* arg) {
			AST::Array* a = arg->getArray();
			ia.growTo(a->a.size());
			for (int i=a->a.size(); i--;) {
				if (a->a[i]->isIntVar()) {
					ia[i] = s->iv[a->a[i]->getIntVar()];
				} else {
					int value = a->a[i]->getInt();
					ia[i] = getConstant(value);
				}
			}
		}

		inline void arg2BoolVarArgs(vec<BoolView>& ia, AST::Node* arg) {
			AST::Array* a = arg->getArray();
			ia.growTo(a->a.size());
			for (int i=a->a.size(); i--;) {
				if (a->a[i]->isBoolVar()) {
					ia[i] = s->bv[a->a[i]->getBoolVar()];
				} else {
					bool value = a->a[i]->getBool();
					ia[i] = newBoolVar(value, value);
				}
			}
		}

    inline MDDOpts getMDDOpts(AST::Node* ann)
    {
      MDDOpts mopts;
      if(ann)
      {
        if(ann->hasCall("mdd"))
        {
          AST::Array* args(ann->getCall("mdd")->getArray());
          for(unsigned int i = 0; i < args->a.size(); i++)
          {
            if (AST::Atom* at = dynamic_cast<AST::Atom*>(args->a[i]))
              mopts.parse_arg(at->id);
          }
        }
      }
      return mopts;      
    }

		BoolView getBoolVar(AST::Node* n) {
			if (n->isBoolVar()) {
				return s->bv[n->getBoolVar()];
			}	else {
				return newBoolVar(n->getBool(), n->getBool());
			}
		}

		IntVar* getIntVar(AST::Node* n) {
			IntVar* x0;
			if (n->isIntVar()) {
				x0 = s->iv[n->getIntVar()];
			} else {
				x0 = getConstant(n->getInt());
			}
			return x0;
		}

		void p_int_CMP(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			if (ce[0]->isIntVar()) {
				if (ce[1]->isIntVar()) {
					int_rel(getIntVar(ce[0]), irt, getIntVar(ce[1]));
				} else {
					int_rel(getIntVar(ce[0]), irt, ce[1]->getInt());
				}
			} else {
				int_rel(getIntVar(ce[1]), -irt, ce[0]->getInt());
			}
		}
		void p_int_eq(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_EQ, ce, ann);
		}
		void p_int_ne(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_NE, ce, ann);
		}
		void p_int_ge(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_GE, ce, ann);
		}
		void p_int_gt(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_GT, ce, ann);
		}
		void p_int_le(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_LE, ce, ann);
		}
		void p_int_lt(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP(IRT_LT, ce, ann);
		}

		void p_int_CMP_reif(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			if (ce[2]->isBool()) {
				if (ce[2]->getBool()) {
					p_int_CMP(irt, ce, ann);
				} else {
					p_int_CMP(!irt, ce, ann);
				}
				return;
			}
			if (ce[0]->isIntVar()) {
				if (ce[1]->isIntVar()) {
					int_rel_reif(getIntVar(ce[0]), irt, getIntVar(ce[1]), getBoolVar(ce[2]));
				} else {
					int_rel_reif(getIntVar(ce[0]), irt, ce[1]->getInt(), getBoolVar(ce[2]));
				}
			} else {
				int_rel_reif(getIntVar(ce[1]), -irt, ce[0]->getInt(), getBoolVar(ce[2]));
			}
		}

		/* Comparisons */
		void p_int_eq_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_EQ, ce, ann);
		}
		void p_int_ne_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_NE, ce, ann);
		}
		void p_int_ge_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_GE, ce, ann);
		}
		void p_int_gt_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_GT, ce, ann);
		}
		void p_int_le_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_LE, ce, ann);
		}
		void p_int_lt_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_CMP_reif(IRT_LT, ce, ann);
		}

		/* linear (in-)equations */
		void p_int_lin_CMP(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			vec<int> ia; arg2intargs(ia, ce[0]);
			vec<IntVar*> iv; arg2intvarargs(iv, ce[1]);

/*
			if (ann2icl(ann) == CL_DOM) {
				if (irt == IRT_EQ && iv.size() == 3) {
					int_linear_dom(ia, iv, ce[2]->getInt());
					return;
				}
				fprintf(stderr, "Ignoring consistency annotation on int_linear constraint\n");
			}
*/

			int_linear(ia, iv, irt, ce[2]->getInt(), bv_true);
		}
		void p_int_lin_CMP_reif(IntRelType irt,	const ConExpr& ce, AST::Node* ann) {
			if (ce[3]->isBool()) {
				if (ce[3]->getBool()) {
					p_int_lin_CMP(irt, ce, ann);
				} else {
					p_int_lin_CMP(!irt, ce, ann);
				}
				return;
			}
			vec<int> ia; arg2intargs(ia, ce[0]);
			vec<IntVar*> iv; arg2intvarargs(iv, ce[1]);
			int_linear(ia, iv, irt, ce[2]->getInt(), getBoolVar(ce[3]));
		}
		void p_int_lin_eq(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_EQ, ce, ann);
		}
		void p_int_lin_eq_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_EQ, ce, ann);
		}
		void p_int_lin_ne(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_NE, ce, ann);
		}
		void p_int_lin_ne_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_NE, ce, ann);
		}
		void p_int_lin_le(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_LE, ce, ann);
		}
		void p_int_lin_le_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_LE, ce, ann);
		}
		void p_int_lin_lt(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_LT, ce, ann);
		}
		void p_int_lin_lt_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_LT, ce, ann);
		}
		void p_int_lin_ge(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_GE, ce, ann);
		}
		void p_int_lin_ge_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_GE, ce, ann);
		}
		void p_int_lin_gt(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP(IRT_GT, ce, ann);
		}
		void p_int_lin_gt_reif(const ConExpr& ce, AST::Node* ann) {
			p_int_lin_CMP_reif(IRT_GT, ce, ann);
		}

		/* arithmetic constraints */

		// can specialise
		void p_int_plus(const ConExpr& ce, AST::Node* ann) {
			int_plus(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));
		}

		// can specialise
		void p_int_minus(const ConExpr& ce, AST::Node* ann) {
			int_minus(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));
		}

		// can specialise
		void p_int_times(const ConExpr& ce, AST::Node* ann) {
			int_times(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));    
		}
		// can specialise?
		void p_int_div(const ConExpr& ce, AST::Node* ann) {
			int_div(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));    
		}
		void p_int_mod(const ConExpr& ce, AST::Node* ann) {
			int_mod(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));    
		}

		void p_int_min(const ConExpr& ce, AST::Node* ann) {
			int_min(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));    
		}
		void p_int_max(const ConExpr& ce, AST::Node* ann) {
			int_max(getIntVar(ce[0]), getIntVar(ce[1]), getIntVar(ce[2]));    
		}
		void p_abs(const ConExpr& ce, AST::Node* ann) {
			int_abs(getIntVar(ce[0]), getIntVar(ce[1]));
		}
		// can specialise
		void p_int_negate(const ConExpr& ce, AST::Node* ann) {
			int_negate(getIntVar(ce[0]), getIntVar(ce[1]));
		}

		/* Boolean constraints */
		void p_bool_CMP(int brt, const ConExpr& ce, AST::Node* ann, int sz) {
			BoolView b1 = ce[0]->isBoolVar() ? getBoolVar(ce[0]) : bv_true;
			if (ce[0]->isBool()) {
				if (ce[0]->getBool()) {
					brt &= 0xaa; brt |= (brt>>1);
				} else {
					brt &= 0x55; brt |= (brt<<1);
				}
			}
			BoolView b2 = ce[1]->isBoolVar() ? getBoolVar(ce[1]) : bv_true;
			if (ce[1]->isBool()) {
				if (ce[1]->getBool()) {
					brt &= 0xcc; brt |= (brt>>2);
				} else {
					brt &= 0x33; brt |= (brt<<2);
				}
			}
			if (sz == 2) {
				bool_rel(b1, (BoolRelType) brt, b2);
				return;
			}
			BoolView b3 = ce[2]->isBoolVar() ? getBoolVar(ce[2]) : bv_true;
			if (ce[2]->isBool()) {
				if (ce[2]->getBool()) {
					brt &= 0xf0; brt |= (brt>>4);
				} else {
					brt &= 0x0f; brt |= (brt<<4);
				}
			}
			bool_rel(b1, (BoolRelType) brt, b2, b3);
		}

		void p_bool_and(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_AND, ce, ann, 3);
		}
		void p_bool_not(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_NOT, ce, ann, 2);
		}
		void p_bool_or(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_OR, ce, ann, 3);
		}
		void p_bool_xor(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_XOR, ce, ann, 3);
		}
		void p_bool_eq(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_EQ, ce, ann, 2);
		}
		void p_bool_eq_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_EQ_REIF, ce, ann, 3);
		}
		void p_bool_ne(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_NE, ce, ann, 2);
		}
		void p_bool_ne_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_NE_REIF, ce, ann, 3);
		}
		void p_bool_le(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_LE, ce, ann, 2);
		}
		void p_bool_le_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_LE_REIF, ce, ann, 3);
		}
		void p_bool_lt(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_LT, ce, ann, 2);
		}
		void p_bool_lt_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_LT_REIF, ce, ann, 3);
		}
		void p_bool_ge(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_GE, ce, ann, 2);
		}
		void p_bool_ge_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_GE_REIF, ce, ann, 3);
		}
		void p_bool_gt(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_GT, ce, ann, 2);
		}
		void p_bool_gt_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_GT_REIF, ce, ann, 3);
		}
		void p_bool_l_imp(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_L_IMPL, ce, ann, 3);
		}
		void p_bool_r_imp(const ConExpr& ce, AST::Node* ann) {
			p_bool_CMP(BRT_R_IMPL, ce, ann, 3);
		}

    void p_array_bool_and(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bv; arg2BoolVarArgs(bv, ce[0]);
			array_bool_and(bv, getBoolVar(ce[1]));
    }
    void p_array_bool_or(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bv; arg2BoolVarArgs(bv, ce[0]);
			array_bool_or(bv, getBoolVar(ce[1]));
    }

		// specialise?
		void p_array_bool_clause(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bvp; arg2BoolVarArgs(bvp, ce[0]);
			vec<BoolView> bvn; arg2BoolVarArgs(bvn, ce[1]);
			bool_clause(bvp, bvn);
		}
		// specialise?
		void p_array_bool_clause_reif(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bvp; arg2BoolVarArgs(bvp, ce[0]);
			vec<BoolView> bvn; arg2BoolVarArgs(bvn, ce[1]);
			BoolView b0 = getBoolVar(ce[2]);
			array_bool_or(bvp, bvn, b0);
		}


		/* element constraints */
		void p_array_int_element(const ConExpr& ce, AST::Node* ann) {
			vec<int> ia; arg2intargs(ia, ce[1]);
			IntVar* sel = getIntVar(ce[0]);
			int_rel(sel, IRT_GE, 1);
			int_rel(sel, IRT_LE, ia.size());
			array_int_element(sel, ia, getIntVar(ce[2]), 1);
		}
		void p_array_var_int_element(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv; arg2intvarargs(iv, ce[1]);
			IntVar* sel = getIntVar(ce[0]);
			int_rel(sel, IRT_GE, 1);
			int_rel(sel, IRT_LE, iv.size());
			if (ann2icl(ann) == CL_DOM) {
				array_var_int_element_dom(sel, iv, getIntVar(ce[2]), 1);
			} else {
				array_var_int_element_bound(sel, iv, getIntVar(ce[2]), 1);
			}
		}
		void p_array_bool_element(const ConExpr& ce, AST::Node* ann) {
			vec<bool> ba; arg2boolargs(ba, ce[1]);
			IntVar* sel = getIntVar(ce[0]);
			int_rel(sel, IRT_GE, 1);
			int_rel(sel, IRT_LE, ba.size());
			array_bool_element(sel, ba, getBoolVar(ce[2]), 1);
		}
		void p_array_var_bool_element(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bv; arg2BoolVarArgs(bv, ce[1]);
			IntVar* sel = getIntVar(ce[0]);
			int_rel(sel, IRT_GE, 1);
			int_rel(sel, IRT_LE, bv.size());
			array_var_bool_element(sel, bv, getBoolVar(ce[2]), 1);
		}

    void p_set_in(const ConExpr& ce, AST::Node *) {
			if (ce[1]->isSetVar()) ERROR("Cannot handle set vars\n");
      AST::SetLit* sl = ce[1]->getSet();
      if (ce[0]->isBoolVar()) {
        assert(sl->interval);
				BoolView v = getBoolVar(ce[0]);
				if (sl->min >= 1) if (!v.setVal(1)) TL_FAIL();
				if (sl->max <= 0) if (!v.setVal(0)) TL_FAIL();
				return;
			}
			IntVar* v = getIntVar(ce[0]);
      if (sl->interval) {
				int_rel(v, IRT_GE, sl->min);
				int_rel(v, IRT_LE, sl->max);
      } else {
				vec<int> is(sl->s.size());
				for (unsigned int i = 0; i < sl->s.size(); i++) is[i] = sl->s[i];
				if (!v->allowSet(is)) TL_FAIL();
      }
    }

    void p_set_in_reif(const ConExpr& ce, AST::Node *) {
			if (ce[1]->isSetVar()) ERROR("Cannot handle set vars\n");
			assert(ce[0]->isIntVar());
			assert(ce[2]->isBoolVar());
      AST::SetLit* sl = ce[1]->getSet();
			IntVar* v = getIntVar(ce[0]);
			BoolView r = getBoolVar(ce[2]);
      if (sl->interval) {
				BoolView r1 = newBoolVar();
				BoolView r2 = newBoolVar();
				int_rel_reif(v, IRT_GE, sl->min, r1);
				int_rel_reif(v, IRT_LE, sl->max, r2);
				bool_rel(r1, BRT_AND, r2, r);
      } else {
				vec<BoolView> rs;
				for (unsigned int i = 0; i < sl->s.size(); i++) {
					rs.push(newBoolVar());
					int_rel_reif(v, IRT_EQ, sl->s[i], rs.last());
				}
				array_bool_or(rs, r);
      }
    }


		/* coercion constraints */
		void p_bool2int(const ConExpr& ce, AST::Node* ann) {
			bool2int(getBoolVar(ce[0]), getIntVar(ce[1]));
		}

		/* constraints from the standard library */

		void p_all_different_int(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va; arg2intvarargs(va, ce[0]);
			all_different(va, ann2icl(ann));
		}

		void p_inverse_offsets(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> x; arg2intvarargs(x, ce[0]);
			vec<IntVar*> y; arg2intvarargs(y, ce[2]);
			inverse(x, y, ce[1]->getInt(), ce[3]->getInt(), ann2icl(ann));
		}

		void p_table_int(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> x; arg2intvarargs(x, ce[0]);
			vec<int> tuples; arg2intargs(tuples, ce[1]);
			int noOfVars = x.size();
			int noOfTuples = tuples.size()/noOfVars;
			vec<vec<int> > ts;
			for (int i=0; i<noOfTuples; i++) {
				ts.push();
				for (int j=0; j<x.size(); j++) {
					ts.last().push(tuples[i*noOfVars+j]);
				}
			}
			if (ann->hasAtom("mdd") || ann->hasCall("mdd"))
				mdd_table(x, ts, getMDDOpts(ann));
      else
				table(x, ts);
		}

		void p_regular(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv; arg2intvarargs(iv, ce[0]);
			int q = ce[1]->getInt();
			int s = ce[2]->getInt();
			vec<int> d_flat; arg2intargs(d_flat, ce[3]);
			int q0 = ce[4]->getInt();

			assert(d_flat.size() == q*s);

			vec<vec<int> > d;
			for (int i = 0; i < q; i++) {
				d.push();
				for (int j = 0; j < s; j++) {
					d.last().push(d_flat[i*s+j]);
				}
			}

			// Final states
			AST::SetLit* sl = ce[5]->getSet();
			vec<int> f;
			if (sl->interval) {
				for (int i = sl->min; i <= sl->max; i++) f.push(i);
			} else {
				for (unsigned int i = 0; i < sl->s.size(); i++) f.push(sl->s[i]);
			}
            
			if(ann->hasAtom("mdd"))
				mdd_regular(iv, q, s, d, q0, f, true, getMDDOpts(ann));
      else
				regular(iv, q, s, d, q0, f);
		}

		void p_disjunctive(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> s; arg2intvarargs(s, ce[0]);
			vec<int> d; arg2intargs(d, ce[1]);
			disjunctive(s, d);
		}

		void p_cumulative(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> s; arg2intvarargs(s, ce[0]);
			vec<int> d; arg2intargs(d, ce[1]);
			vec<int> p; arg2intargs(p, ce[2]);
			int limit = ce[3]->getInt();
			cumulative(s, d, p, limit);
		}

        void p_cumulative2(const ConExpr& ce, AST::Node* ann) {
            vec<IntVar*> s; arg2intvarargs(s, ce[0]);
            vec<IntVar*> d; arg2intvarargs(d, ce[1]);
            vec<IntVar*> r; arg2intvarargs(r, ce[2]);
            cumulative2(s, d, r, getIntVar(ce[3]));
        }

		void p_minimum(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv; arg2intvarargs(iv, ce[1]);
			minimum(iv, getIntVar(ce[0]));
		}

		void p_maximum(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv; arg2intvarargs(iv, ce[1]);
			maximum(iv, getIntVar(ce[0]));
		}

    void p_lex_less(const ConExpr& ce, AST::Node* ann) {
      vec<IntVar*> iv0; arg2intvarargs(iv0, ce[0]);
      vec<IntVar*> iv1; arg2intvarargs(iv1, ce[1]);
      lex(iv0, iv1, true);
    }

    void p_lex_lesseq( const ConExpr& ce, AST::Node* ann) {
      vec<IntVar*> iv0; arg2intvarargs(iv0, ce[0]);
      vec<IntVar*> iv1; arg2intvarargs(iv1, ce[1]);
      lex(iv0, iv1, false);
    }
  
		void var_sym( const ConExpr& ce, AST::Node* ann) {
      vec<IntVar*> iv0; arg2intvarargs(iv0, ce[0]);
			var_sym_ldsb(iv0);
		}

		void val_sym( const ConExpr& ce, AST::Node* ann) {
      vec<IntVar*> iv0; arg2intvarargs(iv0, ce[0]);
			val_sym_ldsb(iv0, ce[1]->getInt(), ce[2]->getInt());
		}

		void var_seq_sym( const ConExpr& ce, AST::Node* ann) {
      vec<IntVar*> iv0; arg2intvarargs(iv0, ce[2]);
			var_seq_sym_ldsb(ce[0]->getInt(), ce[1]->getInt(), iv0);
		}

		void val_seq_sym( const ConExpr& ce, AST::Node* ann) {
			NOT_SUPPORTED;
		}

		void p_bool_sum_CMP(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> bv; arg2BoolVarArgs(bv, ce[0]);
			bool_linear(bv, irt, getIntVar(ce[1]));
		}
		void p_bool_sum_eq(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_EQ, ce, ann);
		}
		void p_bool_sum_ne(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_NE, ce, ann);
		}
		void p_bool_sum_le(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_LE, ce, ann);
		}
		void p_bool_sum_lt(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_LT, ce, ann);
		}
		void p_bool_sum_ge(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_GE, ce, ann);
		}
		void p_bool_sum_gt(const ConExpr& ce, AST::Node* ann) {
			p_bool_sum_CMP(IRT_GT, ce, ann);
		}



                void p_tree(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }

                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }
                    tree(vs,es,ad,en);
                }

                void p_steinerTree(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    IntVar* w = getIntVar(ce[4]);
                    vec< int > ws; arg2intargs(ws,ce[5]);

                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }

                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }


                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }

                    steinerTree(vs,es,ad,en,w,ws);
                }


                void p_bicconected(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }

                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }
                    biconnected(vs,es,en,ad);
                }

                void p_wbicconected(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }

                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }
                    vec< int > ws; arg2intargs(ws,ce[4]);
                    IntVar* w = getIntVar(ce[5]);

                    wbiconnected(vs,es,en,ad,ws,w);
                }

                void p_vrptw(const ConExpr& ce, AST::Node* ann) {
                    
                    vec< BoolView> b_flat; arg2BoolVarArgs(b_flat, ce[0]);
                    vec<IntVar*> bW; arg2intvarargs(bW,ce[1]);
                    vec<int> t; arg2intargs(t,ce[2]);
                    vec<int> s; arg2intargs(s,ce[3]);
                    vec<int> e; arg2intargs(e,ce[4]);
                    vec<int> d; arg2intargs(d,ce[5]);


                    vrptw(b_flat,bW,t,s,e,d);
                    
                }

                void p_tsp(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }



                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }

                    IntVar* w = getIntVar(ce[4]);
                    vec< int > ws; arg2intargs(ws,ce[5]);
                    tsp(vs,es,ad,en,w,ws);
                }

                void p_mst(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }



                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }

                    IntVar* w = getIntVar(ce[4]);
                    vec< int > ws; arg2intargs(ws,ce[5]);
                    mst(vs,es,ad,en,w,ws);
                }

                void p_cmst(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    vec< bool > ad_flat; arg2boolargs(ad_flat, ce[2]);
                    assert(ad_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ad;
                    for (int i = 0; i < vs.size(); i++) {
                        ad.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ad_flat[i*es.size()+j])
                                ad[i].push(j);
                        }
                    }
                    vec< int > en_flat; 
                    try {
                        vec< bool > en_flat_b; 
                        arg2boolargs(en_flat_b, ce[3]);
                        for (int i = 0; i < en_flat_b.size(); i++) {
                            en_flat.push(en_flat_b[i]? 1:0);
                        }
                    } catch(FlatZinc::AST::TypeError& e) {
                        arg2intargs(en_flat, ce[3]);
                    }


                    vec<vec<int> > en;

                    if(en_flat.size() == es.size()*vs.size()) {
                        //Old format!
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            int check = 0;
                            for (int j = 0; j < vs.size(); j++) {
                                if  (en_flat[i*vs.size()+j]){
                                    en[i].push(j);
                                }
                            }
                            if (en[i].size() == 1) //Self loops
                                en[i].push(en[i][0]);
                        }
                    } else if (en_flat.size() == es.size()*2) {
                        //New format
                        for (int i = 0; i < es.size(); i++) {
                            en.push(vec<int>());
                            // The -1 is becaise indexes in MZ start at 1
                            en[i].push(en_flat[i] - 1);
                            en[i].push(en_flat[es.size()+i] - 1);
                        }
                    }
                    IntVar* w = getIntVar(ce[4]);
                    vec< int > ws; arg2intargs(ws,ce[5]);

                    int r = ce[6]->getInt();
                    int c = ce[7]->getInt();
                    cmst(vs,es,ad,en,w,ws,r,c);
                }



                void p_dag(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    int from = ce[2]->getInt() - 1;



                    vec< bool > in_flat; arg2boolargs(in_flat, ce[3]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[4]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j])
                                ou[i].push(j);
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[5]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is because indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }

                    dag(from, vs, es, in, ou, en);
                }


                void p_dreachable(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    int from = ce[2]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[3]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[4]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j])
                                ou[i].push(j);
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[5]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }

                    dreachable(from, vs, es, in, ou, en);
                }

                void p_dreachable_reif(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    int from = ce[2]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[3]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[4]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j])
                                ou[i].push(j);
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[5]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }
                    BoolView b = getBoolVar(ce[6]);
                    dreachable(from, vs, es, in, ou, en, b);
                }




                void p_path(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    int from = ce[2]->getInt() - 1;
                    int to = ce[3]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[4]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[5]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j])
                                ou[i].push(j);
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[6]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }

                    path(from, to, vs, es, in, ou, en);
                }


                void p_pathsucc(const ConExpr& ce, AST::Node* ann) {
                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);
                    int from = ce[2]->getInt() - 1;
                    int to = ce[3]->getInt() - 1;
                    vec<IntVar*> succ; arg2intvarargs(succ,ce[4]);

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[5]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[6]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j])
                                ou[i].push(j);
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[7]);

                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }
                    pathsucc(from, to, vs, es, succ, in, ou, en);
                    //path(from, to, vs, es, in, ou, en);

                }



                void p_bounded_path(const ConExpr& ce, AST::Node* ann) {

                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    int from = ce[2]->getInt() - 1;
                    int to = ce[3]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[4]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[5]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j]) {
                                ou[i].push(j);
                            }
                        }
                    }
                    cout <<endl;
                    vec< int > en_flat; arg2intargs(en_flat, ce[6]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }
                    vec< int > ws; arg2intargs(ws,ce[7]);
                    IntVar* w = getIntVar(ce[8]);


                    vec<int> ds; 
                    for (int i = 0; i < vs.size(); i++)
                        ds.push(0);

                    vec<vec<int> > ws2;
                    for (int i = 0; i < ws.size(); i++) {
                        ws2.push(vec<int>());
                        for (int j = 0; j < 100; j++) {
                            ws2[ws2.size()-1].push(ws[i]);
                        }
                    }

                    //vec<IntVar*> lowers;
                    //vec<IntVar*> uppers;
                    //vec<BoolView> b4_flat;
                    //vec<IntVar*> pos;
                    //createVars(lowers,vs.size(),0,w->getMax()+1);
                    //createVars(uppers,vs.size(),-1,w->getMax());

                    bounded_path(from, to, vs, es,               in, ou, en, ws, w);
                    //td_bounded_path(from, to, vs, es, b4_flat, b4_flat, pos, in, ou, en, ws2, ds, w);//, lowers, uppers);

                }


                void p_td_bounded_path_basic(const ConExpr& ce, AST::Node* ann) {

                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    int from = ce[2]->getInt() - 1;
                    int to = ce[3]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[4]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }

                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[5]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j]) {
                                ou[i].push(j);
                            }
                        }
                    }
                    vec< int > en_flat; arg2intargs(en_flat, ce[6]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }
                    IntVar* w = getIntVar(ce[9]);

                    vec< int > ws_flat; arg2intargs(ws_flat,ce[7]);
                    int frames = ws_flat.size()/es.size();
                    vec<vec<int> > ws;
                    for (int i = 0; i < es.size(); i++) {
                        ws.push(vec<int>());
                        for (int j = 0; j < frames; j++) {
                            ws[i].push(ws_flat[i*frames + j]);
                        }
                    }


                    vec<int> ds; 
                    for (int i = 0; i < vs.size(); i++)
                        ds.push(0);


                    //vec<IntVar*> lowers;
                    //vec<IntVar*> uppers;
                    vec<BoolView> b4_flat;
                    vec<IntVar*> pos;
                    //createVars(lowers,vs.size(),0,w->getMax()+1);
                    //createVars(uppers,vs.size(),-1,w->getMax());

                    //bounded_path(from, to, vs, es,               in, ou, en, ws, w);
                    td_bounded_path(from, to, vs, es, b4_flat, b4_flat, pos, in, ou, en, ws, ds, w);//, lowers, uppers);

                }



                void p_td_bounded_path(const ConExpr& ce, AST::Node* ann) {

                    vec< BoolView > vs; arg2BoolVarArgs(vs, ce[0]);
                    vec< BoolView > es; arg2BoolVarArgs(es, ce[1]);

                    vec< BoolView> b4_flat; arg2BoolVarArgs(b4_flat, ce[2]);
                    vec< BoolView> mb4_flat; arg2BoolVarArgs(mb4_flat, ce[3]);
                    vec<IntVar*> pos; arg2intvarargs(pos, ce[4]);

                    int from = ce[5]->getInt() - 1;
                    int to = ce[6]->getInt() - 1;

                    vec< bool > in_flat; arg2boolargs(in_flat, ce[7]);
                    assert(in_flat.size() == vs.size()*es.size());
                    vec<vec<int> > in;
                    for (int i = 0; i < vs.size(); i++) {
                        in.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (in_flat[i*es.size()+j])
                                in[i].push(j);
                        }
                    }
                    vec< bool > ou_flat; arg2boolargs(ou_flat, ce[8]);
                    assert(ou_flat.size() == vs.size()*es.size());
                    vec<vec<int> > ou;
                    for (int i = 0; i < vs.size(); i++) {
                        ou.push(vec<int>());
                        for (int j = 0; j < es.size(); j++) {
                            if  (ou_flat[i*es.size()+j]) {
                                ou[i].push(j);
                            }
                        }
                    }
                    cout <<endl;
                    vec< int > en_flat; arg2intargs(en_flat, ce[9]);
                    //assert(en_flat.size() == es.size()*vs.size());
                    assert(en_flat.size() == es.size()*2);
                    vec<vec<int> > en;
                    for (int i = 0; i < es.size(); i++) {
                        en.push(vec<int>());
                        // The -1 is becaise indexes in MZ start at 1
                        en[i].push(en_flat[i] - 1);
                        en[i].push(en_flat[es.size()+i] - 1);
                    }


                    vec< int > ws_flat; arg2intargs(ws_flat,ce[10]);
                    int frames = ws_flat.size()/es.size();
                    vec<vec<int> > ws;
                    for (int i = 0; i < es.size(); i++) {
                        ws.push(vec<int>());
                        for (int j = 0; j < frames; j++) {
                            ws[i].push(ws_flat[i*frames + j]);
                        }
                    }
                    vec< int > ds; arg2intargs(ds,ce[11]);
                    IntVar* w = getIntVar(ce[12]);


                    //vec<IntVar*> lowers;
                    //vec<IntVar*> uppers;
                    //vec<BoolView> b4_flat;
                    //vec<IntVar*> pos;
                    //createVars(lowers,vs.size(),0,w->getMax()+1);
                    //createVars(uppers,vs.size(),-1,w->getMax());


                    //td_bounded_path(from, to, vs, es, b4_flat, pos, in, ou, en, ws, ds, w, lowers, uppers);
                    //return;

                    int count  = ce.args->a.size();
                    if (count == 15) {
                        vec<IntVar*> l; arg2intvarargs(l,ce[13]);
                        vec<IntVar*> u; arg2intvarargs(u,ce[14]);
                        //td_bounded_path(from, to, vs, es, b4_flat, pos, in, ou, en, ws, ds, w);
                        td_bounded_path(from, to, vs, es, b4_flat, mb4_flat, pos, in, ou, en, ws, ds, w, l,u);
                    } else {
                        td_bounded_path(from, to, vs, es, b4_flat, mb4_flat, pos, in, ou, en, ws, ds, w);
                    }

                }




                //FROM KATHERYN'S BRANCH:
                void p_circuit_int_kf(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va; arg2intvarargs(va, ce[0]);
			circuit_kf(va);
		}	       		
		void p_path_int_kf(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va; arg2intvarargs(va, ce[0]);
			path_kf(va);
		}
		void p_subcircuit_int_kf(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va; arg2intvarargs(va, ce[0]);
			subcircuit_kf(va);
		}		
		void p_subpath_int_kf(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va; arg2intvarargs(va, ce[0]);
			subpath_kf(va);
		}




                //For MDD's
                void p_mdd(const ConExpr& ce, AST::Node* ann) {

                    MDD mdd;
                    MDDOpts o;
                    vec< IntVar* > iv; arg2intvarargs(iv, ce[0]);
                    vec< int > s; arg2intargs(s,ce[1]);
                    if (iv.size() != s.size()) {
                        fprintf(stderr,"Problem parsing MDD constriant: wrong number of variables/shifts\n");
                        exit(1);
                    }
                    vec<IntView<4> > views;
                    for (int i = 0; i < iv.size(); i++) 
                        views.push(IntView<4>(iv[i],1,s[i]));
                    int n = ce[2]->getInt();
                    vec< int > ll; arg2intargs(ll,ce[3]); //layer length
                    vec< int > edges; arg2intargs(edges,ce[4]);
                    MDDTable* tab = new MDDTable(views.size());             
                    _MDD node = MDDTRUE;

                    std::unordered_map<int,std::vector<std::pair<int,int> > > nedges;
                    std::unordered_map<int,int> node2var;
                    node2var[2] = 0;
                    int cl = 0, var = 0, c = 2;
                    for (int i = 2; i < edges.size(); i+=2) {
                        int val = edges[i]; 
                        int dest = edges[i+1];
                        if (val == -1) {
                            node2var[c] = var;
                            cl++;
                            if (cl == ll[var]) {
                                cl = 0; var++;
                            }
                            c++;
                        } else {
                            nedges[c].push_back(std::make_pair(val,dest));
                        }
                    }
                    node2var[c] = var;

                    std::unordered_map<int,_MDD> old2new;
                    old2new[0] = 0;
                    old2new[1] = 1;
                    for (int i = c; i >= 2; i--) {        
                        _MDD old = i;
                        std::vector<std::pair<int,int> >& e = nedges[old];
                        std::vector<edgepair> edges;
                        int var = node2var[old];
                        for (int j = 0; j < e.size(); j++) {
                            edges.push_back(std::make_pair(e[j].first,old2new[e[j].second]));
                            for (int k = e[j].first+1; j < e.size() - 1 && k < e[j+1].first; k++) {
                                edges.push_back(std::make_pair(k,old2new[e[j].second]));
                            }
                        }
                        node = tab->mdd_case(node2var[old],edges);
                        old2new[old] = node;
                    }  

                    mdd.table = tab;
                    mdd.val = node;

                    /*For DEBUGGING
                    int key = engine.loaded_mdds.size();
                    engine.loaded_mdds[key] = mdd;
                    key = engine.mddfied_variables.size();
                    for (int i = 0; i < iv.size(); i++)
                        engine.mddfied_variables[key].push_back(iv[i]); 
                    //*/
                    // { D_PROP, D_MINIMAL, D_MINISAT, D_TSEITIN, D_BASIC, 
                    //   D_SDNNF , D_LEVEL, D_COMPLETE}
                    if (so.mdd_prop_type < 0 || so.mdd_prop_type > MDDOpts::D_COMPLETE)
                        o.decomp = MDDOpts::D_PROP;
                    else
                        o.decomp = (MDDOpts::Decomp)so.mdd_prop_type; //Default is D_PROP
                    addMDD(views, mdd,o);
                }


                //For MDD's
                //*
                  void p_wmdd(const ConExpr& ce, AST::Node* ann) {

                    MDDOpts o;
                    vec< IntVar* > iv; arg2intvarargs(iv, ce[0]);
                    vec< int > s; arg2intargs(s,ce[1]);
                    if (iv.size() != s.size()) {
                        fprintf(stderr,"Problem parsing MDD constriant: wrong number of variables/shifts\n");
                        exit(1);
                    }
                    vec<IntView<> > views;
                    for (int i = 0; i < iv.size(); i++) {
                        views.push(IntView<>(iv[i],1,s[i]));
                        iv[i]->specialiseToEL();
                    }
                    int n = ce[2]->getInt() - 1; //Node FFF is not counted in WMDD
                    vec< int > ll; arg2intargs(ll,ce[3]); //layer length
                    vec< int > edges; arg2intargs(edges,ce[4]);
                    vec< int > var_ids;  arg2intargs(var_ids,ce[5]); //values 1 to max
                    vec< int > var_vals;  arg2intargs(var_vals,ce[6]);
                    vec< int > var_cost;  arg2intargs(var_cost,ce[7]);
                    std::vector< std::unordered_map< int, int > > vvc(var_ids.size() + 1);
                    for (int i = 0; i < var_ids.size(); i++) {
                        vvc[var_ids[i]][var_vals[i]] = var_cost[i];
                    }
                    IntVar* cost_var = getIntVar(ce[8]);
                    cost_var->specialiseToEL();
                    IntView<> cost(cost_var);


                    std::unordered_map<int,std::vector<std::pair<int,int> > > nedges;
                    std::unordered_map<int,int> node2var;
                    node2var[2] = 0;
                    int cl = 0, var = 0, c = 2;
                    for (int i = 2; i < edges.size(); i+=2) {
                        int val = edges[i]; 
                        int dest = edges[i+1];
                        if (val == -1) {
                            node2var[c] = var;
                            cl++;
                            if (cl == ll[var]) {
                                cl = 0; var++;
                            }
                            c++;
                        } else {
                            nedges[c].push_back(std::make_pair(val,dest));
                        }
                    }
                    node2var[c] = var;
                    vec<int> level;
                    for (int i = 0; i < n; i++)  level.push(0);
                    vec< Edge > all_edges;
                    for (int i = c; i >= 2; i--) {        
                        _MDD old = i;
                        std::vector<std::pair<int,int> >& e = nedges[old];
                        int var = node2var[old];
                        level[i - 1] = var;
                        //printf("Level[%d] = %d\n",i-1,var);
                        for (int j = 0; j < e.size(); j++) {
                            if (e[j].second == 0) continue;
                            //printf("Edge: %d --%d(%d)--> %d\n",i-1,e[j].first,vvc[var+1][e[j].first],e[j].second -1);
                            Edge xx = {
                                e[j].first,
                                vvc[var+1][e[j].first],
                                i - 1,  //WMDDPROP: root is 1 instead of 2
                                e[j].second - 1 
                            };
                            all_edges.push(xx);
                            for (int k = e[j].first+1; j < e.size() - 1 && k < e[j+1].first; k++) {
                                //printf("Edge: %d ==%d(%d)==> %d\n",i-1,k,vvc[var+1][k],e[j].second -1);
                                Edge xx = {
                                    k,
                                    vvc[var+1][k],
                                    i - 1,  //WMDDPROP: root is 1 instead of 2
                                    e[j].second - 1 
                                };
                                all_edges.push(xx);
                            }
                        }
                    }  

                    new WMDDProp(views, cost, level, all_edges, o);

                }
                //*/
            /*
            void p_wmdd(const ConExpr& ce, AST::Node* ann) {

                    MDD mdd;
                    MDDOpts o;
                    vec< IntVar* > iv; arg2intvarargs(iv, ce[0]);
                    vec< int > s; arg2intargs(s,ce[1]);
                    if (iv.size() != s.size()) {
                        fprintf(stderr,"Problem parsing MDD constriant: wrong number of variables/shifts\n");
                        exit(1);
                    }
                    vec<IntView<4> > views;
                    for (int i = 0; i < iv.size(); i++) 
                        views.push(IntView<4>(iv[i],1,s[i]));
                    int n = ce[2]->getInt();
                    vec< int > ll; arg2intargs(ll,ce[3]); //layer length
                    vec< int > edges; arg2intargs(edges,ce[4]);
                    MDDTable* tab = new MDDTable(views.size());             
                    _MDD node = MDDTRUE;

                    std::unordered_map<int,std::vector<std::pair<int,int> > > nedges;
                    std::unordered_map<int,int> node2var;
                    node2var[2] = 0;
                    int cl = 0, var = 0, c = 2;
                    for (int i = 2; i < edges.size(); i+=2) {
                        int val = edges[i]; 
                        int dest = edges[i+1];
                        if (val == -1) {
                            node2var[c] = var;
                            cl++;
                            if (cl == ll[var]) {
                                cl = 0; var++;
                            }
                            c++;
                        } else {
                            nedges[c].push_back(std::make_pair(val,dest));
                        }
                    }
                    node2var[c] = var;

                    std::unordered_map<int,_MDD> old2new;
                    old2new[0] = 0;
                    old2new[1] = 1;
                    for (int i = c; i >= 2; i--) {        
                        _MDD old = i;
                        std::vector<std::pair<int,int> >& e = nedges[old];
                        std::vector<edgepair> edges;
                        int var = node2var[old];
                        for (int j = 0; j < e.size(); j++) {
                            edges.push_back(std::make_pair(e[j].first,old2new[e[j].second]));
                            for (int k = e[j].first+1; j < e.size() - 1 && k < e[j+1].first; k++) {
                                edges.push_back(std::make_pair(k,old2new[e[j].second]));
                            }
                        }
                        node = tab->mdd_case(node2var[old],edges);
                        old2new[old] = node;
                    }  

                    mdd.table = tab;
                    mdd.val = node;

                    //addMDD(views,mdd,o);
                    //return;
                    //mdd.table->print_mdd(mdd.val);
                    vec< int > var_ids;  arg2intargs(var_ids,ce[5]); //values 1 to max
                    vec< int > var_vals;  arg2intargs(var_vals,ce[6]);
                    vec< int > var_cost;  arg2intargs(var_cost,ce[7]);

                    EVLayerGraph evlg;
                    vec< vec<int> > present;
                    for (int i = 0; i < iv.size(); i++) {
                        present.push();
                        for (int j = 0; j < iv[i]->getMax(); j++)
                            present.last().push(0);
                    }
                    for (int i = 0; i < var_ids.size(); i++) {
                        int var = var_ids[i];
                        int val = var_vals[i];
                        int cost = var_cost[i];
                        //printf("%d %d %d\n",var,val,cost);
                        if (var-1 >= present.size()) {
                            ERROR("Wrong call to wmdd \n");
                        }
                        if (val < present[var-1].size())
                            present[var-1][val] = cost;
                    }
                    printf("Costs\n");
                    for (int i = 0; i < present.size(); i++) {
                        printf("%d: ",i);
                        for (int j = 0; j < present[i].size(); j++) {
                            printf("%d ",present[i][j]);
                        }       
                        printf("\n");
                    }
                    
                    EVLayerGraph::NodeID root = mdd_to_layergraph(evlg, mdd, present);
                    IntVar* cost_var = getIntVar(ce[8]);
                    cost_var->specialiseToEL();
                    printf("Domain %d %d\n",cost_var->getMin(), cost_var->getMax());
                    evgraph_to_wmdd(iv,cost_var,evlg,root,o);
                    printf("Domain %d %d\n",cost_var->getMin(), cost_var->getMax());
                
            }
            //*/

/*
		void p_bool_lin_CMP(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			vec<int> ia; arg2intargs(ia, ce[0]);
			vec<BoolVar*> bv; arg2BoolVarArgs(bv, ce[1]);
			if (ce[2]->isIntVar())
				bool_linear(bv, irt, s->iv[ce[2]->getIntVar()]);
			else
				bool_linear(bv, irt, ce[2]->getInt());
		}
		void p_bool_lin_CMP_reif(IntRelType irt, const ConExpr& ce, AST::Node* ann) {
			if (ce[2]->isBool()) {
				if (ce[2]->getBool()) {
					p_bool_lin_CMP(irt, ce, ann);
				} else {
					p_bool_lin_CMP(neg(irt), ce, ann);
				}
				return;
			}
			IntArgs ia = arg2intargs(ce[0]);
			vec<BoolView> iv = arg2BoolVarArgs(ce[1]);
			if (ce[2]->isIntVar())
				linear(ia, iv, irt, iv[ce[2]->getIntVar()], getBoolVar(ce[3]), 
							 ann2icl(ann));
			else
				linear(ia, iv, irt, ce[2]->getInt(), getBoolVar(ce[3]), 
							 ann2icl(ann));
		}
		void p_bool_lin_eq(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_EQ, ce, ann);
		}
		void p_bool_lin_eq_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_EQ, ce, ann);
		}
		void p_bool_lin_ne(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_NE, ce, ann);
		}
		void p_bool_lin_ne_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_NE, ce, ann);
		}
		void p_bool_lin_le(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_LE, ce, ann);
		}
		void p_bool_lin_le_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_LE, ce, ann);
		}
		void p_bool_lin_lt(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_LT, ce, ann);
		}
		void p_bool_lin_lt_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_LT, ce, ann);
		}
		void p_bool_lin_ge(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_GE, ce, ann);
		}
		void p_bool_lin_ge_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_GE, ce, ann);
		}
		void p_bool_lin_gt(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP(IRT_GT, ce, ann);
		}
		void p_bool_lin_gt_reif(const ConExpr& ce, AST::Node* ann) {
			p_bool_lin_CMP_reif(IRT_GT, ce, ann);
		}
*/


/*

		void p_distinctOffset(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> va = arg2intvarargs(ce[1]);
			AST::Array* offs = ce.args->a[0]->getArray();
			IntArgs oa(offs->a.size());
			for (int i=offs->a.size(); i--; ) {
				oa[i] = offs->a[i]->getInt();    
			}
			distinct(oa, va, ann2icl(ann));
		}

		void p_count(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv = arg2intvarargs(ce[0]);
			if (!ce[1]->isIntVar()) {
				if (!ce[2]->isIntVar()) {
					count(iv, ce[1]->getInt(), IRT_EQ, ce[2]->getInt(), 
								ann2icl(ann));
				} else {
					count(iv, ce[1]->getInt(), IRT_EQ, getIntVar(ce[2]), 
								ann2icl(ann));
				}
			} else if (!ce[2]->isIntVar()) {
				count(iv, getIntVar(ce[1]), IRT_EQ, ce[2]->getInt(), 
							ann2icl(ann));
			} else {
				count(iv, getIntVar(ce[1]), IRT_EQ, getIntVar(ce[2]), 
							ann2icl(ann));
			}
		}

		void count_rel(IntRelType irt,
									 FlatZincSpace& s, const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> iv = arg2intvarargs(ce[1]);
			count(iv, ce[2]->getInt(), irt, ce[0]->getInt(), ann2icl(ann));
		}

		void p_at_most(const ConExpr& ce, AST::Node* ann) {
			count_rel(IRT_LE, s, ce, ann);
		}

		void p_at_least(const ConExpr& ce, AST::Node* ann) {
			count_rel(IRT_GE, s, ce, ann);
		}

		void p_global_cardinality(const ConExpr& ce,
															AST::Node* ann) {
			vec<IntVar*> iv0 = arg2intvarargs(ce[0]);
			vec<IntVar*> iv1 = arg2intvarargs(ce[1]);
			int cmin = ce[2]->getInt();
			if (cmin == 0) {
				count(iv0, iv1, ann2icl(ann));      
			} else {
				IntArgs values(iv1.size());
				for (int i=values.size(); i--;)
					values[i] = i+cmin;
				count(iv0, iv1, values, ann2icl(ann));
			}
		}

		void
		p_sort(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> x = arg2intvarargs(ce[0]);
			vec<IntVar*> y = arg2intvarargs(ce[1]);
			vec<IntVar*> xy(x.size()+y.size());
			for (int i=x.size(); i--;)
				xy[i] = x[i];
			for (int i=y.size(); i--;)
				xy[i+x.size()] = y[i];
			unshare(xy);
			for (int i=x.size(); i--;)
				x[i] = xy[i];
			for (int i=y.size(); i--;)
				y[i] = xy[i+x.size()];
			sorted(x, y, ann2icl(ann));
		}

		void
		p_increasing_int(const ConExpr& ce, AST::Node* ann) {
			vec<IntVar*> x = arg2intvarargs(ce[0]);
			rel(s,x,IRT_LE,ann2icl(ann));
		}

		void
		p_increasing_bool(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> x = arg2BoolVarArgs(ce[0]);
			rel(s,x,IRT_LE,ann2icl(ann));
		}

		void
		p_table_bool(const ConExpr& ce, AST::Node* ann) {
			vec<BoolView> x = arg2BoolVarArgs(ce[0]);
			IntArgs tuples = arg2boolargs(ce[1]);
			int noOfVars   = x.size();
			int noOfTuples = tuples.size()/noOfVars;
			TupleSet ts;
			for (int i=0; i<noOfTuples; i++) {
				IntArgs t(noOfVars);
				for (int j=0; j<x.size(); j++) {
					t[j] = tuples[i*noOfVars+j];
				}
				ts.add(t);
			}
			ts.finalize();
			extensional(s,x,ts,EPK_DEF,ann2icl(ann));
		}

		void p_cumulatives(const ConExpr& ce,
											AST::Node* ann) {
			vec<IntVar*> start = arg2intvarargs(ce[0]);
			vec<IntVar*> duration = arg2intvarargs(ce[1]);
			vec<IntVar*> height = arg2intvarargs(ce[2]);
			int n = start.size();
			IntVar bound = getIntVar(ce[3]);

			if (bound.assigned()) {
				IntArgs machine(n);
				for (int i = n; i--; ) machine[i] = 0;
				IntArgs limit(1, bound.val());
				vec<IntVar*> end(n);
				for (int i = n; i--; ) end[i] = IntVar(0, Int::Limits::max);
				cumulatives(machine, start, duration, end, height, limit, true,
										ann2icl(ann));
			} else {
				int min = Gecode::Int::Limits::max;
				int max = Gecode::Int::Limits::min;
				vec<IntVar*> end(start.size());
				for (int i = start.size(); i--; ) {
					min = std::min(min, start[i].min());
					max = std::max(max, start[i].max() + duration[i].max());
					end[i] = post(start[i] + duration[i]);
				}
				for (int time = min; time < max; ++time) {
					vec<IntVar*> x(start.size());
					for (int i = start.size(); i--; ) {
						IntVar overlaps = channel(post((~(start[i] <= time) && 
																									~(time < end[i]))));
						x[i] = mult(overlaps, height[i]);
					}
					linear(x, IRT_LE, bound);
				}
			}
		}
*/

		class IntPoster {
		public:
			IntPoster(void) {
				registry().add("int_eq", &p_int_eq);
				registry().add("int_ne", &p_int_ne);
				registry().add("int_ge", &p_int_ge);
				registry().add("int_gt", &p_int_gt);
				registry().add("int_le", &p_int_le);
				registry().add("int_lt", &p_int_lt);
				registry().add("int_eq_reif", &p_int_eq_reif);
				registry().add("int_ne_reif", &p_int_ne_reif);
				registry().add("int_ge_reif", &p_int_ge_reif);
				registry().add("int_gt_reif", &p_int_gt_reif);
				registry().add("int_le_reif", &p_int_le_reif);
				registry().add("int_lt_reif", &p_int_lt_reif);
				registry().add("int_lin_eq", &p_int_lin_eq);
				registry().add("int_lin_eq_reif", &p_int_lin_eq_reif);
				registry().add("int_lin_ne", &p_int_lin_ne);
				registry().add("int_lin_ne_reif", &p_int_lin_ne_reif);
				registry().add("int_lin_le", &p_int_lin_le);
				registry().add("int_lin_le_reif", &p_int_lin_le_reif);
				registry().add("int_lin_lt", &p_int_lin_lt);
				registry().add("int_lin_lt_reif", &p_int_lin_lt_reif);
				registry().add("int_lin_ge", &p_int_lin_ge);
				registry().add("int_lin_ge_reif", &p_int_lin_ge_reif);
				registry().add("int_lin_gt", &p_int_lin_gt);
				registry().add("int_lin_gt_reif", &p_int_lin_gt_reif);
				registry().add("int_plus", &p_int_plus);
				registry().add("int_minus", &p_int_minus);
				registry().add("int_times", &p_int_times);
				registry().add("int_div", &p_int_div);
				registry().add("int_mod", &p_int_mod);
				registry().add("int_min", &p_int_min);
				registry().add("int_max", &p_int_max);
				registry().add("int_abs", &p_abs);
				registry().add("int_negate", &p_int_negate);
				registry().add("bool_and", &p_bool_and);
				registry().add("bool_not", &p_bool_not);
				registry().add("bool_or", &p_bool_or);
				registry().add("bool_xor", &p_bool_xor);
				registry().add("bool_eq", &p_bool_eq);
				registry().add("bool_eq_reif", &p_bool_eq_reif);
				registry().add("bool_ne", &p_bool_ne);
				registry().add("bool_ne_reif", &p_bool_ne_reif);
				registry().add("bool_le", &p_bool_le);
				registry().add("bool_le_reif", &p_bool_le_reif);
				registry().add("bool_lt", &p_bool_lt);
				registry().add("bool_lt_reif", &p_bool_lt_reif);
				registry().add("bool_ge", &p_bool_ge);
				registry().add("bool_ge_reif", &p_bool_ge_reif);
				registry().add("bool_gt", &p_bool_gt);
				registry().add("bool_gt_reif", &p_bool_gt_reif);
				registry().add("bool_left_imp", &p_bool_l_imp);
				registry().add("bool_right_imp", &p_bool_r_imp);
				registry().add("array_bool_and", &p_array_bool_and);
				registry().add("array_bool_or", &p_array_bool_or);
				registry().add("bool_clause", &p_array_bool_clause);
				registry().add("bool_clause_reif", &p_array_bool_clause_reif);
				registry().add("array_int_element", &p_array_int_element);
				registry().add("array_var_int_element", &p_array_var_int_element);
				registry().add("array_bool_element", &p_array_bool_element);
				registry().add("array_var_bool_element", &p_array_var_bool_element);
				registry().add("bool2int", &p_bool2int);

        registry().add("set_in", &p_set_in);
        registry().add("set_in_reif", &p_set_in_reif);

				registry().add("all_different_int", &p_all_different_int);
				registry().add("inverse_offsets", &p_inverse_offsets);
				registry().add("table_int", &p_table_int);
				registry().add("regular", &p_regular);
				registry().add("chuffed_disjunctive_strict", &p_disjunctive);
				registry().add("chuffed_cumulative", &p_cumulative);
				registry().add("chuffed_cumulative_vars", &p_cumulative2);
				registry().add("minimum_int", &p_minimum);
				registry().add("maximum_int", &p_maximum);
				registry().add("lex_less_int", &p_lex_less);
				registry().add("lex_lesseq_int", &p_lex_lesseq);

				registry().add("variables_interchange", &var_sym);
				registry().add("values_interchange", &val_sym);
				registry().add("variables_sequences", &var_seq_sym);
				registry().add("values_sequences", &val_seq_sym);

/*	    
				registry().add("all_different_int", &p_distinct);
				registry().add("all_different_offset", &p_distinctOffset);
				registry().add("count", &p_count);
				registry().add("at_least_int", &p_at_least);      
				registry().add("at_most_int", &p_at_most);
				registry().add("global_cardinality_gecode", &p_global_cardinality);
				registry().add("sort", &p_sort);
				registry().add("inverse_offsets", &p_inverse_offsets);
				registry().add("increasing_int", &p_increasing_int);
				registry().add("increasing_bool", &p_increasing_bool);
				registry().add("table_bool", &p_table_bool);
				registry().add("cumulatives", &p_cumulatives);
*/
				registry().add("bool_sum_eq", &p_bool_sum_eq);
				registry().add("bool_sum_ne", &p_bool_sum_ne);
				registry().add("bool_sum_le", &p_bool_sum_le);
				registry().add("bool_sum_lt", &p_bool_sum_lt);
				registry().add("bool_sum_ge", &p_bool_sum_ge);
				registry().add("bool_sum_gt", &p_bool_sum_gt);
/*
				registry().add("bool_lin_eq", &p_bool_lin_eq);
				registry().add("bool_lin_ne", &p_bool_lin_ne);
				registry().add("bool_lin_le", &p_bool_lin_le);
				registry().add("bool_lin_lt", &p_bool_lin_lt);
				registry().add("bool_lin_ge", &p_bool_lin_ge);
				registry().add("bool_lin_gt", &p_bool_lin_gt);

				registry().add("bool_lin_eq_reif", &p_bool_lin_eq_reif);
				registry().add("bool_lin_ne_reif", &p_bool_lin_ne_reif);
				registry().add("bool_lin_le_reif", &p_bool_lin_le_reif);
				registry().add("bool_lin_lt_reif", &p_bool_lin_lt_reif);
				registry().add("bool_lin_ge_reif", &p_bool_lin_ge_reif);
				registry().add("bool_lin_gt_reif", &p_bool_lin_gt_reif);
*/

				registry().add("tree", &p_tree);
				registry().add("steiner_tree", &p_steinerTree);
				registry().add("biconnected", &p_bicconected);
				registry().add("wbiconnected", &p_wbicconected);
				registry().add("vrptw", &p_vrptw);
				registry().add("mst", &p_mst);
				registry().add("tsp", &p_tsp);
				registry().add("cmst", &p_cmst);
                                registry().add("dreachable", &p_dreachable);
                                registry().add("dreachable_reif", &p_dreachable_reif);
				registry().add("pathsucc", &p_pathsucc);
				registry().add("path", &p_path);
				registry().add("dag", &p_dag);
				registry().add("bounded_path", &p_bounded_path);
				registry().add("td_bounded_path", &p_td_bounded_path);
				registry().add("td_bounded_path_basic", &p_td_bounded_path_basic);
				registry().add("subcircuit_kf", &p_subcircuit_int_kf);
				registry().add("subpath_kf", &p_subpath_int_kf);
				registry().add("circuit_kf", &p_circuit_int_kf);
				registry().add("circuit", &p_circuit_int_kf);
				registry().add("path_kf", &p_path_int_kf);
				registry().add("mdd", &p_mdd);
				registry().add("wmdd", &p_wmdd);
			}
		};
		IntPoster __int_poster;

	}

        void Registry::parseVariableAnnotations(AST::Node* ann, VarSpec* vs, Var* v) {
            if (!ann) return;
            if (ann->hasAtom("mddfied")) {
                if (!so.mddfy) {
                    fprintf(stderr,"Ignoring mddfied annotation (turn on options)\n");
                    return;
                }
                if (!so.presolve) {
                    fprintf(stderr,"Ignoring mddfied annotations (turn on options)\n");
                    return;
                }
                if (v->getType() < INT_VAR) {
                    fprintf(stderr,"Ignoring mddfied variable that is not INT\n");
                    return;
                }
                bool add = true;
                for (int i = 0; i < engine.mddfied_variables[0].size(); i++) {
                    if (engine.mddfied_variables[0][i] == (IntVar*)v)
                        add = false;
                }
                if (add)
                    engine.mddfied_variables[0].push_back((IntVar*)v); 
                assert(vs->name != "");
                engine.presolved_variables[(IntVar*)v] = vs->name;
                //printf("Inserted %p with name %s\n",(IntVar*)v,vs->name.c_str());
            }
        }

        void Registry::parseConstraintAnnotations(AST::Node* ann, const ConExpr& ce,int prev_last_prop) {
            if (!ann) return;
            if (ann->hasCall("mddfy")) {
                if (!so.mddfy) return;
                int id;
                vec<IntVar*> vars;
                for (int i = 0; i < ce.args->a.size(); i++) {
                    AST::Node* n = ce.args->a[i];
                    if (n->isArray()) {                    
                        AST::Array* arr = n->getArray();
                        for (int j = 0; j < arr->a.size(); j++) {
                            AST::Node* n2 = arr->a[j];
                            if (n2->isIntVar())
                                vars.push(s->iv[n2->getIntVar()]); 
                        }
                    } else if (n->isIntVar()) {
                        vars.push(s->iv[n->getIntVar()]);
                    }                
                }
                if(ann->getCall("mddfy")->args[0].isInt(id)) {
                    printf("TODO!!!!!registry.c:%d\n",__LINE__);
                    exit(1);
                    assert(so.presolve);
                    //predicate name(args) :: mddfy(id)
                    id = ann->getCall("mddfy")->args[0].getInt();
                    for (int i = 0; i < vars.size(); i++) {
                        bool add = true;
                        for (int j = 0; j < engine.mddfied_variables[id].size(); j++) {
                            if (engine.mddfied_variables[id][j] == vars[i])
                                add = false;
                        }
                        if (add)
                            engine.mddfied_variables[id].push_back(vars[i]); 
                    }
                } else if (ann->getCall("mddfy")->hasAtom("variable")) {
                    assert(so.presolve);
                    //var domain name :: mddfy(variable)
                    printf("Encountered variable \n");
                    ann->print(std::cout); printf("\n");
                    for (int i = 0; i < vars.size(); i++) {
                        bool add = true;
                        for (int j = 0; j < engine.mddfied_variables[0].size(); j++) {
                            if (engine.mddfied_variables[0][j] == vars[i])
                                add = false;
                        }
                        if (add)
                            engine.mddfied_variables[0].push_back(vars[i]); 
                    }
                } else if (ann->getCall("mddfy")->args[0].hasCall("call")) {
                    //constraint **(args) :: mddfy(call(some_id)) 
                    //the id is for debuging purposes
                    AST::Call* call = ann->getCall("mddfy")->args[0].getCall("call");
                    id = call->args[0].getInt();
                    for (int i = 0; i < vars.size(); i++) {
                        bool add = true;
                        for (int j = 0; j < engine.mddfied_variables[id].size(); j++) {
                            if (engine.mddfied_variables[id][j] == vars[i])
                                add = false;
                        }
                        if (add)
                            engine.mddfied_variables[id].push_back(vars[i]); 
                    }
                } else if (ann->getCall("mddfy")->args[0].hasCall("model")) {
                    if (so.mddfolder == "") {
                        fprintf(stderr,"No MDD folder specified: can't load MDDs\n");
                        exit(1);
                    }
                    //constraint **(args) :: mddfy(model(id_of_MDD_to_use))
                    AST::Call* model = ann->getCall("mddfy")->args[0].getCall("model");
                    assert(model->args[0].isInt(id));
                    id = model->args[0].getInt();
                    if (engine.loaded_mdds.find(id) == engine.loaded_mdds.end()){
                        engine.loaded_mdds[id] = MDD::read_mdd_file(so.mddfolder+"/"+std::to_string(id)+".mdd");
                    }
                    MDDOpts o;
                    vec<IntView<4> > views;
                    if (vars.size() != engine.loaded_mdds[id].shifts.size()) {
                        fprintf(stderr,
                                "Warning: Not building an MDD for one of the "
                                "constraints because it has only %d arguments "
                                "but the MDD was built for %d variables.\n",
                                vars.size(),engine.loaded_mdds[id].shifts.size());
                    } else {
                        for (int i = 0; i < vars.size(); i++) {
                            views.push(IntView<4>(vars[i],1,engine.loaded_mdds[id].shifts[i]));
                            assert(views[i].getMin() >= 0);
                        }
                        addMDD(views, engine.loaded_mdds[id], o);
                    }
                }

            }
        }



}
