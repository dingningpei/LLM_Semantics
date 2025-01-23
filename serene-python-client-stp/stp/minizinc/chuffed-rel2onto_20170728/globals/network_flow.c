#include <limits>
#include "core/propagator.h"

//#include "vars/bool_view.h"
//#include "vars/int_var.h"
//#include "vars/int_view.h"

#include "primitives/primitives.h"
#include "globals/globals.h"

#include <vector>

#define LAZY_EXPL 0
#define CHECK_EXPL 0
#define INLINE 1


int  getMin0(BoolView& bv) { return (bv.isTrue()) ? 1 : 0; }
int  getMax0(BoolView& bv) { return (bv.isFalse()) ? 0 : 1; }
#define MASK_PRIORITY 7
#define MASK_NO_SCC_PRUNING 8
#define MASK_LP_ONLY 0x400
#define MASK_CP_ONLY 0x800

//-----

class NetworkFlow : public Propagator {
	class Arc;
	class Node;

	class SCC {
	public:
		int parent;
		vec<Node *> cut;
		bool in_scc_change;
	};

	class Node {
	public:
		int mark;

		int capacity;
		Arc *pred;
		bool pred_forw;

		vec<Arc *> forw;
		vec<Arc *> back;

		vec<Arc *> unsat_forw;
		vec<Arc *> unsat_back;

		int supply;
		int excess; // current supply + incoming - outgoing flows

		bool in_source;

		void init( NetworkFlow *_this, int _supply) {
			mark = 0;
			_this->scc[0].cut.push(this);

			capacity = 0;

			supply = _supply;
			excess = _supply;

			in_source = true;
			_this->source.push(this);
		}
	};

	class Arc {
	public:
		bool is_int;

		Node *head;
		Node *tail;

		int flow;
		int flow_min;
		int flow_max;

		bool in_unsat_forw;
		bool in_unsat_back;

		void init(bool _is_int, Node *_head, Node *_tail, int _flow_min, int _flow_max) {
			is_int = _is_int;

			head = _head;
			head->back.push(this);
			tail = _tail;
			tail->forw.push(this);

			flow = _flow_min;
			head->excess += _flow_min;
			tail->excess -= _flow_min;
			flow_min = _flow_min;
			flow_max = _flow_max;

			in_unsat_forw = true;
			tail->unsat_forw.push(this);
			in_unsat_back = true;
			head->unsat_back.push(this);
		}
	};

	class IntArc : public Arc {
	public:
		IntVar *int_var;

		void init(Node *_head, Node *_tail, IntVar *_int_var) {
			Arc::init(true, _head, _tail, _int_var->getMin(), _int_var->getMax());
			int_var = _int_var;
		}
	};

	class BoolArc : public Arc {
	public:
		BoolView bool_var;

		void init(Node *_head, Node *_tail, BoolView& _bool_var) {
			Arc::init(false, _head, _tail, 0, 1);
			bool_var = _bool_var;
		}
	};

#if LAZY_EXPL
	// structure to store propagation info for lazy explanation
	class Pinfo {
	public:
		BTPos btpos;
		int trail_min_size;
		int trail_max_size;
		int scc_size;
		// above 4 vars store the backtrack point

		int c; // scc to use
		Arc *exclude; // arc flow to prune

		Pinfo(BTPos _btpos, int _trail_min_size, int _trail_max_size, int _scc_size, int _c, Arc *_exclude) : btpos(_btpos), trail_min_size(_trail_min_size), trail_max_size(_trail_max_size), scc_size(_scc_size), c(_c), exclude(_exclude) {}
	};

	bool trailed_pinfo_sz;
#endif

public:
	// Persistent trailed state
	int nodes;
	Node *node;
	int arcs;
	int int_arcs;
	IntArc *int_arc;
	int bool_arcs;
	BoolArc *bool_arc;
	int flags;

    //Added by Diego, was an int
	Tint scc_size;
	vec<SCC> scc;

	int *queue_pos; // has var_nodes + val_nodes entries, queue indices
	vec<std::pair<int, int> > queue; // records unprocessed wakeups
	vec<std::pair<Arc *, int> > trail_min;
	vec<std::pair<Arc *, int> > trail_max; // selected info gets moved from queue to trails

#if LAZY_EXPL
	vec<Pinfo> p_info; // memory for propagation info
#endif

	// Persistent non-trailed state
	int level; // says whether we have registered a BTWatch with engine

	vec<Node *> source;

	// Scratch, retained so that we don't keep reallocating storage
	vec<Node *> cut;
	vec<int> scc_change;

	int dfs_count;
	vec<Node *> scc_stack;
	int parent; // how to fill in the parent field of a new SCC entry

	vec<Lit> ps;

	bool augment(Node *e) {
 //fprintf(stderr, "augment %d\n", e - node);
		for (int i = 0; i < cut.size(); ++i)
			cut[i]->capacity = 0;
		cut.clear();
		e->capacity = e->excess;
		cut.push(e);

		int capacity;
		Node *o;
		for (int i = 0; i < cut.size(); ++i) {
			Node *n = cut[i];
 //fprintf(stderr, " visit %d\n", n - node);

			int s;

			s = 0;
			for (int i = 0; i < n->unsat_forw.size(); ++i) {
				Arc *a = n->unsat_forw[i];
				capacity = a->flow_max - a->flow;
				if (capacity <= 0) {
					a->in_unsat_forw = false;
					continue;
				}

				o = a->head;
				if (o->capacity == 0) {
					o->pred = a;
					o->pred_forw = true;
					capacity = std::min(n->capacity, capacity);
					if (o->excess < 0) {
						for (; i < n->unsat_forw.size(); ++i)
							n->unsat_forw[s++] = n->unsat_forw[i];
						n->unsat_forw.resize(s);
						goto found;
					}
					o->capacity = capacity;
					cut.push(o);
				}

				n->unsat_forw[s++] = a;
			}
			n->unsat_forw.resize(s);

			s = 0;
			for (int i = 0; i < n->unsat_back.size(); ++i) {
				Arc *a = n->unsat_back[i];
				capacity = a->flow - a->flow_min;
				if (capacity <= 0) {
					a->in_unsat_back = false;
					continue;
				}

				o = a->tail;
				if (o->capacity == 0) {
					o->pred = a;
					o->pred_forw = false;
					capacity = std::min(n->capacity, capacity);
					if (o->excess < 0) {
						for (; i < n->unsat_back.size(); ++i)
							n->unsat_back[s++] = n->unsat_back[i];
						n->unsat_back.resize(s);
						goto found;
					}
					o->capacity = capacity;
					cut.push(o);
				}

				n->unsat_back[s++] = a;
			}
			n->unsat_back.resize(s);
		}
 //fprintf(stderr, " not found\n");
		return false;

	found:
		capacity = std::min(capacity, -o->excess);
 //fprintf(stderr, " found capacity %d\n", capacity);
		o->excess += capacity;
		do {
			Arc *a = o->pred;
 //fprintf(stderr, " pred %d->%d %s\n", a->tail - node, a->head - node, o->pred_forw ? "true" : "false");
			if (o->pred_forw) {
				a->flow += capacity;
				if (!a->in_unsat_back) {
					a->in_unsat_back = true;
					o->unsat_back.push(a);
				}
				o = a->tail;
			}
			else {
				a->flow -= capacity;
				if (!a->in_unsat_forw) {
					a->in_unsat_forw = true;
					o->unsat_forw.push(a);
				}
				o = a->head;
			}
 //assert(a->flow_min <= a->flow && a->flow <= a->flow_max);
		} while (o != e);
		e->excess -= capacity;
		return true;
	}

	bool solve() {
		while (source.size() != 0) {
			Node *e = source.last();
			while (e->excess > 0) {
				if (!augment(e))
					return false;
			}
			e->in_source = false;
			source.pop();
		}
		return true;
	}

	int sum_cut(Arc *exclude) {
		int flow = 0;
		// compute minimum flow entering the cut
		for (int i = 0; i < cut.size(); ++i) {
			Node *n = cut[i];
			flow += n->supply;

			for (int i = 0; i < n->forw.size(); ++i) {
				Arc *a = n->forw[i];
				if (a->head->capacity == 0 && a != exclude)
					flow -= a->flow_max;
			}

			for (int i = 0; i < n->back.size(); ++i) {
				Arc *a = n->back[i];
				if (a->tail->capacity == 0 && a != exclude)
					flow += a->flow_min;
			}
		}
		return flow;
	}

	Clause *explain_cut(Arc *exclude, int lift) {
#if CHECK_EXPL
 int s = ps.size();
#endif
		for (int i = 0; i < cut.size(); ++i) {
			Node *n = cut[i];

			for (int i = 0; i < n->forw.size(); ++i) {
 assert(lift >= 0);
				Arc *a = n->forw[i];
				if (a->head->capacity == 0 && a != exclude) {
					if (a->is_int) {
						int max_lift = static_cast<IntArc *>(a)->int_var->getMax0() - a->flow_max;
						if (lift >= max_lift)
							lift -= max_lift;
						else {
							ps.push(~static_cast<IntArc *>(a)->int_var->getLit(a->flow_max + lift, 3));
							lift = 0;
						}
					}
					else {
                                            int max_lift = getMax0(static_cast<BoolArc *>(a)->bool_var) - a->flow_max;
						if (lift >= max_lift)
							lift -= max_lift;
						else
							ps.push(~static_cast<BoolArc *>(a)->bool_var.getLit(false));
					}
				}
			}

			for (int i = 0; i < n->back.size(); ++i) {
 assert(lift >= 0);
				Arc *a = n->back[i];
				if (a->tail->capacity == 0 && a != exclude) {
					if (a->is_int) {
						int max_lift = a->flow_min - static_cast<IntArc *>(a)->int_var->getMin0();
						if (lift >= max_lift)
							lift -= max_lift;
						else {
							ps.push(~static_cast<IntArc *>(a)->int_var->getLit(a->flow_min - lift, 2));
							lift = 0;
						}
					}
					else {
                                            int max_lift = a->flow_min - getMin0(static_cast<BoolArc *>(a)->bool_var);
						if (lift >= max_lift)
							lift -= max_lift;
						else
							ps.push(~static_cast<BoolArc *>(a)->bool_var.getLit(true));
					}
				}
			}
		}
#if CHECK_EXPL
 for (; s < ps.size(); ++s) {
  assert(sat.value(ps[s]) == l_False);
  assert(sat.level[var(ps[s])] > 0);
 }
#endif
		return Reason_new(ps);
	}

	Clause *explain_scc(int c, Arc *exclude) {
		for (int i = 0; i < scc[c].cut.size(); ++i) {
			Node *n = scc[c].cut[i];

			for (int i = 0; i < n->forw.size(); ++i) {
				Arc *a = n->forw[i];
				if (a->head->mark != c && a != exclude) {
					if (a->is_int) {
						if (static_cast<IntArc *>(a)->int_var->getMax0() > a->flow_max)
							ps.push(~static_cast<IntArc *>(a)->int_var->getLit(a->flow_max, 3));
					}
					else {
                                            if (getMax0(static_cast<BoolArc *>(a)->bool_var) > a->flow_max)
							ps.push(~static_cast<BoolArc *>(a)->bool_var.getLit(false));
					}
				}
			}

			for (int i = 0; i < n->back.size(); ++i) {
				Arc *a = n->back[i];
				if (a->tail->mark != c && a != exclude) {
					if (a->is_int) {
						if (a->flow_min > static_cast<IntArc *>(a)->int_var->getMin0())
							ps.push(~static_cast<IntArc *>(a)->int_var->getLit(a->flow_min, 2));
					}
					else {
                                            if (a->flow_min > getMin0(static_cast<BoolArc *>(a)->bool_var))
							ps.push(~static_cast<BoolArc *>(a)->bool_var.getLit(true));
					}
				}
			}
		}
		return Reason_new(ps);
	}

	int tarjan(Node *n) {
		// see citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.73.3278
		assert(n->mark == parent);
		int low_point = --dfs_count;
		n->mark = low_point;
		scc_stack.push(n);
 //fprintf(stderr, " Tarjan %d %d\n", n - node, n->mark);

		int s;

		s = 0;
		for (int i = 0; i < n->unsat_forw.size(); ++i) {
			Arc *a = n->unsat_forw[i];
 //fprintf(stderr, "  %d->%d %d,%d,%d\n", a->tail - node, a->head - node, a->flow_min, a->flow, a->flow_max);
			if (a->flow >= a->flow_max) {
				a->in_unsat_forw = false;
				continue;
			}

			Node *o = a->head;
			int c = o->mark;
			if (c == parent) {
				c = tarjan(o);
				if (c == static_cast<int>(0x80000000))
					goto fail;
			}
			if (c < 0)
				low_point = std::max(low_point, c);
			else {
 //fprintf(stderr, "%p %d->%d prune_max_scc %d->%d scc %d\n", this, n - node, o - node, a->flow_max, a->flow, c);
				if (a->is_int) {
					if (static_cast<IntArc *>(a)->int_var->setMaxNotR(static_cast<IntArc *>(a)->flow_min) && !static_cast<IntArc *>(a)->int_var->setMax(static_cast<IntArc *>(a)->flow_min, createReason(c, a)))
						goto fail;
				}
				else if (static_cast<BoolArc *>(a)->bool_var.setValNotR(false) && !static_cast<BoolArc *>(a)->bool_var.setVal(false, createReason(c, a)))
					goto fail;
				trail_max.push(std::pair<Arc *, int>(a, a->flow_max));
				a->flow_max = a->flow_min;

				a->in_unsat_forw = false;
				continue;
			}

			n->unsat_forw[s++] = a;
			continue;

		fail:
			for (; i < n->unsat_forw.size(); ++i)
				n->unsat_forw[s++] = n->unsat_forw[i];
			n->unsat_forw.resize(s);
			return 0x80000000;
		}
		n->unsat_forw.resize(s);

		s = 0;
		for (int i = 0; i < n->unsat_back.size(); ++i) {
			Arc *a = n->unsat_back[i];
 //fprintf(stderr, "  %d->%d %d,%d,%d\n", a->head - node, a->tail - node, -a->flow_min, -a->flow, -a->flow_max);
			if (a->flow <= a->flow_min) {
				a->in_unsat_back = false;
				continue;
			}

			Node *o = a->tail;
			int c = o->mark;
			if (c == parent) {
				c = tarjan(o);
				if (c == static_cast<int>(0x80000000))
					goto bail;
			}
			if (c < 0)
				low_point = std::max(low_point, c);
			else {
 //fprintf(stderr, "%p %d->%d prune_min_scc %d->%d scc %d\n", this, o - node, n - node, a->flow_min, a->flow, c);
				if (a->is_int) {
					if (static_cast<IntArc *>(a)->int_var->setMinNotR(static_cast<IntArc *>(a)->flow_max) && !static_cast<IntArc *>(a)->int_var->setMin(static_cast<IntArc *>(a)->flow_max, createReason(c, a)))
						goto bail;
				}
				else if (static_cast<BoolArc *>(a)->bool_var.setValNotR(true) && !static_cast<BoolArc *>(a)->bool_var.setVal(true, createReason(c, a)))
					goto bail;
				trail_min.push(std::pair<Arc *, int>(a, a->flow_min));
				a->flow_min = a->flow_max;

				a->in_unsat_back = false;
				continue;
			}

			n->unsat_back[s++] = a;
			continue;

		bail:
			for (; i < n->unsat_back.size(); ++i)
				n->unsat_back[s++] = n->unsat_back[i];
			n->unsat_back.resize(s);
			return 0x80000000;
		}
		n->unsat_back.resize(s);

		if (low_point != n->mark)
			return low_point;

		int c = scc_size++;
 rassert(scc_size >= 0);
		if (scc.size() < scc_size)
			scc.push();
		scc[c].parent = parent;
		scc[c].cut.clear();
		scc[c].in_scc_change = false;
		Node *o;
		do {
			o = scc_stack.last();
			scc_stack.pop();
			o->mark = c;
			scc[c].cut.push(o);
		} while (o != n);
		return c;
	}

	NetworkFlow(vec<int>& supply, vec<int>& head, vec<int>& tail, vec<IntVar *>& int_var, vec<BoolView>& bool_var, int _flags) : flags(_flags) {
#if 0 // check idempotence (want to make this official eventually)
 char *c = new char[engine.vars.size()];
 memset(c, 0, engine.vars.size());
 for (int i = 0; i < int_var.size(); ++i) {
  int iv = int_var[i]->var_id;
  rassert(!c[iv]);
  c[iv] = 1;
 }
 for (int i = 0; i < bool_var.size(); ++i) {
  ChannelInfo& ci = sat.c_info[bool_var[i].v];
  rassert(ci.cons_type == 1);
  int iv = ci.cons_id;
  rassert(!c[iv]);
  c[iv] = 1;
 }
 delete c;
#endif
		// create an initial SCC to contain all nodes
		scc.push();
		scc[0].parent = -1;
		scc[0].in_scc_change = false;
		scc_size = 1;

		// create nodes
		nodes = supply.size();
		arcs = int_var.size() + bool_var.size();
		node = new Node[nodes];
		for (int i = 0; i < nodes; ++i)
			node[i].init(this, supply[i]);

		// create arcs
		int_arcs = int_var.size();
		int_arc = new IntArc[int_arcs];
		for (int i = 0; i < int_arcs; ++i)
			int_arc[i].init(node + head[i], node + tail[i], int_var[i]);

		bool_arcs = bool_var.size();
		bool_arc = new BoolArc[bool_arcs];
		for (int i = 0; i < bool_arcs; ++i)
			bool_arc[i].init(node + head[int_arcs + i], node + tail[int_arcs + i], bool_var[i]);

#if 0 // don't want to include initial solving time in parse time, so skip this
		// make feasible
		if (!solve())
			TL_FAIL();
#endif

		// create queue
		queue_pos = new int[arcs];
		memset(queue_pos, -1, arcs * sizeof(int));

		// make sure queue valid before attach
		priority = flags & MASK_PRIORITY;
		level = 0;
		for (int i = 0; i < int_arcs; ++i) {
			int_arc[i].int_var->attach(this, i, EVENT_LU);
#if HEUR_SUGGEST
			if ((flags & MASK_NO_SUGGEST) == 0)
				int_arc[i].int_var->suggest_props.push(std::pair<Propagator *, int>(this, i));
#endif
		}
		for (int i = 0; i < bool_arcs; ++i) {
			bool_arc[i].bool_var.attach(this, int_arcs + i, EVENT_LU);
#if HEUR_SUGGEST
			if ((flags & MASK_NO_SUGGEST) == 0)
				sat.suggest_props[bool_arc[i].bool_var.v].push(std::pair<Propagator *, int>(this, int_arcs + i));
#endif
		}
	}

	void wakeup(int i, int c) {
		if (queue_pos[i] >= 0)
			queue[queue_pos[i]].second |= c;
		else {
			queue_pos[i] = queue.size();
			queue.push(std::pair<int, int>(i, c));
			pushInQueue();
		}
	}

	void narrow_min(Arc *a, int new_min) {
 //fprintf(stderr, "%p %d->%d narrow_min %d\n", this, a->tail - node, a->head - node, new_min);
		// ignore redundant notifications, can happen either
		// when notified of our own pruning (making this an
		// idempotency check), or in case of multiple wakeups
		if (new_min <= a->flow_min)
			return;
		trail_min.push(std::pair<Arc *, int>(a, a->flow_min));
		a->flow_min = new_min;

		// is arc now saturated due to narrowed minimum flow?
		int capacity = a->flow - new_min;
		if (capacity > 0)
			return;

		// change to residual graph, redo affected SCC
		int c = a->tail->mark;
		if (c == a->head->mark && !scc[c].in_scc_change) {
			scc[c].in_scc_change = true;
			scc_change.push(c);
		}

		// negative capacity indicates arc is now in violation
		if (capacity >= 0)
			return;

		// make arc feasible again at the expense of its nodes
		a->flow = new_min;
		a->tail->excess += capacity;
		a->head->excess -= capacity;
		if (!a->head->in_source) {
			a->head->in_source = true;
			source.push(a->head);
		}
	}

	void narrow_max(Arc *a, int new_max) {
 //fprintf(stderr, "%p %d->%d narrow_max %d\n", this, a->tail - node, a->head - node, new_max);
		// ignore redundant notifications, can happen either
		// when notified of our own pruning (making this an
		// idempotency check), or in case of multiple wakeups
		if (new_max >= a->flow_max)
			return;
		trail_max.push(std::pair<Arc *, int>(a, a->flow_max));
		a->flow_max = new_max;

		// is arc now saturated due to narrowed maximum flow?
		int capacity = new_max - a->flow;
		if (capacity > 0)
			return;

		// change to residual graph, redo affected SCC
		int c = a->tail->mark;
		if (c == a->head->mark && !scc[c].in_scc_change) {
			scc[c].in_scc_change = true;
			scc_change.push(c);
		}

		// negative capacity indicates arc is now in violation
		if (capacity >= 0)
			return;

		// make arc feasible again at the expense of its nodes
		a->flow = new_max;
		a->tail->excess -= capacity;
		if (!a->tail->in_source) {
			a->tail->in_source = true;
			source.push(a->tail);
		}
		a->head->excess += capacity;
	}

	void process_wakeups() {
		for (int i = 0; i < queue.size(); ++i) {
			int j = queue[i].first;
			queue_pos[j] = -1;
			if (j < int_arcs) {
				IntArc *a = int_arc + j;
				int c = queue[i].second;
				if (c & EVENT_L)
					narrow_min(a, static_cast<int>(a->int_var->getMin()));
				if (c & EVENT_U)
					narrow_max(a, static_cast<int>(a->int_var->getMax()));
			}
			else {
				BoolArc *a = bool_arc + (j - int_arcs);
				if (a->bool_var.getVal())
					narrow_min(a, 1);
				else
					narrow_max(a, 0);
			}
		}
		queue.clear();
	}

	Reason createReason(int c, Arc *exclude) {
		// NOTE:  this should be split up for different kinds of reason
		if (!so.lazy)
			return Reason();
#if LAZY_EXPL
 //fprintf(stderr, "%p createReason:%d %d %d->%d\n", this, p_info.size(), c, (int)(exclude->tail - node), (int)(exclude->head - node));
		if (!trailed_pinfo_sz) {
                    engine.trail[engine.decisionLevel()].trail_elem.push(TrailElem(&p_info._size(), 4));
			trailed_pinfo_sz = true;
		}
		p_info.push(Pinfo(engine.getBTPos(), trail_min.size(), trail_max.size(), scc_size, c, exclude));
		return Reason(prop_id, p_info.size()-1);
#else
		ps.clear();
		ps.push();
		return explain_scc(c, exclude);
#endif
	}

	bool propagate() {
 //fprintf(stderr, "%p propagate level %d\n", this, engine.decisionLevel());
#if LAZY_EXPL
		trailed_pinfo_sz = false;
#endif

		// register to receive notification on backtrack
		if (level < engine.decisionLevel()) {
 //fprintf(stderr, "%p level %d BTWatch %d %d %d %d\n", this, engine.decisionLevel(), level, trail_min.size(), trail_max.size(), scc_size);

                    //Removed by Diego, made scc_size be a Tint
                    //engine.trail[engine.decisionLevel()].bt_watch.push(BTWatch(this, level, trail_min.size(), trail_max.size(), scc_size));
			level = engine.decisionLevel();
		}

		// process external tightenings
		scc_change.clear();
		process_wakeups();

		// regain feasibility
		if (!solve()) {
			if (so.lazy) {
				ps.clear();
				// couldn't we get the sum_cut() value from the
				// amount of infeasibility of the leaving arc?
                                bool opt_lift = true;
				sat.confl = explain_cut(0, opt_lift ? sum_cut(0) - 1 : 0);
			}
			goto fail;
		}

		// detect fixed flow variables by Tarjan's algorithm
		if ((flags & MASK_NO_SCC_PRUNING) == 0) {
			for (int i = 0; i < scc_change.size(); ++i) {
				parent = scc_change[i];
	
				dfs_count = 0;
				scc_stack.clear();
				for (int j = 0; j < scc[parent].cut.size(); ++j) {
					Node *n = scc[parent].cut[j];
					if (n->mark == parent && tarjan(n) == static_cast<int>(0x80000000)) {
						for (int k = 0; k < scc_stack.size(); ++k)
							scc_stack[k]->mark = parent;
						goto tarjan_fail;
					}
				}
	
				scc[parent].in_scc_change = false;
				continue;
	
			tarjan_fail:
				for (; i < scc_change.size(); ++i)
					scc[scc_change[i]].in_scc_change = false;
				return false;
			}
		}
		return true;

	fail:
		for (int i = 0; i < scc_change.size(); ++i)
			scc[scc_change[i]].in_scc_change = false;
		return false;
	}

	void clearPropState() {
		for (int i = 0; i < queue.size(); ++i)
			queue_pos[queue[i].first] = -1;
		queue.clear();
		in_queue = false;
	}

        void backtrackToPos(int prev_trail_min_size, int prev_trail_max_size, int prev_scc_size) {
		while (trail_min.size() > prev_trail_min_size) {
			std::pair<Arc *, int> t = trail_min.last();
			trail_min.pop();
 //fprintf(stderr, "%p %d->%d trail_min %d\n", this, t.first->tail - node, t.first->head - node, t.second);
			t.first->flow_min = t.second;
			if (!t.first->in_unsat_back) {
				t.first->in_unsat_back = true;
				t.first->head->unsat_back.push(t.first);
			}
		}
		while (trail_max.size() > prev_trail_max_size) {
			std::pair<Arc *, int> t = trail_max.last();
			trail_max.pop();
 //fprintf(stderr, "%p %d->%d trail_max %d\n", this, t.first->tail - node, t.first->head - node, t.second);
			t.first->flow_max = t.second;
			if (!t.first->in_unsat_forw) {
				t.first->in_unsat_forw = true;
				t.first->tail->unsat_forw.push(t.first);
			}
		}
		while (scc_size > prev_scc_size) {
			int c = scc[--scc_size].parent;
			for (int i = 0; i < scc[scc_size].cut.size(); ++i)
				scc[scc_size].cut[i]->mark = c;
		}
	}

#if LAZY_EXPL
	Clause *explain(Lit p, int inf_id) {
		Pinfo& pi = p_info[inf_id];
 //fprintf(stderr, "%p explain:%d %d %d->%d\n", this, inf_id, pi.c, (int)(pi.exclude->tail - node), (int)(pi.exclude->head - node));
		engine.btToPos(pi.btpos);
		backtrackToPos(pi.trail_min_size, pi.trail_max_size, pi.scc_size);
		assert(so.lazy);
		ps.clear();
		ps.push();
		return explain_scc(pi.c, pi.exclude);
	}
#endif

	void backtrack(int prev_level, int i, int j, int k) {
 //fprintf(stderr, "%p backtrack %d %d %d %d\n", this, prev_level, i, j, k);
		level = prev_level;
		backtrackToPos(i, j, k);
	}

#if HEUR_SUGGEST
	double getValue(int i) {
		assert(queue.empty());

		// regain feasibility
		solve();
		assert(source.empty()); // means solve returned true
		return (i < int_arcs) ?
			int_arc[i].flow :
			bool_arc[i - int_arcs].bool_var.s ?
				1 - bool_arc[i - int_arcs].flow :
				bool_arc[i - int_arcs].flow;
	}

	double getDual(int i) {
		assert(queue.empty());
		return 0;
	}
#endif
};

void network_flow(vec<int>& supply, vec<int>& head, vec<int>& tail, vec<IntVar *>& int_var, vec<BoolView>& bool_var, int flags
	) {
	rassert(head.size() == tail.size());
	rassert(head.size() == int_var.size() + bool_var.size());
	for (int i = 0; i < head.size(); ++i) {
		rassert(head[i] >= 0 && head[i] < supply.size());
		rassert(tail[i] >= 0 && head[i] < supply.size());
	}
#if 1 // remove constant arcs (naughtily clobber the passed inputs)
 int s = 0;
 int si = 0;
 int sb = 0;
 for (int i = 0; i < int_var.size(); ++i) {
  if (int_var[i]->isFixed()) {
   supply[head[i]] += int_var[i]->getVal();
   supply[tail[i]] -= int_var[i]->getVal();
  }
  else {
   head[s] = head[i];
   tail[s] = tail[i];
   ++s;
   int_var[si++] = int_var[i];
  }
 }
 for (int i = 0; i < bool_var.size(); ++i) {
  if (bool_var[i].isFixed()) {
   supply[head[int_var.size() + i]] += bool_var[i].getVal();
   supply[tail[int_var.size() + i]] -= bool_var[i].getVal();
  }
  else {
   head[s] = head[int_var.size() + i];
   tail[s] = tail[int_var.size() + i];
   ++s;
   bool_var[sb++] = bool_var[i];
  }
 }
 head.resize(s);
 tail.resize(s);
 int_var.resize(si);
 bool_var.resize(sb);
#endif
 
 /*if (so.master_lp >= 1 && !(flags & MASK_CP_ONLY)) {
		std::vector<Inequality> ineqs;
		for (int i = 0; i < supply.size(); ++i) {
			Inequality ineq;
			ineq.sense = 'E';
			ineq.rhs = supply[i];
			ineqs.push_back(ineq);
		}
		for (int i = 0; i < int_var.size(); ++i) {
			IntVar *iv = int_var[i];
			ineqs[head[i]].coeff[iv->var_id] += -1.0;
			ineqs[tail[i]].coeff[iv->var_id] += 1.0;
		}
		for (int i = 0; i < bool_var.size(); ++i) {
			BoolView bv = bool_var[i];
			if (bv.s) {
				ineqs[head[int_var.size() + i]].rhs += -1.0;
				ineqs[tail[int_var.size() + i]].rhs += 1.0;
				ineqs[head[int_var.size() + i]].coeff[~(bv.v)] += 1.0;
				ineqs[tail[int_var.size() + i]].coeff[~(bv.v)] += -1.0;
			}
			else {
				ineqs[head[int_var.size() + i]].coeff[~(bv.v)] += -1.0;
				ineqs[tail[int_var.size() + i]].coeff[~(bv.v)] += 1.0;
			}
		}
		for (int i = 0; i < static_cast<int>(ineqs.size()); ++i)
			engine.ineqs.push_back(ineqs[i]);
                        }*/
 int master_lp = 0;
	if (master_lp < 2 && !(flags & MASK_LP_ONLY))
		new NetworkFlow(supply, head, tail, int_var, bool_var, flags);
}
