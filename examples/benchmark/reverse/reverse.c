#include "vst_ide.h"

#define NULL ((void*)0)

/*@ Extern Coq
  (listrep : addr -> list Z -> Assertion)
*/

struct List {
   int head;
   struct List *tail;
};

struct List *reverse(struct List *p)
/*@
With
  (l : list Z)
Require
  listrep(p, l)
Ensure
  listrep(__return, rev(l))
*/
{
  /*@ Assert
    listrep(p@pre, l) *
    data_at(&p, struct List*, p@pre)
  */
  struct List *w = NULL;
  /*@ Assert
    listrep(p@pre, l) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, 0)
  */
  struct List *v = p;
  /*@ Assert
    listrep(p@pre, l) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, 0) *
    data_at(&v, struct List*, p@pre)
  */
  // reverse_which_implies_wit_1
  /*@
    listrep(p@pre, l)
    which implies
    l == app(rev(nil), l) &&
    listrep(0, nil) *
    listrep(p@pre, l)
  */
  /*@ Assert
    l == app(rev(nil), l) &&
    listrep(0, nil) *
    listrep(p@pre, l) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, 0) *
    data_at(&v, struct List*, p@pre)
  */
  // reverse_entail_wit_5
  /*@ Assert Inv
    exists w_v v_v l1 l2,
    l == app(rev(l1), l2) &&
    listrep(w_v, l1) *
    listrep(v_v, l2) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, w_v) *
    data_at(&v, struct List*, v_v)
  */
  while (v != NULL) {
    /*@ Assert
      exists w_v v_v l1 l2,
      v_v != 0 &&
      l == app(rev(l1), l2) &&
      listrep(w_v, l1) *
      listrep(v_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, w_v) *
      data_at(&v, struct List*, v_v)
    */
    // reverse_which_implies_wit_2
    /*@
      exists v_v l1 l2,
      v_v != 0 &&
      l == app(rev(l1), l2) &&
      listrep(v_v, l2)
      which implies
      exists t_v x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(t_v, l2) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, t_v)
    */
    /*@ Assert
      exists w_v v_v t_v l1 x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(w_v, l1) *
      listrep(t_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, w_v) *
      data_at(&v, struct List*, v_v) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, t_v)
    */
    struct List *t = v->tail;
    /*@ Assert
      exists w_v v_v t_v l1 x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(w_v, l1) *
      listrep(t_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, w_v) *
      data_at(&v, struct List*, v_v) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, t_v) *
      data_at(&t, struct List*, t_v)
    */
    v->tail = w;
    /*@ Assert
      exists w_v v_v t_v l1 x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(w_v, l1) *
      listrep(t_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, w_v) *
      data_at(&v, struct List*, v_v) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, w_v) *
      data_at(&t, struct List*, t_v)
    */
    w = v;
    /*@ Assert
      exists w_v v_v t_v l1 x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(w_v, l1) *
      listrep(t_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, v_v) *
      data_at(&v, struct List*, v_v) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, w_v) *
      data_at(&t, struct List*, t_v)
    */
    v = t;
    /*@ Assert
      exists w_v v_v t_v l1 x l2,
      l == app(rev(l1), cons(x, l2)) &&
      listrep(w_v, l1) *
      listrep(t_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, v_v) *
      data_at(&v, struct List*, t_v) *
      data_at(&v_v->head, int, x) *
      data_at(&v_v->tail, struct List*, w_v) *
      data_at(&t, struct List*, t_v)
    */
    // reverse_entail_wit_12
    /*@ Assert
      exists w_v v_v l1 l2,
      l == app(rev(l1), l2) &&
      listrep(w_v, l1) *
      listrep(v_v, l2) *
      data_at(&p, struct List*, p@pre) *
      data_at(&w, struct List*, w_v) *
      data_at(&v, struct List*, v_v) *
      undef_data_at(&t, struct List*)
    */
  }
  /*@ Assert
    exists w_v v_v l1 l2,
    v_v == 0 &&
    l == app(rev(l1), l2) &&
    listrep(w_v, l1) *
    listrep(v_v, l2) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, w_v) *
    data_at(&v, struct List*, v_v)
  */
  // reverse_entail_wit_15
  /*@ Assert
    exists w_v,
    listrep(w_v, rev(l)) *
    data_at(&p, struct List*, p@pre) *
    data_at(&w, struct List*, w_v) *
    data_at(&v, struct List*, 0)
  */
  return w;
}
