// run with dynamically checked ghost code
#include "cstar.h"
#include "reverse_datatype.h"
#include <assert.h>
#include <stddef.h>

struct list_cell {
    int head;
    struct list_cell *tail;
};

HProp list_repr(struct list_cell *p, List l) { // Here p actually serve as a pair of a Ptr and an
                                               // field offset mapping for struct list_cell
    if (list_is_nil(l)) {
        return PURE(p EQ VAL(NULL));
    }
    if (list_is_cons(l)) {
        Z head = list_cons_head(l);    // generates a universally quantified variable and a pure constraint
        List tail = list_cons_tail(l); // same as above
        LET_SEP(Z, p_head, p->head)    // generates a exists and a data_at. A field access actually
                                       // requires a data_at with field offset and size information.
        LET_SEP(struct list_cell *, p_tail, p->tail) // same as above
        return PURE(p_head EQ head) SEP list_repr(p_tail, tail);
    }
}

// declare the original function without a body
struct list_cell *reverse_original(struct list_cell *p, List l);

List list_append(List list1, List list2) {
    return list_is_nil(list1) ? list2 : list_cons(list_cons_head(list1), list_append(list_cons_tail(list1), list2));
}

List list_reverse(List list) {
    if (list_is_nil(list)) {
        return list;
    }
    Z head = list_cons_head(list);
    List rev_tail = list_reverse(list_cons_tail(list));
    return list_append(rev_tail, list_cons(head, list_nil()));
}

struct list_cell *reverse(struct list_cell *p, List l) {
    require(list_repr(p, l));
    struct list_cell *__result = reverse_original(p, l);
    // construst a wrapper for executable functions because ensure clause must be checked for all
    // possible exit points
    ensure(list_repr(__result, list_reverse(l)));
    return __result;
}

struct list_cell *reverse_original(struct list_cell *p, const List l) {
    struct list_cell *rev_prefix;
    struct list_cell *rem_suffix;
    rev_prefix = NULL;
    List l1 = list_nil(); // ghost local variable (feed to VST-IDE like a non-address-taken variable)
    rem_suffix = p;
    List l2 = l; // same as above
#define INV                                                                                                            \
    (PURE(list_equal(list_append(list_reverse(l1), l2), l))                                                            \
         SEPAND (list_repr(rev_prefix, l1) SEP list_repr(rem_suffix, l2) SEP DATA_AT_EXISTS(VAL(&p))))
    for (assert(INV); rem_suffix != NULL; assert(INV)) {
        // invariant is checked at the begining and at the end of each loop body using for loop
#undef INV
        struct list_cell *t;
        assert(rem_suffix != NULL); // tell VST-IDE that rem_suffix is not NULL (unfold the cell)
        t = rem_suffix->tail;
        rem_suffix->tail = rev_prefix;
        rev_prefix = rem_suffix;
        l1 = list_cons(rem_suffix->head, l1); // ghost command
        rem_suffix = t;
        l2 = list_cons_tail(l2); // ghost command
    }
    return rev_prefix;
}

void test_list_reverse() {
    List l1 = list_cons(1, list_cons(2, list_cons(3, list_nil())));
    List l1_rev = list_cons(3, list_cons(2, list_cons(1, list_nil())));
    List l2 = list_reverse(l1);
    assert(list_equal(l1_rev, l2));
    list_println_sexp(l1_rev);
    list_println_sexp(l2);
}

int main() {
    test_list_reverse();
    struct list_cell *p = &(struct list_cell){1, &(struct list_cell){2, &(struct list_cell){3, NULL}}};
    List l = list_cons(1, list_cons(2, list_cons(3, list_nil())));
    reverse(p, l);
    return 0;
}
