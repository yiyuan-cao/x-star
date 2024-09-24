// run with dynamically checked ghost code
#include "cstar_test.h"
#include "reverse_datatype.h"

struct list_cell {
    int head;
    struct list_cell *tail;
};

HProp list_repr(struct list_cell *p, List l) { // Here p actually serve as a pair of a Ptr and an
                                               // field offset mapping for struct list_cell (used in field acesssing)
    LET_SEP(&p, Ptr p_val)                     // added only when we have addressable stack locations; can be emitted by C* compiler.
    // hexists p_val : Ptr. data_at(&p, p_val)      NB. exists is at the SL level in VST-IDE
    if (list_is_nil(l)) {
        return PURE(p_val EQ VAL(NULL)) SEPAND EMP;
        // we generate:
        //     hexists p_val : Ptr.
        //       data_at(&p, p_val) **
        //       (if is_nil(l) then pure(p_val EQ 0) SEPAND EMP else <...to be filled below...>)
    }
    if (list_is_cons(l)) {
        Z head = list_cons_head(l); // generates a universally quantified variable and a pure constraint
        // we generate:
        //     ...
        //       (if is_cons(l) then
        //         hexists head. (pure(head(l) EQ head) SEPAND
        //                        <... ...>)
        //       else <...to be filled further below, but actually absent...>)
        List tail = list_cons_tail(l); // same as above
        LET_SEP(&p->head, Z p_head)    // generates a exists and a data_at. A field access actually
                                       // requires a data_at with field offset and size information.
        LET_SEP(&p->tail, Ptr p_tail)  // same as above
        return PURE(p_head EQ head) SEP list_repr((struct list_cell *)p_tail, tail);
    }
    return BOT;
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

// the subset of C features that can be supported by extraction:
// - local variables (of extractable (ghost) data types)
// - for loop
// - if statement
// - return statement
// - ?: operator
// - function call

// extraction can use the constraint generation approach or multiple functions (continuation points) approach

// a possible substitute for list_reverse
List list_reverse_with_local_var_and_for_loop(List list) {
    List rev_list = list_nil();
    List rem_list = list;
    for (; rem_list != list_nil();) {
        Z head = list_cons_head(rem_list);
        rem_list = list_cons_tail(rem_list);
        rev_list = list_cons(head, rev_list);
    }
    return rev_list;
}

struct list_cell *reverse(struct list_cell *p, List l) {
    require(list_repr(p, l));
    struct list_cell *__result = reverse_original(p, l);
    // construst a wrapper for executable functions because ensure clause must be checked for all
    // possible exit points
    ensure(list_repr(__result, list_reverse(l)));
    return __result;
}

struct list_cell *reverse_original(struct list_cell *p,
                                   const List l) { // ghost level variables cannot be mutated except
                                                   //  on ghost local variables
    struct list_cell *rev_prefix = NULL, *rem_suffix = p;
    List l1 = list_nil(), l2 = l; // ghost local variable (feed to VST-IDE)
#define INV                                                                                                            \
    (PURE(list_equal(list_append(list_reverse(l1), l2), l))                                                            \
         SEPAND (list_repr(rev_prefix, l1) SEP list_repr(rem_suffix, l2) SEP DATA_AT_ANY(&p)))
    for (assert(INV); rem_suffix != NULL; assert(INV)) {
        // Trick: using for-loop to ensure invariant is checked at the begining and at the end of each loop body
#undef INV
        struct list_cell *t;
        assert(rem_suffix != NULL); // Possible hint: tell VST-IDE that rem_suffix is not NULL (unfold the cell)
        t = rem_suffix->tail;
        rem_suffix->tail = rev_prefix;
        rev_prefix = rem_suffix;
        l1 = list_cons(rem_suffix->head, l1); // ghost command
        rem_suffix = t;
        l2 = list_cons_tail(l2); // ghost command
    }
    return rev_prefix;
}

// debug only
void test_list_reverse() {
    List l1 = list_cons(1, list_cons(2, list_cons(3, list_nil())));
    List l1_rev = list_cons(3, list_cons(2, list_cons(1, list_nil())));
    List l2 = list_reverse(l1);
    assert(list_equal(l1_rev, l2));
    list_println_sexp(l1_rev);
    list_println_sexp(l2);
}

int main() {
    test_list_reverse(); // debug only
    struct list_cell *p = &(struct list_cell){1, &(struct list_cell){2, &(struct list_cell){3, NULL}}};
    List l = list_cons(1, list_cons(2, list_cons(3, list_nil())));
    reverse(p, l);
    return 0;
}
