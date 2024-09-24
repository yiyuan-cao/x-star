// C + ghost code written by the programmer.
// using ghost code for executable specification and imperative-style proof hints.

#include <stdlib.h>
#include <stdio.h>

struct list_cell {
    int head;
    struct list_cell *tail;
};

[[ghost::datatype(List(/* no type variables */), nil(), cons(Z head, List tail))]];
// generates accessors, constructors, and discriminators that can be used in ghost code

[[ghost::representation(HProp list_repr(struct list_cell * p, List l) {
    if (list_is_nil(l)) {
        return PURE(p_val EQ VAL(NULL)) SEPAND EMP;
    }
    if (list_is_cons(l)) {
        Z head = list_cons_head(l);
        List tail = list_cons_tail(l);
        LET_SEP(&p->head, Z p_head)
        LET_SEP(&p->tail, Ptr p_tail)
        return PURE(p_head EQ head) SEP list_repr((struct list_cell *)p_tail, tail);
    }
    return BOT;
})]];

[[ghost::function(List list_append(List list1, List list2) {
    return list_is_nil(list1) ? list2 : list_cons(list_cons_head(list1), list_append(list_cons_tail(list1), list2));
})]];

[[ghost::function(List list_reverse(List list) {
    if (list_is_nil(list)) {
        return list;
    }
    Z head = list_cons_head(list);
    List rev_tail = list_reverse(list_cons_tail(list));
    return list_append(rev_tail, list_cons(head, list_nil()));
})]];

// extraction can use the constraint generation approach or multiple functions (continuation points) approach

// the subset of C features that can be supported by extraction:
// - local variables (of extractable (ghost) data types)
// - for loop
// - if statement
// - return statement
// - ?: operator
// - function call
// a possible substitute for list_reverse
[[ghost::function(List list_reverse_with_local_var_and_for_loop(List list) {
    List rev_list = list_nil();
    List rem_list = list;
    for (; rem_list != list_nil();) {
        Z head = list_cons_head(rem_list);
        rem_list = list_cons_tail(rem_list);
        rev_list = list_cons(head, rev_list);
    }
    return rev_list;
})]];

// struct list_cell *reverse(struct list_cell *p, List l) {
//     struct list_cell *__result = reverse_original(p, l);
//     // construst a wrapper for executable functions because ensure clause must be checked for all
//     // possible exit points
//     ensure(list_repr(__result, list_reverse(l)));
//     return __result;
// }

void print_linked_list(struct list_cell *p) {
    while (p != NULL) {
        printf("%d ", p->head);
        p = p->tail;
    }
    printf("\n");
}

struct list_cell *reverse(struct list_cell *p)
    [[ghost::parameter(List l)]]
    [[ghost::require(list_repr(p, l))]]
    [[ghost::ensure(list_repr(p, list_reverse(l)))]]
{
    struct list_cell *rev_prefix = NULL, *rem_suffix = p;
    [[ghost::localvar(List l1 = list_nil(), l2 = l)]]; // ghost local variable, must be initialized
    [[ghost::invariant((PURE(list_equal(list_append(list_reverse(l1), l2), l))
                            SEPAND(list_repr(rev_prefix, l1) SEP list_repr(rem_suffix, l2) SEP DATA_AT_ANY(&p))))]] // no `;`, attached to the while loop below
    while (rem_suffix != NULL) {
        struct list_cell *t;
        [[ghost::assert(rem_suffix != NULL)]]; // Possible hint: tell VST-IDE that rem_suffix is not NULL (unfold the cell)
        t = rem_suffix->tail;
        rem_suffix->tail = rev_prefix;
        rev_prefix = rem_suffix;
        [[ghost::command(l1 = list_cons(rem_suffix->head, l1))]];
        rem_suffix = t;
        [[ghost::command(l2 = list_cons_tail(l2))]];
    }
    return rev_prefix;
}

[[ghost::debug(void test_list_reverse() {
    List l1 = list_cons(1, list_cons(2, list_cons(3, list_nil())));
    List l1_rev = list_cons(3, list_cons(2, list_cons(1, list_nil())));
    List l2 = list_reverse(l1);
    assert(list_equal(l1_rev, l2));
    list_println_sexp(l1_rev);
    list_println_sexp(l2);
})]];

#define DEBUG

int main() {
    [[ghost::debug(test_list_reverse())]]; // debug only
    struct list_cell *p = &(struct list_cell){1, &(struct list_cell){2, &(struct list_cell){3, NULL}}};
    #ifdef DEBUG
    print_linked_list(p);
    #endif
    [[ghost::localvar(List l = list_cons(1, list_cons(2, list_cons(3, list_nil()))))]];
    [[ghost::argument(l)]] // attached to the function call, used to pass ghost arguments
    struct list_cell *q = reverse(p);
    #ifdef DEBUG
    print_linked_list(q);
    #endif
    return 0;
}
