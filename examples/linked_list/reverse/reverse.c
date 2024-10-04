#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

struct int_ll_node {
    int value;
    struct int_ll_node *next;
};

[[cstar::datatype(
    int_list,
    nil(),
    cons(int head, int_list tail),
)]];

/**
 * defines a type `int_list` together with its constructors, accessors, and discriminators.
 * constructors {
 *     int_list nil(),
 *     int_list cons(int head, int_list tail),
 * }
 * accessors {
 *     int head(int_list l),
 *     int_list tail(int_list l),
 * }
 * discriminators {
 *     bool is_nil(int_list l),
 *     bool is_cons(int_list l),
 * }
 */

/**
 * if a C type or literal appears in the ghost code, it is automatically lifted as its direct logical counterpart.
 * e.g., (!) : bool -> bool ---> (!) : PROP -> PROP
 */
[[cstar::representation(
    HPROP int_ll_repr(struct int_ll_node * p, int_list l) {
        if (is_nil(l)) {
            return PURE(p == NULL) SEPAND EMP;
        } else {
            int h = head(l);
            int_list t = tail(l);
            LET_DATA_AT(&p->value, int, value);                  // Internally DATA_AT_INT(p + 0, value)
            LET_DATA_AT(&p->next, struct int_ll_node*, next);    // DATA_AT_PTR(p + 1, next) (ignore size difference between C values and paddings)
            return PURE(value == h) SEPAND int_ll_repr(next, t);
        }
    }
)]];

[[cstar::function(
    int_list append(int_list l1, int_list l2) {
        return is_nil(l1) ? l2 : cons(head(l1), append(tail(l1), l2));
    }
)]];

[[cstar::function(
    int_list reverse(int_list l) {
        if (is_nil(l)) {
            return l;
        } else {
            int h = head(l);
            int_list rev_t = reverse(tail(l));
            return append(rev_t, cons(h, nil()));
        }
    }
)]];

// Not used: for syntax test only
[[cstar::predicate(
    PROP int_list_eq(int_list l1, int_list l2) {
        return is_nil(l1) ? is_nil(l2) : (is_cons(l1) && is_cons(l2) && head(l1) == head(l2) && int_list_eq(tail(l1), tail(l2)));
    }
)]];

// Another version of reverse, possibly supported in the future.
[[cstar::function(
    int_list reverse_with_local_var_and_for_loop(int_list l) {
        int_list rev_list = nil();
        int_list rem_list = l;
        while (is_cons(rem_list)) {
            int head = head(rem_list);
            rem_list = tail(rem_list);
            rev_list = cons(head, rev_list);
        }
        return rev_list;
    }
)]];

struct int_ll_node *int_ll_reverse(struct int_ll_node *p)
    [[cstar::parameter(int_list p)]]
    [[cstar::require(int_ll_repr(p, l))]]
    [[cstar::ensure(int_ll_repr(__result, reverse(l)))]]
{
    struct int_ll_node *rev_prefix = NULL, *rem_suffix = p;
    [[cstar::localvar(int_list l1 = nil(), l2 = l)]];
    [[cstar::invariant(
            (append(reverse(l1), l2) == l) SEPAND
            (int_ll_repr(rev_prefix, l1) SEP
             int_ll_repr(rem_suffix, l2) SEP
             DATA_AT_ANY(&p)))]]
    while (rem_suffix != NULL)
    {
        struct int_ll_node *t;
        [[cstar::assert(is_cons(l2))]];
        t = rem_suffix->next;
        rem_suffix->next = rev_prefix;
        rev_prefix = rem_suffix;
        [[cstar::command(l1 = cons(rem_suffix->value, l1))]];
        rem_suffix = t;
        [[cstar::command(l2 = tail(l2))]];
    }
    return rev_prefix;
}

int main() {
    struct int_ll_node *p = &(struct int_ll_node){1, &(struct int_ll_node){2, &(struct int_ll_node){3, NULL}}};
    [[cstar::localvar(int_list l = cons(1, cons(2, cons(3, nil()))))]];
    struct int_ll_node *q;
    [[cstar::argument(l)]] q = int_ll_reverse(p);
    return 0;
}
