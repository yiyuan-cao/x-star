/**
 * datatype header automatically generated by cstar compiler
 * extracted from [[ghost::datatype]] attributes in reverse.c
 * intended for use by reverse_test.c
 */

#ifndef REVERSE_DATATYPE_H
#define REVERSE_DATATYPE_H

#include "cstar.h"
#include <stdbool.h>

/** datatype */
struct list_block;
typedef struct list_block *List;

// users should only use the following functions to create and access List values
// all functions are appended a type name prefix to avoid name clashes

/** constructors */
List list_nil();
List list_cons(Z head, List tail);

/** accessors */
Z list_cons_head(List list);
List list_cons_tail(List list);

/** discriminators */
Bool list_is_nil(List list);
Bool list_is_cons(List list);

/** equality */
Bool list_equal(List list1, List list2);

/** debug only */
void list_println_sexp(List list);

#endif