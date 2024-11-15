#include "vst_ide.h"

void *malloc(unsigned size)
/*@
Require
  size % 4 == 0
Ensure
  malloc_at(__return, size@pre) *
  store_undef_array(undef_store_int, __return, size / sizeof(int))
*/
;

void free(void *p)
/*@
With
  (size : Z)
Require
  malloc_at(p, size) *
  store_undef_array(undef_store_int, p, size / sizeof(int))
Ensure
  emp
*/
;

void foo()
/*@
Require
  emp
Ensure
  emp
*/
{
  /*@ Assert
    emp
  */
  int *arr = (int *)malloc(2 * sizeof(int));
  /*@ Assert
    exists arr_v,
    data_at(&arr, int*, arr_v) *
    malloc_at(arr_v, 2 * sizeof(int)) *
    store_undef_array(undef_store_int, arr_v, 2 * sizeof(int) / sizeof(int))
  */
  free((void *)arr) /*@ where size = 2 * sizeof(int) */;
  /*@ Assert
    exists arr_v,
    data_at(&arr, int*, arr_v)
  */
}
