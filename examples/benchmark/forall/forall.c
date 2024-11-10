// https://github.com/verifast/verifast/blob/b351656ae5b89afe0539be4c3c2703af8dc94c90/examples/forall.c

#include "vst_ide.h"

void increment_all(int* a, int N)
/*@
With
  (l : list Z)
Require
  store_array(store_int, a, N, l)
Ensure
  store_array(store_int, a@pre, N@pre, map(Zadd(1), l))
*/
{
  /*@ Assert
    store_array(store_int, a@pre, N@pre, l) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre)
  */
  int k = 0;
  /*@ Assert
    store_array(store_int, a@pre, N@pre, l) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, 0)
  */

  // increment_all_which_implies_wit_1
  /*@
    store_array(store_int, a@pre, N@pre, l)
    which implies
    store_array(store_int, a@pre, 0, map(Zadd(1), sublist(0, 0, l))) *
    store_array(store_int, a@pre + 0 * sizeof(int), N@pre, sublist(0, N@pre, l))
  */

  /*@ Assert
    store_array(store_int, a@pre, 0, map(Zadd(1), sublist(0, 0, l))) *
    store_array(store_int, a@pre + 0 * sizeof(int), N@pre, sublist(0, N@pre, l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, 0)
  */
  // increment_all_entail_wit_4
  /*@ Assert
    0 <= 0 && 0 <= N@pre &&
    store_array(store_int, a@pre, 0, map(Zadd(1), sublist(0, 0, l))) *
    store_array(store_int, a@pre + 0 * sizeof(int), N@pre, sublist(0, N@pre, l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, 0)
  */
  /*@ Assert Inv
    exists k_v,
    0 <= k_v && k_v <= N@pre &&
    store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
    store_array(store_int, a@pre + k_v * sizeof(int), N@pre, sublist(k_v, N@pre, l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, k_v)
  */
  while(k < N)
  {
    /*@ Assert
      exists k_v,
      k_v < N@pre &&
      0 <= k_v && k_v <= N@pre &&
      store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
      store_array(store_int, a@pre + k_v * sizeof(int), N@pre, sublist(k_v, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v)
    */

    // increment_all_which_implies_wit_2
    /*@
      exists k_v,
      k_v < N@pre &&
      0 <= k_v &&
      store_array(store_int, a@pre + k_v * sizeof(int), N@pre, sublist(k_v, N@pre, l))
      which implies
      data_at(a@pre + k_v * sizeof(int), int, Znth(k_v, l, 0)) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l))
    */

    /*@ Assert
      exists k_v,
      k_v < N@pre &&
      0 <= k_v && k_v <= N@pre &&
      store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
      data_at(a@pre + k_v * sizeof(int), int, Znth(k_v, l, 0)) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v)
    */
    a[k] = a[k] + 1;
    /*@ Assert
      exists k_v,
      k_v < N@pre &&
      0 <= k_v && k_v <= N@pre &&
      store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
      data_at(a@pre + k_v * sizeof(int), int, Znth(k_v, l, 0) + 1) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v)
    */
    k++;
    /*@ Assert
      exists k_v,
      k_v < N@pre &&
      0 <= k_v && k_v <= N@pre &&
      store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
      data_at(a@pre + k_v * sizeof(int), int, Znth(k_v, l, 0) + 1) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v + 1)
    */

    // increment_all_which_implies_wit_3
    /*@
      exists k_v,
      store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
      data_at(a@pre + k_v * sizeof(int), int, Znth(k_v, l, 0) + 1)
      which implies
      store_array(store_int, a@pre, k_v + 1, map(Zadd(1), sublist(0, k_v + 1, l)))
    */

    /*@ Assert
      exists k_v,
      k_v < N@pre &&
      0 <= k_v && k_v <= N@pre &&
      store_array(store_int, a@pre, k_v + 1, map(Zadd(1), sublist(0, k_v + 1, l))) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v + 1)
    */
    // increment_all_entail_wit_11
    /*@ Assert
      exists k_v,
      0 <= k_v + 1 && k_v + 1 <= N@pre &&
      store_array(store_int, a@pre, k_v + 1, map(Zadd(1), sublist(0, k_v + 1, l))) *
      store_array(store_int, a@pre + (k_v + 1) * sizeof(int), N@pre, sublist(k_v + 1, N@pre, l)) *
      data_at(&a, int*, a@pre) *
      data_at(&N, int, N@pre) *
      data_at(&k, int, k_v + 1)
    */
  }
  /*@ Assert
    exists k_v,
    k_v >= N@pre &&
    0 <= k_v && k_v <= N@pre &&
    store_array(store_int, a@pre, k_v, map(Zadd(1), sublist(0, k_v, l))) *
    store_array(store_int, a@pre + k_v * sizeof(int), N@pre, sublist(k_v, N@pre, l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, k_v)
  */
  // increment_all_entail_wit_14
  /*@ Assert
    store_array(store_int, a@pre, N@pre, map(Zadd(1), sublist(0, N@pre, l))) *
    store_array(store_int, a@pre + N@pre * sizeof(int), N@pre, sublist(N@pre, N@pre, l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, N@pre)
  */

  // increment_all_which_implies_wit_4
  /*@
    store_array(store_int, a@pre, N@pre, map(Zadd(1), sublist(0, N@pre, l))) *
    store_array(store_int, a@pre + N@pre * sizeof(int), N@pre, sublist(N@pre, N@pre, l))
    which implies
    store_array(store_int, a@pre, N@pre, map(Zadd(1), l))
  */

  /*@ Assert
    store_array(store_int, a@pre, N@pre, map(Zadd(1), l)) *
    data_at(&a, int*, a@pre) *
    data_at(&N, int, N@pre) *
    data_at(&k, int, N@pre)
  */
}