#include "vst_ide.h"

void clear(void *to, int len)
/*@
With
  (n : Z)
Require
  n >= 0 &&
  len == n &&
  store_undef_array(undef_store_char, to, n)
Ensure
  store_array(store_char, to, n, Zrepeat(0, n))
*/
{
    /*@ Assert
      n >= 0 &&
      len@pre == n &&
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_undef_array(undef_store_char, to@pre, n)
    */
    // clear_entail_wit_2
    /*@ Assert
      n >= 0 &&
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_undef_array(undef_store_char, to@pre, n)
    */
    int i = 0;
    /*@ Assert
      n >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_undef_array(undef_store_char, to@pre, n)
    */

    // clear_which_implies_wit_1
    /*@
      emp
      which implies
      store_array(store_char, to@pre, 0, Zrepeat(0, 0))
    */

    /*@ Assert
      n >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, 0, Zrepeat(0, 0)) *
      store_undef_array(undef_store_char, to@pre, n)
    */
    // clear_entail_wit_5
    /*@ Assert
      0 <= 0 && 0 <= n &&
      n >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, 0, Zrepeat(0, 0)) *
      store_undef_array(undef_store_char, to@pre + 0 * sizeof(char), n - 0)
    */

    /*@ Assert Inv
      exists i_v,
      0 <= i_v && i_v <= n &&
      n >= 0 &&
      data_at(&i, int, i_v) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
      store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), n - i_v)
    */
    while (i < len)
    {
        /*@ Assert
          exists i_v,
          i_v < n &&
          0 <= i_v && i_v <= n &&
          n >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), n - i_v)
        */

        // clear_which_implies_wit_2
        /*@
          exists i_v,
          i_v < n &&
          n >= 0 &&
          store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), n - i_v)
          which implies
          undef_data_at(to@pre + i_v * sizeof(char), char) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */

        /*@ Assert
          exists i_v,
          i_v < n &&
          0 <= i_v && i_v <= n &&
          n >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          undef_data_at(to@pre + i_v * sizeof(char), char) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */
        *((char *)to + i) = (char) 0;
        /*@ Assert
          exists i_v,
          i_v < n &&
          0 <= i_v && i_v <= n &&
          n >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          data_at(to@pre + i_v * sizeof(char), char, 0) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */
        i = i + 1;
        /*@ Assert
          exists i_v,
          i_v < n &&
          0 <= i_v && i_v <= n &&
          n >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          data_at(to@pre + i_v * sizeof(char), char, 0) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */

        // clear_which_implies_wit_3
        /*@
          exists i_v,
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          data_at(to@pre + i_v * sizeof(char), char, 0)
          which implies
          store_array(store_char, to@pre, i_v + 1, Zrepeat(0, i_v + 1))
        */

        /*@ Assert
          exists i_v,
          i_v < n &&
          0 <= i_v && i_v <= n &&
          n >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v + 1, Zrepeat(0, i_v + 1)) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */
        // clear_entail_wit_12
        /*@ Assert
          exists i_v,
          0 <= i_v + 1 && i_v + 1 <= n &&
          n >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, n) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v + 1, Zrepeat(0, i_v + 1)) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), n - (i_v + 1))
        */
    }
    /*@ Assert
      exists i_v,
      i_v >= n &&
      0 <= i_v && i_v <= n &&
      n >= 0 &&
      data_at(&i, int, i_v) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
      store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), n - i_v)
    */
    // clear_entail_wit_15
    /*@ Assert
      n >= 0 &&
      data_at(&i, int, n) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, n, Zrepeat(0, n)) *
      store_undef_array(undef_store_char, to@pre + n * sizeof(char), n - n)
    */

    // clear_which_implies_wit_4
    /*@
      store_undef_array(undef_store_char, to@pre + n * sizeof(char), n - n)
      which implies
      emp
    */

    /*@ Assert
      n >= 0 &&
      data_at(&i, int, n) *
      data_at(&len, int, n) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, n, Zrepeat(0, n))
    */
}