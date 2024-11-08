#include "vst_ide.h"

void clear(void *to, int len)
/*@
Require
  len >= 0 &&
  store_undef_array(undef_store_char, to, len)
Ensure
  store_array(store_char, to, len@pre, Zrepeat(0, len@pre))
*/
{
    /*@ Assert
      len@pre >= 0 &&
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_undef_array(undef_store_char, to@pre, len@pre)
    */
    int i = 0;
    /*@ Assert
      len@pre >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_undef_array(undef_store_char, to@pre, len@pre)
    */

    // clear_which_implies_wit_1
    /*@
      emp
      which implies
      store_array(store_char, to@pre, 0, Zrepeat(0, 0))
    */

    /*@ Assert
      len@pre >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, 0, Zrepeat(0, 0)) *
      store_undef_array(undef_store_char, to@pre, len@pre)
    */
    // clear_entail_wit_4
    /*@ Assert
      0 <= 0 && 0 <= len@pre &&
      len@pre >= 0 &&
      data_at(&i, int, 0) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, 0, Zrepeat(0, 0)) *
      store_undef_array(undef_store_char, to@pre + 0 * sizeof(char), len@pre - 0)
    */

    /*@ Assert Inv
      exists i_v,
      0 <= i_v && i_v <= len@pre &&
      len@pre >= 0 &&
      data_at(&i, int, i_v) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
      store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), len@pre - i_v)
    */
    while (i < len)
    {
        /*@ Assert
          exists i_v,
          i_v < len@pre &&
          0 <= i_v && i_v <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), len@pre - i_v)
        */

        // clear_which_implies_wit_2
        /*@
          exists i_v,
          i_v < len@pre &&
          0 <= i_v &&
          len@pre >= 0 &&
          store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), len@pre - i_v)
          which implies
          undef_data_at(to@pre + i_v * sizeof(char), char) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
        */

        /*@ Assert
          exists i_v,
          i_v < len@pre &&
          0 <= i_v && i_v <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          undef_data_at(to@pre + i_v * sizeof(char), char) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
        */
        *((char *)to + i) = (char) 0;
        /*@ Assert
          exists i_v,
          i_v < len@pre &&
          0 <= i_v && i_v <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          data_at(to@pre + i_v * sizeof(char), char, 0) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
        */
        i = i + 1;
        /*@ Assert
          exists i_v,
          i_v < len@pre &&
          0 <= i_v && i_v <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
          data_at(to@pre + i_v * sizeof(char), char, 0) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
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
          i_v < len@pre &&
          0 <= i_v && i_v <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v + 1, Zrepeat(0, i_v + 1)) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
        */
        // clear_entail_wit_11
        /*@ Assert
          exists i_v,
          0 <= i_v + 1 && i_v + 1 <= len@pre &&
          len@pre >= 0 &&
          data_at(&i, int, i_v + 1) *
          data_at(&len, int, len@pre) *
          data_at(&to, void*, to@pre) *
          store_array(store_char, to@pre, i_v + 1, Zrepeat(0, i_v + 1)) *
          store_undef_array(undef_store_char, to@pre + (i_v + 1) * sizeof(char), len@pre - (i_v + 1))
        */
    }
    /*@ Assert
      exists i_v,
      i_v >= len@pre &&
      0 <= i_v && i_v <= len@pre &&
      len@pre >= 0 &&
      data_at(&i, int, i_v) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, i_v, Zrepeat(0, i_v)) *
      store_undef_array(undef_store_char, to@pre + i_v * sizeof(char), len@pre - i_v)
    */
    // clear_entail_wit_14
    /*@ Assert
      len@pre >= 0 &&
      data_at(&i, int, len@pre) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, len@pre, Zrepeat(0, len@pre)) *
      store_undef_array(undef_store_char, to@pre + len@pre * sizeof(char), len@pre - len@pre)
    */

    // clear_which_implies_wit_4
    /*@
      store_undef_array(undef_store_char, to@pre + len@pre * sizeof(char), len@pre - len@pre)
      which implies
      emp
    */

    /*@ Assert
      len@pre >= 0 &&
      data_at(&i, int, len@pre) *
      data_at(&len, int, len@pre) *
      data_at(&to, void*, to@pre) *
      store_array(store_char, to@pre, len@pre, Zrepeat(0, len@pre))
    */
}
