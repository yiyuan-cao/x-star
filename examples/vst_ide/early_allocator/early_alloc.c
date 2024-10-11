// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* CP: originally at linux/arch/arm64/kvm/hyp/nvhe/early_alloc.c */


/* CP: originally: #include <asm/kvm_pgtable.h> */

/* CP: originally: #include <nvhe/memory.h> */
// #include "memory.h"

/* CP: adding */
#include "include/page-def.h"
#include "include/stddef.h"
// #include "include/kvm_pgtable.h"

#include "vst_ide.h"

/* CP: originally: s64 hyp_physvirt_offset; */
unsigned long long hyp_physvirt_offset;
// struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

static unsigned long base;
static unsigned long end_;
static unsigned long cur;

unsigned long hyp_early_alloc_nr_pages()
/*@
Require
  base <= cur
Ensure
  __return == (cur - base) >> PAGE_SHIFT
*/
{
	return (cur - base) >> PAGE_SHIFT;
}

/* CP: originally: extern void clear_page(void *to); */
/* CP: instead, making up a definition of this */
void clear_page(void *to)
/*@
Require
  store_undef_array(undef_store_char, to, PAGE_SIZE)
Ensure
  store_array(store_char, to, PAGE_SIZE, repeat(0, Z_to_nat(PAGE_SIZE)))
*/
{                                                           /*RCIGNORE*/
  int i = 0;                                                /*RCIGNORE*/
  /*@ Inv
	0 <= i && i <= 4096 &&
    to == to@pre &&
	store_array(store_char, to, i, repeat(0, Z_to_nat(i))) &&
	store_undef_array_rec(undef_store_char, to, i, PAGE_SIZE, Z_to_nat(PAGE_SIZE - i))
  */
  while(i < 4096)                                           /*RCIGNORE*/
  {                                                         /*RCIGNORE*/
	/*@
	  0 <= i && i < 4096 &&
	  store_undef_array_rec(undef_store_char, to, i, PAGE_SIZE, Z_to_nat(PAGE_SIZE - i))
	  which implies
	  undef_data_at(to + i * sizeof(char), char) &&
	  store_undef_array_rec(undef_store_char, to, i + 1, PAGE_SIZE, Z_to_nat(PAGE_SIZE - (i + 1)))
	*/
    *((char *) to+i) = (char) 0;                                   /*RCIGNORE*/
	/*@
	  0 <= i &&
	  data_at(to + i * sizeof(char), char, 0) &&
	  store_array(store_char, to, i, repeat(0, Z_to_nat(i)))
	  which implies
	  store_array(store_char, to, i + 1, repeat(0, Z_to_nat(i + 1)))
	*/
    i++;                                                    /*RCIGNORE*/
  };                                                        /*RCIGNORE*/
}                                                           /*RCIGNORE*/

void * hyp_early_alloc_page(void *arg)
/*@
Require
  cur + PAGE_SIZE <= end_ &&
  store_undef_array(undef_store_char, cur, end_ - cur)
Ensure
  cur == cur@pre + PAGE_SIZE &&
  __return == cur@pre &&
  store_array(store_char, __return, PAGE_SIZE, repeat(0, Z_to_nat(PAGE_SIZE))) &&
  store_undef_array(undef_store_char, cur, end_ - cur)
*/
{
	/*@
	  cur >= 0
	*/
	unsigned long ret = cur;

	cur += PAGE_SIZE;
	if (cur > end_) {
		cur = ret;
		return NULL;
	}
	/*@
	  ret + PAGE_SIZE == cur && cur <= end_ &&
      store_undef_array(undef_store_char, ret, end_ - ret)
	  which implies
      store_undef_array(undef_store_char, ret, PAGE_SIZE) &&
      store_undef_array(undef_store_char, cur, end_ - cur)
	*/
	clear_page((void*)ret);

	return (void *)ret;
}

/* CP: We also include this variant of hyp_early_alloc_page that
   allocates a number of pages, as found in newer versions of
   early_alloc.c */
void *hyp_early_alloc_contig(unsigned int nr_pages)
/*@
Require
  0 < nr_pages &&
  nr_pages * PAGE_SIZE <= UINT_MAX &&
  cur + nr_pages * PAGE_SIZE <= end_ &&
  store_undef_array(undef_store_char, cur, end_ - cur)
Ensure
  cur == cur@pre + nr_pages * PAGE_SIZE &&
  __return == cur@pre &&
  store_array(store_char, __return, nr_pages * PAGE_SIZE, repeat(0, Z_to_nat(nr_pages * PAGE_SIZE))) &&
  store_undef_array(undef_store_char, cur, end_ - cur)
*/
{
	/*@
	  cur >= 0
	*/
	unsigned long ret = cur, i, p;

	if (!nr_pages)
		return NULL;

	cur += (unsigned long)(nr_pages << PAGE_SHIFT);
	if (cur > end_) {
		cur = ret;
		return NULL;
	}

    /*@ Inv
	  0 <= i && i <= nr_pages@pre &&
	  ret == cur@pre && end_ == end_@pre &&
	  store_array(store_char, ret, i * PAGE_SIZE, repeat(0, Z_to_nat(i * PAGE_SIZE))) &&
	  store_undef_array(undef_store_char, ret + i * PAGE_SIZE, end_ - (ret + i * PAGE_SIZE))
	*/
	for (i = 0; i < (unsigned long)nr_pages; i++) {                    /*RCIGNORE*/
		p = ret + (i << PAGE_SHIFT);                /*RCIGNORE*/
		/*@
		  i < nr_pages && p == ret + i * PAGE_SIZE && ret + nr_pages * PAGE_SIZE <= end_ &&
	      store_undef_array(undef_store_char, ret + i * PAGE_SIZE, end_ - (ret + i * PAGE_SIZE))
		  which implies
		  i == i && nr_pages == nr_pages && ret == ret &&
	      store_undef_array(undef_store_char, p, PAGE_SIZE) &&
	      store_undef_array(undef_store_char, p + PAGE_SIZE, end_ - (p + PAGE_SIZE))
		*/
		clear_page((void *)(p));                    /*RCIGNORE*/
		/*@
		  i >= 0 && p == ret + i * PAGE_SIZE &&
	      store_array(store_char, ret, i * PAGE_SIZE, repeat(0, Z_to_nat(i * PAGE_SIZE))) &&
		  store_array(store_char, p, PAGE_SIZE, repeat(0, Z_to_nat(PAGE_SIZE))) &&
	      store_undef_array(undef_store_char, p + PAGE_SIZE, end_ - (p + PAGE_SIZE))
		  which implies
		  p == p &&
	      store_array(store_char, ret, (i + 1) * PAGE_SIZE, repeat(0, Z_to_nat((i + 1) * PAGE_SIZE))) &&
	      store_undef_array(undef_store_char, ret + (i + 1) * PAGE_SIZE, end_ - (ret + (i + 1) * PAGE_SIZE))
		*/
	}                                                   /*RCIGNORE*/

	return (void *)ret;
}

// void hyp_early_alloc_init(unsigned long virt, unsigned long size)
// {
// 	base = virt;
// 	end_ = virt + size;
// 	cur = virt;

// 	hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
// 	hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
// 	hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
// }
