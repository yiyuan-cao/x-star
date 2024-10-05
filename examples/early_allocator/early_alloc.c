// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google, inc
 * Author: Quentin Perret <qperret@google.com>
 */

/* CP: originally at linux/arch/arm64/kvm/hyp/nvhe/early_alloc.c */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define NULL ((void *)0)
#define PAGE_SHIFT 12
#define PAGE_SIZE (1 << PAGE_SHIFT)

// /* CP: originally: #include <asm/kvm_pgtable.h> */

// /* CP: originally: #include <nvhe/memory.h> */
// #include "memory.h"

// /* CP: adding */
// #include "include/page-def.h"
// #include "include/stddef.h"
// #include "include/kvm_pgtable.h"

// /* CP: originally: s64 hyp_physvirt_offset; */
// unsigned long long hyp_physvirt_offset;
// struct kvm_pgtable_mm_ops hyp_early_alloc_mm_ops;

static unsigned long base;
static unsigned long end;
static unsigned long cur;

// [[ghost::datatype(
//     list(),
//     nil(),
//     cons(int head, list tail)
// )]];

// [[ghost::function(
// list append(list l1, list l2)
// {
// 	if(is_nil(l1)) return l2;
// 	else
// 		return cons(head(l1), append(tail(l1), l2));
// }
// )]]

// [[ghost::function(
// list take(list l, int n)
// {
// 	if(n == 0) return nil();
// 	else
// 	{
// 		if(is_nil(l)) return BOT;
// 		else
// 		{
// 			int h = head(l);
// 			list t = tail(l);
// 			return cons(h, take(t, n - 1));
// 		}
// 	}
// }
// )]]

// [[ghost::function(
// list rest(list l, int n)
// {
// 	if(n == 0) return l;
// 	else
// 	{
// 		if(is_nil(l)) return BOT;
// 		else
// 		{
// 			list t = tail(l);
// 			return take(t, n - 1);
// 		}
// 	}
// }
// )]]

// [[ghost::representation(
// bool repr_array(char *addr, int lo, int hi, list l)
// {
// 	if(lo > hi) return false; // HFalse
// 	else if(lo == hi)
// 	{
// 		if(is_nil(l)) return EMP;
// 		return false; // HFalse
// 	}
// 	else
// 	{
// 		int h = head(l);
// 		list t = tail(l);
// 		return (addr + lo) ~> h SEP repr_array(addr, lo + 1, hi, t);
// 	}
// }
// )]]

[[ghost::representation(
bool owned_array(char *addr, int lo, int hi)
{
	if(lo > hi) return false; // HFalse
	else if(lo == hi) return EMP;
	else
	{
		DATA_AT_ANY(addr + lo); // (addr + lo) ~> _
		return owned_array(addr, lo + 1, hi);
	}
}
)]]

[[ghost::representation(
bool zeroed_array(char *addr, int lo, int hi)
{
	if(lo > hi) return false; // HFalse
	else if(lo == hi) return EMP;
	else
	{
		LET_DATA_AT(addr + lo, int val); // (addr + lo) ~> 0
		return PURE(val == 0) SEP zeroed_array(addr, lo + 1, hi);
	}
}
)]]

unsigned long hyp_early_alloc_nr_pages(void)
	[[ghost::require(base <= cur)]]
	[[ghost::ensure(__result == (cur - base) >> PAGE_SHIFT)]]
{
	return (cur - base) >> PAGE_SHIFT;
}

void clear_page(void *to)
	[[ghost::require(owned_array(to, 0, PAGE_SIZE))]]
	[[ghost::ensure(zeroed_array(to, 0, PAGE_SIZE))]]
{    
	int i = 0;   
	[[ghost::invariant(
		PURE(i <= PAGE_SIZE) SEP zeroed_array(to, 0, i) SEP owned_array(to, i, PAGE_SIZE)
	)]]
	while(i < PAGE_SIZE)   
	{
		// need several lemmas - see below
		// lemma1
		[[ghost::assert(
			PURE(i < PAGE_SIZE) SEP 
			zeroed_array(to, 0, i) SEP ((char *)to + i) ~> _ SEP owned_array(to, i + 1, PAGE_SIZE)
		)]]
		*((char *) to+i) = 0;
		i++;
	}; 
}    

void * hyp_early_alloc_page(void *arg)
	[[ghost::require(PURE(0 <= cur && cur + PAGE_SIZE <= end) SEP owned_array(cur, 0, end - cur))]]
	[[ghost::ensure(PURE(__result + PAGE_SIZE == cur) SEP zeroed_array(__result, 0, PAGE_SIZE) SEP owned_array(cur, 0, end - cur))]]
{
	unsigned long ret = cur;

	cur += PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}
	// lemma1
	[[ghost::assert(
		PURE(ret + PAGE_SIZE == cur) SEP owned_array(ret, 0, PAGE_SIZE) SEP owned_array(ret, PAGE_SIZE, end - ret)
	)]]
	clear_page((void*)ret);
	// lemma3

	return (void *)ret;
}

void *hyp_early_alloc_contig(unsigned int nr_pages)
	[[ghost::require(PURE(nr_pages > 0 && (nr_pages * PAGE_SIZE) < UINT_MAX && cur + (nr_pages * PAGE_SIZE) <= end) SEP owned_array(cur, 0, end - cur))]]
	[[ghost::ensure(PURE(__result + (nr_pages * PAGE_SIZE) == cur) SEP zeroed_array(__result, 0, nr_pages * PAGE_SIZE) SEP owned_array(cur, 0, end - cur))]]
{
	unsigned long ret = cur, i, p;

	if (!nr_pages)
		return NULL;

	cur += nr_pages * PAGE_SIZE;
	if (cur > end) {
		cur = ret;
		return NULL;
	}

	i = 0;
	[[ghost::invariant(
		PURE(i <= nr_pages && ret + nr_pages * PAGE_SIZE == cur) SEP zeroed_array(ret, 0, i * PAGE_SIZE) SEP owned_array(ret, i * PAGE_SIZE, end - ret)
	)]]
	while(i < nr_pages)
	{
		// break owned_array -- lemma1
		[[ghost::assert(
			PURE(i < nr_pages && ret + nr_pages * PAGE_SIZE == cur) SEP 
			zeroed_array(ret, 0, i * PAGE_SIZE) SEP 
			owned_array(ret, i * PAGE_SIZE, (i * PAGE_SIZE) + PAGE_SIZE) SEP
			owned_array(ret, (i * PAGE_SIZE) + PAGE_SIZE, end - ret)
		)]]
		p = ret + (i * PAGE_SIZE);
		// change the base addr (from ret to p) -- lemma2
		[[ghost::assert(
			PURE(i < nr_pages && ret + nr_pages * PAGE_SIZE == cur) SEP 
			zeroed_array(ret, 0, i * PAGE_SIZE) SEP 
			owned_array(p, 0, PAGE_SIZE) SEP
			owned_array(ret, (i * PAGE_SIZE) + PAGE_SIZE, end - ret)
		)]]
		clear_page((void *)(p));
		// merge zero_array -- lemma3
		[[ghost::assert(
			PURE(i < nr_pages && ret + nr_pages * PAGE_SIZE == cur) SEP 
			zeroed_array(ret, 0, (i * PAGE_SIZE) + PAGE_SIZE) SEP 
			owned_array(ret, (i * PAGE_SIZE) + PAGE_SIZE, end - ret)
		)]]
		i++;
	}
	// for (i = 0; i < nr_pages; i++) {
	// 	p = ret + (i * PAGE_SIZE);
	// 	clear_page((void *)(p));
	// }

	return (void *)ret;
}

void hyp_early_alloc_init(unsigned long virt, unsigned long size)
	[[ghost::require(owned_array(virt, 0, size))]]
	[[ghost::ensure(PURE(base == virt && end == virt + size && cur == virt) SEP owned_array(virt, 0, size))]]
{
	base = virt;
	end = virt + size;
	cur = virt;

	// hyp_early_alloc_mm_ops.zalloc_page = hyp_early_alloc_page;
	// hyp_early_alloc_mm_ops.phys_to_virt = hyp_phys_to_virt;
	// hyp_early_alloc_mm_ops.virt_to_phys = hyp_virt_to_phys;
}

int main()
{
	return 0;
}
