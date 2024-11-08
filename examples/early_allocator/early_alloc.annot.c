// DEV notes:
//   Possible syntactric improvements: syntax for repeat ([x] * n), append (x ++ y), list slice (x[i..j]), ...
//   Use early return to get the symbolic state __state at a program point, and manually insert a [[cstar::assert]].
//   No extraction in this example: all object logic-level entities are in quotes.
//   For now, we can also delegate directly to VST-IDE support for `which-implies`.
//   Add [[cstar::assert]] before and after [[cstar::proof]] to see communication with VST-IDE.
// CStar attributes:
//   MUST support: proof, require, ensure, assert, invariant, parameter, argument
//   OPTIONAL: type (check the type of an object logic term)
// Possible issues:
//   Negative number syntax is different from C: -1 vs (--(&1))
//   Only allows antiquotation of `term`-typed variables of object logic type `:hprop`

typedef void* term;
typedef void* thm;

typedef long int ptrdiff_t;
typedef long unsigned int size_t;
typedef int wchar_t;

size_t base;
size_t end;
size_t cur;

size_t hyp_early_alloc_nr_pages(void)
    [[cstar::parameter(`_base : Z`)]]
    [[cstar::parameter(`_cur : Z`)]]
    [[cstar::require(`
        fact(_base <= _cur) **
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    `)]]
    [[cstar::ensure(`
        fact(__result == (_cur - _base) / &4096) **
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    `)]]
{
 return (cur - base) >> 12;
}

[[cstar::function(


term in_range(
     term i,
     term lo,
     term hi
) {
    return `${lo:int} <= ${i:int} && ${i:int} <= ${hi:int}`;
}

// Above is a meta-level function definition that assembles object logic terms.
// An alternative is to define a object logic level function, e.g.
//     thm in_range_def = define `in_range(i:int, lo:int, hi:int) = lo <= i && i <= hi`;
// Choose meta-level function definition over object logic level definition if it's just for simple `macros` in the object logic terms.
// Object logic level definition is useful if it has general properties or should be folded most of the time.
// Moreover, one can also provide a meta-level function definition that returns the application of the object logic level function, e.g.
//     term in_range_app(term i, term lo, term hi) { return `in_range(${i}, ${lo}, ${hi})`; }
// Although I don't see much value in this.
)]];

[[cstar::function(


term splitted_array_at(
     term i
) {
    return `
        array_at(_to, Tchar, ireplicate(${i:int}, &0)) **
        undef_slice_at(_to, Tchar, ${i:int}, &4096 - ${i:int})
    `;
}

)]];

void clear_page(void *to)
    [[cstar::require(`
        undef_array_at(to, Tchar, &4096)
    `)]]
    [[cstar::ensure(`
        array_at(to, Tchar, ireplicate(&4096, &0))
    `)]]
{
    [[cstar::assert(`
        exists (_to:addr).
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `)]]; // All cstar::asserts are obtained from symbolic execution results (with manual fixes)

    int i = 0;

    [[cstar::assert(`
        exists (_i:Z) (_to:addr).
        fact(_i == &0) **
        data_at(&"i", Tint, _i) **
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `)]];

    [[cstar::proof( // Proof blocks have function scope inside of functions

        
        term locals = `
            data_at(&"i", Tint, _i) **
            data_at(&"to", Tptr, _to)
        `;

        
        term whole_array = `
            undef_array_at(_to, Tchar, &4096)
        `;

        

        term splitted_array_at_i = splitted_array_at(`_i:int`);
        // Clumsy because don't support expression in antiquotation for now...

        tmp_goal = `
            _i == &0 // under these facts that holds at this point
            ==>
            (${whole_array:hprop}
            |--
            ${splitted_array_at_i:hprop})
        `;

        // ... constructing actual proof steps here ...

        term tm1 = `_i == &0`;
        term tm3 = `undef_slice_at(_to, Tchar, _i, &4096 - _i)`;
        term tm4 = `array_at(_to, Tchar, ireplicate(_i, &0))`;
        thm th1 = ASSUME(tm1);
        // (_i:int) == &0 |- (_i:int) == &0
        thm th2 = ONCE_REWRITE_CONV1(undef_array_at_def, whole_array);;
        // |- undef_array_at ((_to:int),Tchar,&4096) 
        //-|- undef_slice_at ((_to:int),Tchar,&0,&4096)
        thm minus0 = ARITH_RULE(`! (a : int). a - &0 = a`);
        thm th3 = REWRITE_CONV2(th1, minus0, tm3);
        // (_i:int) == &0
        // |- undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        //-|- undef_slice_at ((_to:int),Tchar,&0,&4096)
        thm th4 = TRANS(th2, SYM(th3));
        // (_i:int) == &0
        // |- undef_array_at ((_to:int),Tchar,&4096) 
        //-|- undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        // numofint0 : (num_of_int (&0)) == 0
        // thm th5 = REWRITE_CONV [th1; array_at_def; slice_at_def; hiter_irange0_def; hiter_def; ireplicate_def; dy0; REPLICATE; ilength_def; LENGTH; irange0_def; list_of_seq; MAP; ITLIST] tm4;
        thm array_at_0 = new_axiom(`! x ty c. array_at (x, ty, ireplicate(&0, c)) -|- emp`);
        thm th5 = REWRITE_CONV2(th1, array_at_0, tm3);
        // (_i:int) == &0
        // |- array_at ((_to:int),Tchar,ireplicate ((_i:int),&0)) -|- emp
        thm th6 = ONCE_REWRITE_CONV1(hsep_hemp_left, mk_comb(mk_comb(`**`, `emp`), tm3));
        // |- emp ** undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        //-|- undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        thm th7 = TRANS(th4, SYM(th6));
        // (_i:int) == &0
        // |- undef_array_at ((_to:int),Tchar,&4096) 
        //-|- emp ** undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        thm th8 = ONCE_REWRITE_RULE1(SYM(th5), th7);
        // (_i:int) == &0
        // |- undef_array_at ((_to:int),Tchar,&4096)
        //-|- array_at ((_to:int),Tchar,ireplicate ((_i:int),&0)) **
        //    undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        thm iff_imp = new_axiom(`! hp1 hp2. (hp1 -|- hp2) ==> (hp1 |-- hp2)`);
        thm th9 = MATCH_MP(iff_imp, th8);
        // (_i:int) == &0
        // |- undef_array_at ((_to:int),Tchar,&4096)
        // |-- array_at ((_to:int),Tchar,ireplicate ((_i:int),&0)) **
        //     undef_slice_at ((_to:int),Tchar,(_i:int),&4096 - (_i:int))
        split_thm = DISCH(tm1, th9);

        // thm split_thm = axiom(tmp_goal);

        // apply the partial transformation to the symbolic state
        // __transform = which_implies(__state, split_thm);
        __transform = axiom(`
            ${__state:hprop}
            |--
            exists (_i:Z) (_to:addr).
            fact(_i == &0) **
            ${locals:hprop} **
            ${splitted_array_at_i:hprop}
        `);

    )]]; // this block split the array into two parts

    [[cstar::proof(

        
        term i_in_range = in_range(`_i:int`, `&0`, `&4096`);

        tmp_goal = `
            fact(_i == &0)
            |--
            fact(${i_in_range:bool})
        `;

        // ... constructing actual proof steps here ...
        term tm1 = `(_i : int) = &0`;
        term tm2 = `&0 <= &0 && &0 <= &4096`;
        thm th1 = ASSUME(tm1);
        // (_i:int) == &0 |- (_i:int) == &0
        thm th2 = ONCE_REWRITE_CONV1(th1, i_in_range);
        // (_i:int) == &0 |- ${i_in_range} = &0 <= &0 && &0 <= &4096
        thm th3 = ONCE_REWRITE_RULE1(ARITH_RULE(tm2), th2);
        // (_i:int) == &0 |- ${i_in_range}
        thm th4 = SPEC(`emp`, hentail_refl);
        // |- emp |-- emp
        thm th5 = MATCH_MP(MATCH_MP(hpure_intro, th3), th4);
        // (_i:int) == &0 |- emp |-- hpure ${i_in_range} && emp
        thm th6 = DISCH(tm1, th5);
        // |- (_i:int) == &0 ==> emp |-- hpure ${i_in_range} && emp
        thm th7 = MATCH_MP(hpure_elim, th6);
        // |- hpure (_i:int) == &0 && emp |-- hpure ${i_in_range} && emp
        thm th8 = REWRITE_CONV1(hfact_def, tmp_goal);
        // tmp_goal = hpure (_i:int) == &0 && emp |-- hpure ${i_in_range} && emp
        tmp_thm = REWRITE_CONV1(SYM(th8), th7);

        // tmp_thm = axiom(tmp_goal);

        __transform = axiom(`
            ${__state:hprop}
            |--
            exists (_i:Z) (_to:addr).
            fact(${i_in_range:bool}) **
            ${locals:hprop} **
            ${splitted_array_at_i:hprop}
        `);

    )]]; // This block establishes the invariant initially


    [[cstar::invariant(`
        exists (_i:Z) (_to:addr).
        fact(${i_in_range:bool}) **
        ${locals:hprop} **
        ${splitted_array_at_i:hprop}
    `)]]

    while (i < 4096)
    {
        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            fact(_i < &4096) **
            fact(${i_in_range:bool}) **
            ${locals:hprop} **
            ${splitted_array_at_i:hprop}
        `)]];

        [[cstar::proof(

            term before_split = `
                fact(_i < &4096) **
                fact(${i_in_range:bool}) **
                undef_slice_at(_to, Tchar, _i, &4096 - _i)
            `;

            term i_plus_in_range = in_range(`_i + (&1)`, `&1`, `&4096`); // greater than 0 is necessary

            term after_split = `
                fact(${i_plus_in_range:bool}) **
                undef_data_at(_to + _i * size_of(Tchar), Tchar) ** // What does VST-IDE need here?
                undef_slice_at(_to, Tchar, _i + 1, &4096 - (_i + 1))
            `;

            tmp_goal = `
                ${before_split:hprop}
                |--
                ${after_split:hprop}
            `;

            // ... constructing actual proof steps here ...
            term tm1 = `_i < &4096`;
            term tm2 = `(_i : int) < &4096 ==> &4096 - (_i + &1) >= &0`;
            term tm3 = `&4096 - _i = &1 + (&4096 - (_i + &1))`;
            term tm4 = `undef_slice_at(_to, Tchar, _i, &4096 - _i)`;
            term tm5 = `&1 >= &0`;
            term tm6 = `fact(${i_in_range:bool})`;
            thm th1 = ASSUME(tm1);
            // _i < &4096 |- _i < &4096
            thm th2 = MATCH_MP(ARITH_RULE(tm2), th1);
            // _i < &4096 |- &4096 - (_i + &1) >= &0
            thm th3 = ONCE_REWRITE_CONV1(ARITH_RULE(tm3), tm4);
            // |- undef_slice_at(_to, Tchar, _i, &4096 - _i)
            //-|- undef_slice_at(_to, Tchar, _i, &1 + (&4096 - (_i + &1)))
            thm undef_slice_split = new_axiom(`!x ty i n1 n2. (n1 >= &0) ==> (n2 >= &0) ==> undef_slice_at (x, ty, i, n1 + n2) -|- undef_slice_at (x, ty, i, n1) ** undef_slice_at (x, ty, i + n1, n2)`);
            thm th4 = MATCH_MP(MATCH_MP(undef_slice_split, ARITH_RULE(tm5)), th2);
            // _i < &4096
            // |- !x ty i. undef_slice_at(x, ty, i, &1 + (&4096 - (_i + &1)))
            //-|- undef_slice_at(x, ty, i, &1) ** undef_slice_at(x, ty, i + &1, &4096 - (_i + &1))
            thm th5 = ONCE_REWRITE_RULE1(th4, th3);
            // _i < &4096
            // |- undef_slice_at(_to, Tchar, _i, &4096 - _i)
            //-|- undef_slice_at(_to, Tchar, _i, &1) ** undef_slice_at (_to, Tchar, _i + &1, &4096 - (_i + &1))
            thm undef_slice_at1 = new_axiom(`! x ty i. undef_slice_at(x, ty, i, &1) -|- undef_data_at(x + i * size_of(ty), ty)`);
            thm th6 = ONCE_REWRITE_RULE1(undef_slice_at1, th5);
            // _i < &4096
            // |- undef_slice_at(_to, Tchar, _i, &4096 - _i)
            //-|- undef_data_at(_to + _i * size_of(Tchar), Tchar) ** undef_slice_at (_to, Tchar, _i + &1, &4096 - (_i + &1))
            thm iff_imp = new_axiom(`! hp1 hp2. (hp1 -|- hp2) ==> (hp1 |-- hp2)`);
            thm th7 = MATCH_MP(iff_imp, th6);
            // _i < &4096
            // |-  undef_slice_at(_to, Tchar, _i, &4096 - _i)
            // |-- undef_data_at(_to + _i * size_of(Tchar), Tchar) ** undef_slice_at (_to, Tchar, _i + &1, &4096 - (_i + &1))
            thm th8 = SPEC(tm6, MATCH_MP(hsep_cancel_left, th7));
            // _i < &4096
            // |-  fact(${i_in_range:bool}) ** undef_slice_at(_to, Tchar, _i, &4096 - _i)
            // |-- fact(${i_in_range:bool}) ** undef_data_at(_to + _i * size_of(Tchar), Tchar) ** undef_slice_at (_to, Tchar, _i + &1, &4096 - (_i + &1))
            thm th9 = DISCH(tm1, th8);
            // _i < &4096
            // ==> fact(${i_in_range:bool}) ** undef_slice_at(_to, Tchar, _i, &4096 - _i)
            // |-- fact(${i_in_range:bool}) ** undef_data_at(_to + _i * size_of(Tchar), Tchar) ** undef_slice_at (_to, Tchar, _i + &1, &4096 - (_i + &1))
            tmp_thm = MATCH_MP(hfact_elim, th9);

            // tmp_thm = axiom(tmp_goal);

            // __transform = which_implies(__state, tmp_thm);
            __transform = axiom(`
                ${__state:hprop}
                |--
                exists (_i:Z) (_to:addr).
                ${locals:hprop} **
                ${after_split:hprop}
            `);
        )]]; // Picks out the first element of the unintialized part and knows the i+1 part is still in the range.

        *((char *)to + i) = (char) 0;

        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            fact(${i_plus_in_range:bool}) **
            ${locals:hprop} **
            data_at(_to + _i * size_of(Tchar), Tchar, &0) ** // (to + i) is assigned 0
            array_at(_to, Tchar, ireplicate(_i, &0)) **
            undef_slice_at(_to, Tchar, _i + 1, &4096 - (_i + 1))
        `)]];

        i = i + 1; // Need to check how VST-IDE handles existentially quantified _i.

        [[cstar::assert(`
            exists (_i:Z) (_to:addr). // _i is still the old value of i
            fact(${i_plus_in_range:bool}) **
            data_at(&"i", Tint, _i + (&1)) ** // i is incremented
            data_at(&"to", Tptr, _to) **
            data_at(_to + _i * size_of(Tchar), Tchar, &0) **
            array_at(_to, Tchar, ireplicate(_i, &0)) **
            undef_slice_at(_to, Tchar, _i + 1, &4096 - (_i + 1))
        `)]];

        [[cstar::proof(
            // establish the invariant
            thm merge = axiom(`
                _i >= &0
                ==>
                (data_at(_to + _i * size_of(Tchar), Tchar, &0) **
                array_at(_to, Tchar, ireplicate(_i, &0))
                |--
                array_at(_to, Tchar, ireplicate(_i + 1, &0)))
            `);
            // merge and reinstantiate existential variables to (_i + (&1))
            __transform = axiom(`42 = 21 + 21`); // Omit the proof details here.
        )]];

        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            fact(${i_in_range:bool}) **
            ${locals:hprop} **
            ${splitted_array_at_i:hprop}
        `)]];
    }
}
