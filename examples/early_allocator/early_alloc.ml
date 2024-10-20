needs "cstarlib.ml";;

let early_alloc_state = ref `hp:hprop`;;
let early_alloc_transform = ref `th:thm`;;

(* 
size_t hyp_early_alloc_nr_pages(void)
*)
(* let hyp_early_alloc_nr_pages = begin *)
(*
    [[cstar::parameter(`_base : Z`)]]
    [[cstar::parameter(`_cur : Z`)]]
*)
    the_implicit_types := ["_base", `:Z`; "_cur", `:Z`];;
(*
    [[cstar::require(`
        pure(_base <= _cur) &&
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    `)]]
*)
    assert (type_of `
        pure(_base <= _cur) &&
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    ` = `:hprop`);;
(*
    [[cstar::ensure(`
        pure(__result == (_cur - _base) / &4096) &&
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    `)]]
*)
    assert (type_of `
        pure(__result == (_cur - _base) / &4096) &&
        data_at(&"base", Tptr, _base) **
        data_at(&"cur", Tptr, _cur)
    ` = `:hprop`);;
(*
{
	return (cur - base) >> PAGE_SHIFT;
}
*)
(* end;; *)

(*
void clear_page(void *to)
*)
(* let clear_page = begin *)
(*
    [[cstar::require(`undef_array_at(to, Tchar, &4096)`)]]
    [[cstar::ensure(`array_at(to, Tchar, ireplicate(&4096, &0))`)]]
*)
    assert (type_of `
        undef_array_at(to, Tchar, &4096)
    ` = `:hprop`);;
    assert (type_of `
        array_at(to, Tchar, ireplicate(&4096, &0))
    ` = `:hprop`);;
(*
{
    [[cstar::assert(`
        exists (_to:addr).
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `)]];
*)
    early_alloc_state := `
        exists (_to:addr). // locals
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `;

(*
    int i = 0;
*)
(*
    [[cstar::assert(`
        exists (_i:Z) (_to:addr).
        pure(_i == &0) &&
        data_at(&"i", Tint, _i) **
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `)]]
*)
    early_alloc_state := `
        exists (_i:Z) (_to:addr). // locals
        pure(_i == &0) &&
        data_at(&"i", Tint, _i) **
        data_at(&"to", Tptr, _to) **
        undef_array_at(_to, Tchar, &4096)
    `;

(*
    [[cstar::ghostcmd(
    {
        [[cstar::type(`:hprop`)]]
        term antecedent = `
            pure(_i == &0) &&
            undef_array_at(_to, Tchar, &4096)
        `;
*)
        let antecedent = ref `
            pure(_i == &0) &&
            undef_array_at(_to, Tchar, &4096)
        `
        in
        assert (type_of !antecedent = `:hprop`);
(*
        [[cstar::type(`:hprop`)]]
        term part_inv = `
            pure(&0 <= _i && _i <= &4096) &&
            array_at(_to, Tchar, ireplicate(_i, &0)) **
            undef_slice_at(_to, Tchar, _i, &4096 - _i)
        `;
*)
        let part_inv = ref `
            pure(&0 <= _i && _i <= &4096) &&
            array_at(_to, Tchar, ireplicate(_i, &0)) **
            undef_slice_at(_to, Tchar, _i, &4096 - _i)
        `
        in
        assert (type_of !part_inv = `:hprop`);
(*
        [[cstar::type(`:bool`)]]
        term goal = `
            ${antecedent}
            |-
            ${part_inv}
        `;
*)
        let goal = ref `
            (antecedent:hprop)
            |-
            (part_inv:hprop)
        `
        in
        goal := vsubst [!antecedent, `(antecedent:hprop)`; !part_inv, `(part_inv:hprop)`] !goal;
        assert (type_of !goal = `:bool`);
        
(*
        // ... constructing actual proof steps here ...
        thm th = axiom(goal);
        assert(proves(th, goal));
        // bool proves(thm th, term goal) = {
        //     assert(no_hyps(th));
        //     aconv(concl(th), goal);
        // }
*)
        let th = ref (prove (!goal,
            PRINT_GOAL_TAC THEN
            CHEAT_TAC
        ))
        in
        
(*
        __transform = which_implies(__state, th);
        // thm which_implies(term state, thm th) = { /* Does a partial transformation on the symbolic state */ }
        // for now, we can also delegate directly to VST-IDE support for `which-implies`.
*)

        early_alloc_transform := `
            {$early_alloc_state}
            |-
            exists (_i:Z) (_to:addr).
            {$part_inv} **
            data_at(&"i", Tint, _i) **
            data_at(&"to", Tptr, _to)
        `;
        (* which_implies(!early_alloc_state, !th); *)
        

(*
    }
    )]];
*)
    [[cstar::ghostcmd(
    {
        [[cstar::type(`:hprop`)]]
        term locals = `
            data_at(&"i", Tint, _i) **
            data_at(&"to", Tptr, _to)
        `;
        __transform = hentail_refl(__state);
    }
    )]]; // this is a expanded version of the [[cstar::ghostvar]] attribute.
    
    [[cstar::invariant(`
        exists (_i:Z) (_to:addr).
        {$part_inv} ** {$locals}
    `)]]
    while (i < &4096)
    {
        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            pure(_i < &4096) &&
            {$part_inv} ** {$locals}
        `)]];
        
        [[cstar::ghostcmd(
        {
            [[cstar::type(`:hprop`)]]
            term before_split = `
                pure(_i < &4096) &&
                pure(&0 <= _i && _i <= &4096) &&
                undef_slice_at(_to, Tchar, _i, &4096 - _i)
            `;
            term after_split = `
                pure(&0 <= _i && _i + 1 <= &4096) &&
                undef_cell_at(_to, Tchar, _i) **
                undef_slice_at(_to, Tchar, _i + 1, &4096 - (_i + 1))
            `;
            term goal = `
                {$before_split}
                |-
                {$after_split}
            `;
            // proofs here ...
            thm th = axiom(goal);
            assert(proves(th, goal));
            __transform = which_implies(__state, th);
        }
        )]];

        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            {$locals} **
            {$after_split} **
            array_at(_to, Tchar, ireplicate(_i, &0))
        `)]];

        *((char *)to + i) = (char) 0;
        
        [[cstar::assert(`
            exists (_i:Z) (_to:addr).
            pure(&0 <= _i && _i + 1 <= &4096) &&
            data_at(_to + _i * size_of(Tchar), Tchar, 0) **
            array_at(_to, Tchar, ireplicate(_i, &0)) **
            undef_slice_at(_to, Tchar, _i + 1, &4096 - (_i + 1)) **
            {$locals}
        `)]];

        i++;

        [[cstar::ghostcmd(
            // establish the invariant
        )]];
    }
}
NOT FINISHED!!!