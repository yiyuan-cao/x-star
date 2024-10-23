needs "cstarlib.ml";;

let rec SEP_NORMALIZE' septerm = 
  let hsep_hfact_comm = 
    prove(`!hp p. hp ** fact p -|- fact p ** hp`,
          REWRITE_TAC[hsep_comm]) in 
  TRY_CONV 
  ( if is_binop `hsep` septerm
    then begin
      if ((is_comb o rand) septerm && (is_comb o rand o rator) septerm 
        && (rator o rand) septerm = `hfact`
        && not ((rator o rand o rator) septerm = `hfact`))
        then PURE_ONCE_REWRITE_CONV[hsep_hfact_comm] THENC RAND_CONV SEP_NORMALIZE'
        else LAND_CONV SEP_NORMALIZE'
    end 
    else LAND_CONV SEP_NORMALIZE' 
  ) septerm 
;;

(* Normalize a septerm without quantifiers and `hand` of two heaps. *)
let SEP_NORMALIZE = 
  let hfact_hpure_r = 
    prove(`!p hp. hp && hpure p -|- hfact p ** hp`,
          REWRITE_TAC[hfact_hpure; hand_comm]) in 
  PURE_REWRITE_CONV [
    hand_assoc; 
    GSYM hfact_hpure; hfact_hpure_r; 
    GSYM hsep_assoc
  ] 
    THENC 
  SEP_NORMALIZE'
    THENC 
  PURE_REWRITE_CONV [hsep_assoc]
;;

let SEP_NORMALIZE_EXAMPLE =
  SEP_NORMALIZE 
    `((((pure p1 && pure p2) && hp1 && pure p3) 
    ** hp2) 
    ** (pure p4 && pure p5 && ((hp3 ** (hp4 && pure p3)) ** ((hp5 ** hp6) ** (pure p4 && pure p5 && hp7)) ** hp8))) 
    ** (pure p6 && hp4)`;;

let SEP_NORMALIZE_RULE th = 
  let th_pre, th_post = th |> concl |> dest_binop `hentail` in 
  REWRITE_RULE[SEP_NORMALIZE th_pre; SEP_NORMALIZE th_post] th 
;;

let rec SEP_LIFT' lft septerm = (* lift a single term; suppose it always exists. *)
  let hsep_h_right = SPEC lft 
    ( prove(`!hp hp1 hp2. hp1 ** hp ** hp2 -|- hp ** hp1 ** hp2`,
            ONCE_REWRITE_TAC [GSYM hsep_assoc] THEN 
            REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN 
            ACCEPT_TAC (SPECL [`hp1`;`hp`] hsep_comm) ) ) in 
  let hsep_h_swap = SPEC lft 
    ( prove(`!hp hp1. hp1 ** hp -|- hp ** hp1`,
            REWRITE_TAC[hsep_comm]) ) in
  septerm |> 
    if is_binop `hsep` septerm 
      then begin 
        match dest_binop `hsep` septerm with 
        | (l, r) -> 
          if l = lft 
            then ONCE_REWRITE_CONV[hsep_h_right] 
            else begin
              if is_binop `hsep` r 
                then RAND_CONV (SEP_LIFT' lft) THENC ONCE_REWRITE_CONV[hsep_h_right]
                else ONCE_REWRITE_CONV[hsep_h_swap]
            end
      end 
      else REFL
;;

let rec SEP_LIFT lft = (* lift a whole term; suppose they always exist. *)
  if is_binop `hsep` lft 
    then begin
      match dest_binop `hsep` lft with 
      | (l, r) -> 
        SEP_LIFT r THENC 
        SEP_LIFT' l THENC 
        ONCE_REWRITE_CONV[GSYM hsep_assoc] 
    end 
    else SEP_LIFT' lft
;;

let SEP_LIFT_EXAMPLE = 
  SEP_LIFT
  `fact ((a:int) == (b:int)) 
    ** undef_data_at ((z:int),Tint)
    ** data_at ((x:int),Tint,&0)`
  `fact (a == b) ** (data_at(x, Tint, &0) ** data_at(y, Tptr, &1)) 
                 ** fact (x + y == a) ** undef_data_at(z, Tint)`;;

(* state: `exists xs. H1 * R` *)
(*  th  : `P |- (H1 |-- H2)`  *)
(* suppose P is empty.        *)
let WHICH_IMPLIES state th =
  let exl = ref [] in
  let GEN_EXL th = 
    let th = GEN (hd !exl) th in
      exl := tl !exl; th
  and exists_snd (x, tm) = (exl := x :: !exl; tm) in (* exists elim/mono. *)
  let th = SEP_NORMALIZE_RULE th in 
  let th_pre, th_post = th |> concl |> dest_binop `hentail` in 
  let state' = state |> repeat (exists_snd o dest_binder "hexists") 
      |> SEP_NORMALIZE THENC SEP_LIFT th_pre |> concl |> rand in
  let entail = SPEC (rand state') (MATCH_MP hsep_cancel_right th) in 
    repeat (MATCH_MP hexists_monotone o GEN_EXL) (SEP_NORMALIZE_RULE entail)
;;

(* one manual example. *)
let state = 
  `exists a b x y z. fact (a == b) ** (data_at(x, Tint, &0) ** data_at(y, Tptr, &1))
                  ** fact (x + y == a) ** undef_data_at(z, Tint)`
;;
let trans = new_axiom 
  `fact ((a:int) == b) ** undef_data_at(z, Tint) ** data_at(x, Tint, &0) 
    |-- data_at(z, Tint, &0) ** fact (z + y == a)`
;;
let WHICH_IMPLIES_EXAMPLE = WHICH_IMPLIES state trans;;
