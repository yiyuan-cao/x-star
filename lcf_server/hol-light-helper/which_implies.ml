(* Deprecated `which_implies` library in HOL-light. *)

(* Suppose `septerm` is left associative. *)
let rec SEP_NORMALIZE' septerm = 
  let hsep_hfact_comm = 
    prove(`!hp p. hp ** fact p -|- fact p ** hp`,
          REWRITE_TAC[hsep_comm]) in 
  TRY_CONV 
  ( if is_binop `hsep` septerm
    then begin
      if ((is_comb o rand) septerm   
        && (rator o rand) septerm = `hfact`
        && ( (not ((is_comb o rand o rator) septerm))
          || (not ((rator o rand o rator) septerm = `hfact`))))
        then ONCE_REWRITE_CONV[hsep_hfact_comm] THENC RAND_CONV SEP_NORMALIZE'
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
  REWRITE_CONV [
    hand_assoc; 
    GSYM hfact_hpure; 
    hfact_hpure_r; 
    GSYM hsep_assoc;
    hsep_hemp_left;
    hsep_hemp_right
  ] 
    THENC 
  SEP_NORMALIZE'
    THENC 
  REWRITE_CONV [hsep_assoc]
;;

(* Normalize an entailment with both sides without quantifiers and `hand` of two heaps. *)
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

(* Suppose terms `lft` and lifted term are both right associative,
   and `lft` is always a proper subset of lifted term. *)
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

(* Suppose terms `lft` and lifted term are both right associative,
   and `lft` is always the same set as lifted term. *)
let rec SEP_CANCEL lft = 
  if is_binop `hsep` lft 
    then begin
      match dest_binop `hsep` lft with 
      | (l, r) -> 
        SEP_LIFT' l THENC 
        (RAND_CONV o SEP_CANCEL) r
    end 
    else SEP_LIFT' lft 
;;

(* state: `exists xs. H1 * R` *)
(*  th  : `P, ... |- (H1 |-- H2)`  *)
let WHICH_IMPLIES state th =
  let exl = ref [] in
  let GEN_EXL th = 
    let th = GEN (hd !exl) th in
      exl := tl !exl; th
  and exists_snd (x, tm) = (exl := x :: !exl; tm) in (* exists elim/mono. *)
  let DISCH_ONE th = DISCH (hd (hyp th)) th in 
  let th = th |> UNDISCH_ALL |> repeat (MATCH_MP hfact_elim o DISCH_ONE)
      |> SEP_NORMALIZE_RULE in (* discharge hyps in trans. *)
  let th_pre, th_post = th |> concl |> dest_binop `hentail` in 
  let state = repeat (exists_snd o dest_binder "hexists") state in 
  let state' = state |> SEP_NORMALIZE THENC SEP_LIFT th_pre |> concl |> rand in
  let entail = SEP_NORMALIZE_RULE (SPEC (rand state') (MATCH_MP hsep_cancel_right th)) in 
  let norm_pre = entail |> concl |> dest_binop `hentail` |> fst 
      |> SEP_CANCEL state in (* rewrite precondition of result as exactly `state`. *)
  let entail = ONCE_REWRITE_RULE[norm_pre] entail in
    repeat (MATCH_MP hexists_monotone o GEN_EXL) entail
;;
