use hol_rpc::args;
use hol_rpc::{IndTypeKey, IndDefKey, Interface, Result, TermKey, TheoremKey, TypeKey};
use tarpc::context::Context;

use crate::session::Session;

impl Interface for Session {
    /// Dispose a term.
    async fn dispose_term(mut self, _ctx: Context, key: TermKey) -> Result<()> {
        self.terms_mut().remove(key);
        Ok(())
    }

    /// Dispose a theorem.
    async fn dispose_theorem(mut self, _ctx: Context, key: TheoremKey) -> Result<()> {
        self.theorems_mut().remove(key);
        Ok(())
    }

    /// Dispose a type.
    async fn dispose_type(mut self, _ctx: Context, key: TypeKey) -> Result<()> {
        self.types_mut().remove(key);
        Ok(())
    }

    /// Parse a term from a string.
    async fn parse_term_from_string(mut self, _ctx: Context, s: String) -> Result<TermKey> {
        load_dyn_function!(parse_term_from_string);
        let term = unsafe { self.dyn_call(parse_term_from_string, args!(&s)) }?;
        Ok(self.terms_mut().insert(term))
    }

    /// Parse a type from a string.
    async fn parse_type_from_string(mut self, _ctx: Context, s: String) -> Result<TypeKey> {
        load_dyn_function!(parse_type_from_string);
        let ty = unsafe { self.dyn_call(parse_type_from_string, args!(&s)) }?;
        Ok(self.types_mut().insert(ty))
    }

    /// Convert a term to a string.
    async fn string_of_term(self, _ctx: Context, key: TermKey) -> Result<String> {
        load_dyn_function!(string_of_term);
        let terms = self.terms();
        let term = terms.get(key).ok_or("invalid term key")?;
        let string = unsafe { self.dyn_call(string_of_term, args!(term)) }?;
        Ok(unsafe { string.get_str()? })
    }

    /// Convert a theorem to a string.
    async fn string_of_thm(self, _ctx: Context, key: TheoremKey) -> Result<String> {
        load_dyn_function!(string_of_thm);
        let theorems = self.theorems();
        let theorem = theorems.get(key).ok_or("invalid theorem key")?;
        let string = unsafe { self.dyn_call(string_of_thm, args!(theorem)) }?;
        Ok(unsafe { string.get_str()? })
    }

    /// Dump a Coq axiom.
    async fn dump_coq_axiom(self, _ctx: Context, name: String, key: TheoremKey) -> Result<String> {
        load_dyn_function!(dump_coq_thm as dump_coq_axiom);
        let theorems = self.theorems();
        let theorem = theorems.get(key).ok_or("invalid theorem key")?;
        let string = unsafe { self.dyn_call(dump_coq_axiom, args!(&name, theorem)) }?;
        Ok(unsafe { string.get_str()? })
    }

    /// Theorem: A |- A
    async fn assume(mut self, _ctx: Context, term: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(ASSUME as assume);
        let thm = {
            let terms = self.terms();
            let term = terms.get(term).ok_or("invalid term key")?;
            unsafe { self.dyn_call(assume, args!(term)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Transitivity of the theorem.
    ///
    /// ```text
    /// A1 |- a = b  A2 |- b = c
    /// -------------------------
    /// A1, A2 |- a = c
    /// ```
    async fn trans(
        mut self,
        _ctx: Context,
        th1: TheoremKey,
        th2: TheoremKey,
    ) -> Result<TheoremKey> {
        load_dyn_function!(TRANS as trans);
        let thm = {
            let theorems = self.theorems();
            let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
            let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(trans, args!(th1, th2)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Reflexivity.
    ///
    /// ```text
    /// ----------
    /// A |- a = a
    /// ```
    async fn refl(mut self, _ctx: Context, tm: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(REFL as refl);
        let thm = {
            let terms = self.terms();
            let tm = terms.get(tm).ok_or("invalid term key")?;
            unsafe { self.dyn_call(refl, args!(tm)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Discharge an assumption.
    ///
    /// ```text
    /// A, u |- t
    /// ---------
    /// A |- u ==> t
    /// ```
    async fn disch(mut self, _ctx: Context, th: TheoremKey, tm: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(DISCH as disch);
        let thm = {
            let theorems = self.theorems();
            let terms = self.terms();
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            let tm = terms.get(tm).ok_or("invalid term key")?;
            unsafe { self.dyn_call(disch, args!(tm, th)) }? // Order different in HOL-Light
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Generalize a free term in a theorem.
    ///
    /// ```text
    /// A |- t
    /// -------     (x not free in A)
    /// A |- !x. t
    /// ```
    async fn gen(mut self, _ctx: Context, tm: TermKey, th: TheoremKey) -> Result<TheoremKey> {
        load_dyn_function!(GEN as gen);
        let thm = {
            let theorems = self.theorems();
            let terms = self.terms();
            let tm = terms.get(tm).ok_or("invalid term key")?;
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(gen, args!(tm, th)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Specializes the conclusion of a theorem with its own quantified variables. 
    ///
    /// ```text
    /// A |- !x1...xn. t
    /// -------------------------
    /// A |- t[x1'/x1]...[xn'/xn]
    /// ```
    async fn spec_all(mut self, _ctx: Context, th: TheoremKey) -> Result<TheoremKey> {
        load_dyn_function!(SPEC_ALL as spec_all);
        let thm = {
            let theorems = self.theorems();
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(spec_all, args!(th)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Specializes the conclusion of a theorem. 
    /// 
    /// ```text
    /// A |- !x. t
    /// ----------- SPEC `u`
    /// A |- t[u/x]
    /// ```
    async fn spec(mut self, _ctx: Context, tm: TermKey, th: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(ISPEC as spec);
      let thm = {
        let terms = self.terms();
        let theorems = self.theorems();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(spec, args!(tm, th)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Modus ponens.
    ///
    /// ```text
    /// A1 |- t1 ==> t2   A2 |- t1
    /// --------------------------
    /// A1, A2 |- t2
    /// ```
    async fn mp(mut self, _ctx: Context, th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey> {
        load_dyn_function!(MATCH_MP as mp);
        let thm = {
            let theorems = self.theorems();
            let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
            let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(mp, args!(th1, th2)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Equality version of the Modus Ponens rule.
    /// 
    /// ```text
    /// A1 |- t1 <=> t2   A2 |- t1'
    /// ---------------------------
    ///       A1 u A2 |- t2
    /// ```
    async fn eq_mp(mut self, _ctx: Context, th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(EQ_MP as eq_mp);
      let thm = {
        let theorems = self.theorems();
        let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
        let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(eq_mp, args!(th1, th2)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Conjunction.
    ///
    /// ```text
    /// A1 |- t1  A2 |- t2
    /// ------------------
    /// A1, A2 |- t1 /\ t2
    /// ```
    async fn conjunct(
        mut self,
        _ctx: Context,
        th1: TheoremKey,
        th2: TheoremKey,
    ) -> Result<TheoremKey> {
        load_dyn_function!(CONJ as conjunct);
        let thm = {
            let theorems = self.theorems();
            let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
            let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(conjunct, args!(th1, th2)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Extracts left conjunct of theorem. 
    /// 
    /// ```text
    /// A |- t1 /\ t2 
    /// -------------
    ///    A |- t1
    /// ```
    async fn conjunct1(mut self, _ctx: Context, th: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(CONJUNCT1 as conjunct1);
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(conjunct1, args!(th)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Extracts right conjunct of theorem.
    /// 
    /// ```text
    /// A |- t1 /\ t2 
    /// -------------
    ///    A |- t2
    /// ```
    async fn conjunct2(mut self, _ctx: Context, th: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(CONJUNCT2 as conjunct2);
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(conjunct2, args!(th)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Symmetry.
    ///
    /// ```text
    /// A |- t1 = t2
    /// ------------
    /// A |- t2 = t1
    /// ```
    async fn symm(mut self, _ctx: Context, th: TheoremKey) -> Result<TheoremKey> {
        load_dyn_function!(SYM as symm);
        let thm = {
            let theorems = self.theorems();
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(symm, args!(th)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Eliminates disjunction by cases.
    /// 
    /// ```text
    /// A |- t1 \/ t2   A1 |- t   A2 |- t
    /// ----------------------------------
    /// A u (A1 - {t1}) u (A2 - {t2}) |- t
    /// ```
    async fn disj_cases(mut self, _ctx: Context, th1: TheoremKey, th2: TheoremKey, th3: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(DISJ_CASES as disj_cases);
      let thm = {
        let theorems = self.theorems();
        let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
        let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
        let th3 = theorems.get(th3).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(disj_cases, args!(th1, th2, th3)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Deduces logical equivalence from deduction in both directions. 
    /// 
    /// ```text
    ///      A |- p        B |- q 
    /// --------------------------------
    /// (A - {q}) u (B - {p}) |- p <=> q 
    /// ```
    async fn deduct_antisym(mut self, _ctx: Context, th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(DEDUCT_ANTISYM_RULE as deduct_antisym_rule);
      let thm = {
        let theorems = self.theorems();
        let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
        let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(deduct_antisym_rule, args!(th1, th2)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Existentially quantifies a hypothesis of a theorem. 
    /// 
    /// ```text
    /// A |- t   `x` is not free in `A |- t`
    /// ------------------------------------ CHOOSE `x` th
    ///            A |- ?x. t
    /// ```
    async fn choose(mut self, _ctx: Context, tm: TermKey, th: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(SIMPLE_CHOOSE as choose);
      let thm = {
        let terms = self.terms();
        let theorems = self.theorems();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(choose, args!(tm, th))}?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Define an inductive type.
    async fn define_type(
        mut self,
        _ctx: Context,
        name: String,
        variants: Vec<String>,
    ) -> Result<IndTypeKey> {
        load_dyn_function!(define_type);
        load_dyn_function!(distinctness);
        load_dyn_function!(cases);
        load_dyn_function!(injectivity);

        let variants = variants.join("|");
        let variants = format!("{} = {}", name, variants);

        let token = unsafe { self.dyn_call(define_type, args!(&variants)) }?;
        let (ind, rec) = unsafe { self.destruct::<2, _>(&token)? };
        let (ind, rec) = {
            let mut theorems = self.theorems_mut();
            (theorems.insert(ind), theorems.insert(rec))
        };
        let token = unsafe { self.dyn_call(distinctness, args!(&name))}?;
        let distinct = self.theorems_mut().insert(token);
        let token = unsafe { self.dyn_call(cases, args!(&name))}?;
        let cases = self.theorems_mut().insert(token);
        let token = unsafe { self.dyn_call(injectivity, args!(&name))}?;
        let inject = self.theorems_mut().insert(token);
        Ok(IndTypeKey { ind, rec, distinct, cases, inject })
    }

    /// Define a new constant or function.
    async fn define(mut self, _ctx: Context, tm: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(define);
        let thm = {
            let terms = self.terms();
            let term = terms.get(tm).ok_or("invalid term key")?;
            unsafe { self.dyn_call(define, args!(term)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Uses an instance of a given equation to rewrite a term.
    async fn rewrite(mut self, _ctx: Context, th: TheoremKey, tm: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(SREWRITE_CONV as rewrite); // see helpers.ml
        let thm = {
            let theorems = self.theorems();
            let terms = self.terms();
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            let tm = terms.get(tm).ok_or("invalid term key")?;
            unsafe { self.dyn_call(rewrite, args!(th, tm)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Instantiation of induction principle.
    async fn induction_aux(
        mut self,
        _ctx: Context,
        th: TheoremKey,
        tm1: TermKey,
        tm2: TermKey,
    ) -> Result<TheoremKey> {
        load_dyn_function!(INDUCT_INSTANTIATE as induction_aux); // see helpers.ml
        let thm = {
            let theorems = self.theorems();
            let terms = self.terms();
            let th = theorems.get(th).ok_or("invalid theorem key")?;
            let tm1 = terms.get(tm1).ok_or("invalid term key")?;
            let tm2 = terms.get(tm2).ok_or("invalid term key")?;
            unsafe { self.dyn_call(induction_aux, args!(th, tm1, tm2)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Substitute terms for other terms inside a term.
    async fn subst(
      mut self,
      _ctx: Context,
      tm1: TermKey,
      tm2: TermKey,
      tm: TermKey,
    ) -> Result<TermKey> {
      load_dyn_function!(ssubst as subst); // see helpers.ml
      let tm = {
        let terms = self.terms();
        let tm1 = terms.get(tm1).ok_or("invalid term key")?;
        let tm2 = terms.get(tm2).ok_or("invalid term key")?;
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(subst, args!(tm1, tm2, tm)) }?
      };
      Ok(self.terms_mut().insert(tm))
    }

    /// Check if a term is a variable.
    async fn is_var(self, _ctx: Context, th: TermKey) -> Result<bool> {
        load_dyn_function!(is_var);
        let is_var = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(is_var, args!(th)) }?
        };
        Ok(unsafe { is_var.get_bool()? })
    }

    /// Check if a term is a constant.
    async fn is_const(self, _ctx: Context, th: TermKey) -> Result<bool> {
        load_dyn_function!(is_const);
        let is_const = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(is_const, args!(th)) }?
        };
        Ok(unsafe { is_const.get_bool()? })
    }

    /// Check if a term is an application.
    async fn is_comb(self, _ctx: Context, th: TermKey) -> Result<bool> {
        load_dyn_function!(is_comb);
        let is_comb = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(is_comb, args!(th)) }?
        };
        Ok(unsafe { is_comb.get_bool()? })
    }

    /// Check if a term is an abstraction.
    async fn is_abs(self, _ctx: Context, th: TermKey) -> Result<bool> {
        load_dyn_function!(is_abs);
        let is_abs = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            unsafe { self.dyn_call(is_abs, args!(th)) }?
        };
        Ok(unsafe { is_abs.get_bool()? })
    }

    /// Destruct a variable.
    async fn dest_var(mut self, _ctx: Context, th: TermKey) -> Result<(String, TypeKey)> {
        load_dyn_function!(dest_var);
        let (name, ty) = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            let token = unsafe { self.dyn_call(dest_var, args!(th))? };
            unsafe { self.destruct::<2, _>(&token)? }
        };
        Ok((unsafe { name.get_str()? }, self.types_mut().insert(ty)))
    }

    /// Destruct a constant.
    async fn dest_const(mut self, _ctx: Context, th: TermKey) -> Result<(String, TypeKey)> {
        load_dyn_function!(dest_const);
        let (name, ty) = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            let token = unsafe { self.dyn_call(dest_const, args!(th))? };
            unsafe { self.destruct::<2, _>(&token)? }
        };
        Ok((unsafe { name.get_str()? }, self.types_mut().insert(ty)))
    }

    /// Destruct an application.
    async fn dest_comb(mut self, _ctx: Context, th: TermKey) -> Result<(TermKey, TermKey)> {
        load_dyn_function!(dest_comb);
        let (th1, th2) = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            let token = unsafe { self.dyn_call(dest_comb, args!(th))? };
            unsafe { self.destruct::<2, _>(&token)? }
        };
        let mut terms = self.terms_mut();
        Ok((terms.insert(th1), terms.insert(th2)))
    }

    /// Destruct an abstraction.
    async fn dest_abs(mut self, _ctx: Context, th: TermKey) -> Result<(TermKey, TermKey)> {
        load_dyn_function!(dest_abs);
        let (tm, th) = {
            let terms = self.terms();
            let th = terms.get(th).ok_or("invalid theorem key")?;
            let token = unsafe { self.dyn_call(dest_abs, args!(th))? };
            unsafe { self.destruct::<2, _>(&token)? }
        };
        let mut terms = self.terms_mut();
        Ok((terms.insert(tm), terms.insert(th)))
    }

    /// Construct a abstraction.
    async fn mk_abs(mut self, _ctx: Context, th1: TermKey, th2: TermKey) -> Result<TermKey> {
      load_dyn_function!(mk_abs_aux);
      let tm = {
        let terms = self.terms();
        let th1 = terms.get(th1).ok_or("invalid term key")?;
        let th2 = terms.get(th2).ok_or("invalid term key")?;
        unsafe { self.dyn_call(mk_abs_aux, args!(th1, th2))? }
      };
      Ok(self.terms_mut().insert(tm))
    }
    
    /// Construct a combination.
    async fn mk_comb(mut self, _ctx: Context, th1: TermKey, th2: TermKey) -> Result<TermKey> {
      load_dyn_function!(mk_comb_aux);
      let tm = {
        let terms = self.terms();
        let th1 = terms.get(th1).ok_or("invalid term key")?;
        let th2 = terms.get(th2).ok_or("invalid term key")?;
        unsafe { self.dyn_call(mk_comb_aux, args!(th1, th2))? }
      };
      Ok(self.terms_mut().insert(tm))
    }

    /// Conclusion of a theorem.
    async fn concl(mut self, _ctx: Context, th: TheoremKey) -> Result<TermKey> {
      load_dyn_function!(concl);
      let tm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(concl, args!(th)) }?
      };
      let mut terms = self.terms_mut();
      Ok(terms.insert(tm))
    }

    /// Create a new type.
    async fn new_type(self, _ctx: Context, name: String, arity: u32) -> Result<()> {
        load_dyn_function!(new_type_helper);
        let arity = arity.to_string();
        let _ = unsafe { self.dyn_call(new_type_helper, args!(&name, &arity)) }?;
        Ok(())
    }

    /// Declare a new constant.
    async fn new_constant(self, _ctx: Context, name: String, ty: TypeKey) -> Result<()> {
        load_dyn_function!(new_constant_helper);
        let types = self.types();
        let ty = types.get(ty).ok_or("invalid type key")?;
        let _ = unsafe { self.dyn_call(new_constant_helper, args!(&name, ty)) }?;
        Ok(())
    }

    /// Set up a new axiom.
    async fn new_axiom(mut self, _ctx: Context, tm: TermKey) -> Result<TheoremKey> {
        load_dyn_function!(new_axiom);
        let thm = {
            let terms = self.terms();
            let tm = terms.get(tm).ok_or("invalid term key")?;
            unsafe { self.dyn_call(new_axiom, args!(tm)) }?
        };
        Ok(self.theorems_mut().insert(thm))
    }

    /// Define a relation or family of relations inductively. 
    async fn new_inductive_definition(mut self, _ctx: Context, tm: TermKey) -> Result<IndDefKey> {
      load_dyn_function!(new_inductive_definition);
      let token = {
        let terms = self.terms();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(new_inductive_definition, args!(tm)) }?
      };
      let (def, ind, cases) = unsafe { self.destruct::<3, _>(&token)? };
      let (def, ind, cases) = {
        let mut theorems = self.theorems_mut();
        (theorems.insert(def), theorems.insert(ind), theorems.insert(cases))
      };
      Ok(IndDefKey { def, ind, cases })
    }
}
