use hol_rpc::args;
use hol_rpc::{IndTypeKey, IndDefKey, Interface, Result, TermKey, TheoremKey, TypeKey, ConversionKey};
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

    /// Dispose a conversion.
    async fn dispose_conversion(mut self, _ctx: Context, key: ConversionKey) -> Result<()> {
      self.conversions_mut().remove(key);
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

    /// Parse a conversion from a string.
    async fn parse_conv_from_string(mut self, _ctx: Context, s: String) -> Result<ConversionKey> {
      load_dyn_function!(parse_conv_from_string);
      let conv = unsafe { self.dyn_call(parse_conv_from_string, args!(&s)) }?;
      Ok(self.conversions_mut().insert(conv))
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

    /// Equality test on terms. 
    async fn equals_term(self, _ctx: Context, t1: TermKey, t2: TermKey) -> Result<bool> {
      load_dyn_function!(equals_term);
      let result = {
        let terms = self.terms();
        let t1 = terms.get(t1).ok_or("invalid term key")?;
        let t2 = terms.get(t2).ok_or("invalid term key")?;
        unsafe { self.dyn_call(equals_term, args!(t1, t2)) }?
      };
      Ok(unsafe { result.get_bool()? })
    }

    /// Equality test on theorems. 
    async fn equals_thm(self, _ctx: Context, th1: TheoremKey, th2: TheoremKey) -> Result<bool> {
      load_dyn_function!(equals_thm);
      let result = {
        let theorems = self.theorems();
        let th1 = theorems.get(th1).ok_or("invalid theorem key")?;
        let th2 = theorems.get(th2).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(equals_thm, args!(th1, th2)) }?
      };
      Ok(unsafe { result.get_bool()? })
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

    /// Undischarges the antecedent of an implicative theorem.
    /// 
    /// ```text
    /// A |- t1 ==> t2
    /// --------------
    ///   A, t1 |- t2
    /// ```
    async fn undisch(mut self, _ctx: Context, th: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(UNDISCH as undisch);
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(undisch, args!(th)) }?
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
        load_dyn_function!(GSYM as symm);
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
        tm: String,
    ) -> Result<IndTypeKey> {
        load_dyn_function!(define_type);

        let token = unsafe { self.dyn_call(define_type, args!(&tm)) }?;
        let (ind, rec) = unsafe { self.destruct::<2, _>(&token)? };
        let (ind, rec) = {
            let mut theorems = self.theorems_mut();
            (theorems.insert(ind), theorems.insert(rec))
        };
        Ok(IndTypeKey { ind, rec })
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
    async fn pure_rewrite(mut self, _ctx: Context, th: TheoremKey, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(SPURE_REWRITE_CONV as pure_rewrite); // see helpers.ml
      let thm = {
          let theorems = self.theorems();
          let terms = self.terms();
          let th = theorems.get(th).ok_or("invalid theorem key")?;
          let tm = terms.get(tm).ok_or("invalid term key")?;
          unsafe { self.dyn_call(pure_rewrite, args!(th, tm)) }?
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

    /// Uses an instance of a given equation to rewrite a theorem.
    async fn pure_rewrite_rule(mut self, _ctx: Context, th: TheoremKey, t: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(SPURE_REWRITE_RULE as pure_rewrite_rule); // see helpers.ml
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        let t = theorems.get(t).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(pure_rewrite_rule, args!(th, t)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }


    /// Uses an instance of a given equation to rewrite a theorem.
    async fn rewrite_rule(mut self, _ctx: Context, th: TheoremKey, t: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(SREWRITE_RULE as rewrite_rule); // see helpers.ml
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        let t = theorems.get(t).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(rewrite_rule, args!(th, t)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Uses an instance of a given equation to rewrite a term only once.
    async fn once_rewrite(mut self, _ctx: Context, th: TheoremKey, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(SONCE_REWRITE_CONV as once_rewrite); // see helpers.ml
      let thm = {
        let theorems = self.theorems();
        let terms = self.terms();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(once_rewrite, args!(th, tm)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Uses an instance of a give equation to rewrite a theorem only once.
    async fn once_rewrite_rule(mut self, _ctx: Context, th: TheoremKey, t: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(SONCE_REWRITE_RULE as once_rewrite_rule); // see helpers.ml
      let thm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        let t = theorems.get(t).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(once_rewrite_rule, args!(th, t)) }?
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

    /// Check if a term is an application of the given binary operator. 
    async fn is_binop(self, _ctx: Context, op: TermKey, tm: TermKey) -> Result<bool> {
      load_dyn_function!(is_binop);
      let is_binop = {
        let terms = self.terms();
        let op = terms.get(op).ok_or("invalid term key")?;
        let tm = terms.get(tm).ok_or("invalie term key")?;
        unsafe { self.dyn_call(is_binop, args!(op, tm)) }?
      };
      Ok(unsafe { is_binop.get_bool()? })
    }

    /// Check if a term is a binder construct with named constant.
    async fn is_binder(self, _ctx: Context, s: String, tm: TermKey) -> Result<bool> {
      load_dyn_function!(is_binder);
      let is_binder = {
        let terms = self.terms();
        let tm = terms.get(tm).ok_or("invalie term key")?;
        unsafe { self.dyn_call(is_binder, args!(&s, tm)) }?
      };
      Ok(unsafe { is_binder.get_bool()? })
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

    /// Destruct an application of the given binary operator.
    async fn dest_binop(mut self, _ctx: Context, op: TermKey, tm: TermKey) -> Result<(TermKey, TermKey)> {
      load_dyn_function!(dest_binop);
      let (tm1, tm2) = {
        let terms = self.terms();
        let op = terms.get(op).ok_or("invalid term key")?;
        let tm = terms.get(tm).ok_or("invalid term key")?;
        let token = unsafe { self.dyn_call(dest_binop, args!(op, tm))? };
        unsafe { self.destruct::<2, _>(&token)? }
      };
      let mut terms = self.terms_mut();
      Ok((terms.insert(tm1), terms.insert(tm2)))
    }

    /// Destruct a binder construct.
    async fn dest_binder(mut self, _ctx: Context, s: String, tm: TermKey) -> Result<(TermKey, TermKey)> {
      load_dyn_function!(dest_binder);
      let (tm1, tm2) = {
        let terms = self.terms();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        let token = unsafe { self.dyn_call(dest_binder, args!(&s, tm))? };
        unsafe { self.destruct::<2, _>(&token)? }
      };
      let mut terms = self.terms_mut();
      Ok((terms.insert(tm1), terms.insert(tm2)))
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

    /// Return one hypothesis of a theorem. 
    async fn hypth(mut self, _ctx: Context, th: TheoremKey) -> Result<TermKey> {
      load_dyn_function!(hypth); // see helpers.ml
      let tm = {
        let theorems = self.theorems();
        let th = theorems.get(th).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(hypth, args!(th)) }? 
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

    /// Automatically proves natural number arithmetic theorems. 
    async fn arith_rule(mut self, _ctx: Context, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(ARITH_RULE_SAFE as arith_rule);
      let thm = {
        let terms = self.terms();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(arith_rule, args!(tm)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Proves integer theorems needing basic rearrangement and linear inequality reasoning only. 
    async fn int_arith(mut self, _ctx: Context, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(INT_ARITH_SAFE as int_arith);
      let thm = {
        let terms = self.terms();
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(int_arith, args!(tm)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// Get a theorem from the search database.
    async fn get_theorem(mut self, _ctx: Context, name: String) -> Result<TheoremKey> {
      load_dyn_function!(get_theorem);
      let thm = unsafe { self.dyn_call(get_theorem, args!(&name)) }?;
      let mut theorems = self.theorems_mut();
      Ok(theorems.insert(thm))
    }

    /// `sep lift` conversion.
    async fn sep_lift(mut self, _ctx: Context, lft: TermKey, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(SEP_LIFT as sep_lift);
      let thm = {
        let terms = self.terms();
        let lft = terms.get(lft).ok_or("invalid term key")?;
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(sep_lift, args!(lft, tm)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    /// `which implies` conversion.
    async fn which_implies(mut self, _ctx: Context, state: TermKey, trans: TheoremKey) -> Result<TheoremKey> {
      load_dyn_function!(WHICH_IMPLIES as which_implies);
      let thm = {
        let terms = self.terms();
        let theorems = self.theorems();
        let state = terms.get(state).ok_or("invalid term key")?;
        let trans = theorems.get(trans).ok_or("invalid theorem key")?;
        unsafe { self.dyn_call(which_implies, args!(state, trans)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }

    // Applies a conversion to the operand of an application. 
    async fn rand_conv(mut self, _ctx: Context, conv: ConversionKey) -> Result<ConversionKey> {
      load_dyn_function!(RAND_CONV as rand_conv);
      let result = {
        let conversions = self.conversions();
        let conv = conversions.get(conv).ok_or("invalid conversion key")?;
        unsafe { self.dyn_call(rand_conv, args!(conv)) }?
      };
      Ok(self.conversions_mut().insert(result))
    }

    /// Applies a conversion.
    async fn apply_conv(mut self, _ctx: Context, conv: ConversionKey, tm: TermKey) -> Result<TheoremKey> {
      load_dyn_function!(apply_conv);
      let thm = {
        let conversions = self.conversions();
        let terms = self.terms();
        let conv = conversions.get(conv).ok_or("invalid conversion key")?;
        let tm = terms.get(tm).ok_or("invalid term key")?;
        unsafe { self.dyn_call(apply_conv, args!(conv, tm)) }?
      };
      Ok(self.theorems_mut().insert(thm))
    }
}
