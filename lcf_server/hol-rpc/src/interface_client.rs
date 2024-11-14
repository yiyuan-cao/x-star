use tarpc::context;

use crate::{
    client::{Client, IndType, IndDef, Term, Theorem, Type, Conversion},
    Result,
};

impl Client {
    /// Parse a term from a string.
    pub fn parse_term_from_string(&self, s: String) -> Result<Term> {
        let key = self.execute(
            self.interface()
                .parse_term_from_string(context::current(), s),
        )??;
        Ok(Term::new(key, self.clone()))
    }

    /// Parse a type from a string.
    pub fn parse_type_from_string(&self, s: String) -> Result<Type> {
        let key = self.execute(
            self.interface()
                .parse_type_from_string(context::current(), s),
        )??;
        Ok(Type::new(key, self.clone()))
    }

    /// Parse a conversion from a conversion.
    pub fn parse_conv_from_string(&self, s: String) -> Result<Conversion> {
      let key = self.execute(
          self.interface()
              .parse_conv_from_string(context::current(), s),
      )??;
      Ok(Conversion::new(key, self.clone()))
  }

    /// Convert a term to a string.
    pub fn string_of_term(&self, term: &Term) -> Result<String> {
        self.execute(
            self.interface()
                .string_of_term(context::current(), term.key),
        )?
    }

    /// Convert a theorem to a string.
    pub fn string_of_thm(&self, theorem: &Theorem) -> Result<String> {
        self.execute(
            self.interface()
                .string_of_thm(context::current(), theorem.key),
        )?
    }

    /// Equality test on terms. 
    pub fn equals_term(&self, t1: &Term, t2: &Term) -> Result<bool> {
      self.execute(self.interface().equals_term(context::current(), t1.key, t2.key))?
    }

    /// Equality test on theorems. 
    pub fn equals_thm(&self, th1: &Theorem, th2: &Theorem) -> Result<bool> {
      self.execute(self.interface().equals_thm(context::current(), th1.key, th2.key))?
    }

    /// Dump a Coq axiom.
    pub fn dump_coq_axiom(&self, name: String, th: &Theorem) -> Result<String> {
        self.execute(
            self.interface()
                .dump_coq_axiom(context::current(), name, th.key),
        )?
    }

    /// Theorem: A |- A
    pub fn assume(&self, term: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().assume(context::current(), term.key))??;
        Ok(Theorem::new(key, self.clone()))
    }
    /// Transitivity of the theorem.
    ///
    /// ```text
    /// A1 |- a = b  A2 |- b = c
    /// -------------------------
    /// A1, A2 |- a = c
    /// ```
    pub fn trans(&self, th1: &Theorem, th2: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().trans(context::current(), th1.key, th2.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Reflexivity.
    ///
    /// ```text
    /// ----------
    /// A |- a = a
    /// ```
    pub fn refl(&self, tm: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().refl(context::current(), tm.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Discharge an assumption.
    ///
    /// ```text
    /// A, u |- t
    /// ---------
    /// A |- u ==> t
    /// ```
    pub fn disch(&self, th: &Theorem, tm: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().disch(context::current(), th.key, tm.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Undischarges the antecedent of an implicative theorem.
    /// 
    /// ```text
    /// A |- t1 ==> t2
    /// --------------
    ///   A, t1 |- t2
    /// ```
    pub fn undisch(&self, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().undisch(context::current(), th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Generalize a free term in a theorem.
    ///
    /// ```text
    /// A |- t
    /// -------     (x not free in A)
    /// A |- !x. t
    /// ```
    pub fn gen(&self, tm: &Term, th: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().gen(context::current(), tm.key, th.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Specializes the conclusion of a theorem with its own quantified variables. 
    ///
    /// ```text
    /// A |- !x1...xn. t
    /// -------------------------
    /// A |- t[x1'/x1]...[xn'/xn]
    /// ```
    pub fn spec_all(&self, th: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().spec_all(context::current(), th.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Specializes the conclusion of a theorem. 
    /// 
    /// ```text
    /// A |- !x. t
    /// ----------- SPEC `u`
    /// A |- t[u/x]
    /// ```
    pub fn spec(&self, tm: &Term, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().spec(context::current(), tm.key, th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Modus ponens.
    ///
    /// ```text
    /// A1 |- t1 ==> t2   A2 |- t1
    /// --------------------------
    /// A1, A2 |- t2
    /// ```
    pub fn mp(&self, th1: &Theorem, th2: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().mp(context::current(), th1.key, th2.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Equality version of the Modus Ponens rule.
    /// 
    /// ```text
    /// A1 |- t1 <=> t2   A2 |- t1'
    /// ---------------------------
    ///       A1 u A2 |- t2
    /// ```
    pub fn eq_mp(&self, th1: &Theorem, th2: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().eq_mp(context::current(), th1.key, th2.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Conjunction.
    ///
    /// ```text
    /// A1 |- t1  A2 |- t2
    /// ------------------
    /// A1, A2 |- t1 /\ t2
    /// ```
    pub fn conjunct(&self, th1: &Theorem, th2: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().conjunct(
            context::current(),
            th1.key,
            th2.key,
        ))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Extracts left conjunct of theorem. 
    /// 
    /// ```text
    /// A |- t1 /\ t2 
    /// -------------
    ///    A |- t1
    /// ```
    pub fn conjunct1(&self, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().conjunct1(context::current(), th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Extracts right conjunct of theorem.
    /// 
    /// ```text
    /// A |- t1 /\ t2 
    /// -------------
    ///    A |- t2
    /// ```
    pub fn conjunct2(&self, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().conjunct2(context::current(), th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Symmetry.
    ///
    /// ```text
    /// A |- t1 = t2
    /// ------------
    /// A |- t2 = t1
    /// ```
    pub fn symm(&self, th: &Theorem) -> Result<Theorem> {
        let key = self.execute(self.interface().symm(context::current(), th.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Eliminates disjunction by cases.
    /// 
    /// ```text
    /// A |- t1 \/ t2   A1 |- t   A2 |- t
    /// ----------------------------------
    /// A u (A1 - {t1}) u (A2 - {t2}) |- t
    /// ```
    pub fn disj_cases(&self, th1: &Theorem, th2: &Theorem, th3: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().disj_cases(context::current(), th1.key, th2.key, th3.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Deduces logical equivalence from deduction in both directions. 
    /// 
    /// ```text
    ///      A |- p        B |- q 
    /// --------------------------------
    /// (A - {q}) u (B - {p}) |- p <=> q 
    /// ```
    pub fn deduct_antisym(&self, th1: &Theorem, th2: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().deduct_antisym(context::current(), th1.key, th2.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Existentially quantifies a hypothesis of a theorem. 
    /// 
    /// ```text
    /// A |- t   `x` is not free in `A |- t`
    /// ------------------------------------ CHOOSE `x` th
    ///            A |- ?x. t
    /// ```
    pub fn choose(&self, tm: &Term, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().choose(context::current(), tm.key, th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Define an inductive type.
    pub fn define_type(&self, tm: String) -> Result<IndType> {
        let key = self.execute(self.interface().define_type(
            context::current(),
            tm,
        ))??;
        Ok(IndType {
            ind: Theorem::new(key.ind, self.clone()),
            rec: Theorem::new(key.rec, self.clone()),
        })
    }

    /// Proves equality of alpha-equivalent terms. 
    pub fn alpha(&self, t1: &Term, t2: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().alpha(context::current(), t1.key, t2.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Performs a simple beta-conversion. 
    pub fn beta_conv(&self, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().beta_conv(context::current(), tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Beta-reduces all the beta-redexes in the conclusion of a theorem. 
    pub fn beta_rule(&self, th: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().beta_rule(context::current(), th.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Define a new constant or function.
    pub fn define(&self, term: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().define(context::current(), term.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Produce cases theorem for an inductive type. 
    pub fn cases(&self, s: String) -> Result<Theorem> {
      let key = self.execute(self.interface().cases(context::current(), s))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Produce distinctness theorem for an inductive type. 
    pub fn distinctness(&self, s: String) -> Result<Theorem> {
      let key = self.execute(self.interface().distinctness(context::current(), s))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a given equation to rewrite a term.
    pub fn pure_rewrite(&self, th: &Theorem, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().pure_rewrite(context::current(), th.key, tm.key))??;
      Ok(Theorem::new(key, self.clone()))
  }

    /// Uses an instance of a given equation to rewrite a term.
    pub fn rewrite(&self, th: &Theorem, tm: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().rewrite(context::current(), th.key, tm.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a given equation to rewrite a theorem. 
    pub fn pure_rewrite_rule(&self, th: &Theorem, t: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().pure_rewrite_rule(context::current(), th.key, t.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a given equation to rewrite a theorem. 
    pub fn rewrite_rule(&self, th: &Theorem, t: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().rewrite_rule(context::current(), th.key, t.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a given equation to rewrite a term only once.
    pub fn once_rewrite(&self, th: &Theorem, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().once_rewrite(context::current(), th.key, tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a give equation to rewrite a theorem only once.
    pub fn once_rewrite_rule(&self, th: &Theorem, t: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().once_rewrite_rule(context::current(), th.key, t.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a given equation to rewrite a term only once.
    pub fn pure_once_rewrite(&self, th: &Theorem, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().pure_once_rewrite(context::current(), th.key, tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Uses an instance of a give equation to rewrite a theorem only once.
    pub fn pure_once_rewrite_rule(&self, th: &Theorem, t: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().pure_once_rewrite_rule(context::current(), th.key, t.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Instantiation of induction principle.
    pub fn induction_aux(&self, th: &Theorem, tm1: &Term, tm2: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().induction_aux(
            context::current(),
            th.key,
            tm1.key,
            tm2.key,
        ))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Substitute terms for other terms inside a term.
    pub fn subst(&self, tm1: &Term, tm2: &Term, tm: &Term) -> Result<Term> {
      let tm = self.execute(self.interface().subst(context::current(), tm1.key, tm2.key, tm.key))??;
      Ok(Term::new(tm, self.clone()))
    }

    /// Tests whether a variable (or constant) occurs free in a term. 
    pub fn free_in(&self, v: &Term, tm: &Term) -> Result<bool> {
      self.execute(self.interface().free_in(context::current(), v.key, tm.key))? 
    }

    /// Check if a term is a variable.
    pub fn is_var(&self, tm: &Term) -> Result<bool> {
        self.execute(self.interface().is_var(context::current(), tm.key))?
    }

    /// Check if a term is a constant.
    pub fn is_const(&self, tm: &Term) -> Result<bool> {
        self.execute(self.interface().is_const(context::current(), tm.key))?
    }

    /// Check if a term is an application.
    pub fn is_comb(&self, tm: &Term) -> Result<bool> {
        self.execute(self.interface().is_comb(context::current(), tm.key))?
    }

    /// Check if a term is an abstraction.
    pub fn is_abs(&self, tm: &Term) -> Result<bool> {
        self.execute(self.interface().is_abs(context::current(), tm.key))?
    }

    /// Check if a term is an application of the given binary operator. 
    pub fn is_binop(&self, op: &Term, tm: &Term) -> Result<bool> {
      self.execute(self.interface().is_binop(context::current(), op.key, tm.key))?
    }

    /// Check if a term is a binder construct with named constant.
    pub fn is_binder(&self, s: String, tm: &Term) -> Result<bool> {
      self.execute(self.interface().is_binder(context::current(), s, tm.key))?
    }

    /// Destruct a variable.
    pub fn dest_var(&self, tm: &Term) -> Result<(String, Type)> {
        let (name, ty) = self.execute(self.interface().dest_var(context::current(), tm.key))??;
        Ok((name, Type::new(ty, self.clone())))
    }

    /// Destruct a constant.
    pub fn dest_const(&self, tm: &Term) -> Result<(String, Type)> {
        let (name, ty) =
            self.execute(self.interface().dest_const(context::current(), tm.key))??;
        Ok((name, Type::new(ty, self.clone())))
    }

    /// Destruct an application.
    pub fn dest_comb(&self, tm: &Term) -> Result<(Term, Term)> {
        let (tm1, tm2) = self.execute(self.interface().dest_comb(context::current(), tm.key))??;
        Ok((Term::new(tm1, self.clone()), Term::new(tm2, self.clone())))
    }

    /// Destruct an abstraction.
    pub fn dest_abs(&self, tm: &Term) -> Result<(Term, Term)> {
        let (tm1, tm2) = self.execute(self.interface().dest_abs(context::current(), tm.key))??;
        Ok((Term::new(tm1, self.clone()), Term::new(tm2, self.clone())))
    }

    /// Destruct an application of the given binary operator.
    pub fn dest_binop(&self, op: &Term, tm: &Term) -> Result<(Term, Term)> {
      let (tm1, tm2) = self.execute(self.interface().dest_binop(context::current(), op.key, tm.key))??;
      Ok((Term::new(tm1, self.clone()), Term::new(tm2, self.clone())))
    }

    /// Destruct a binder construct.
    pub fn dest_binder(&self, s: String, tm: &Term) -> Result<(Term, Term)> {
      let (tm1, tm2) = self.execute(self.interface().dest_binder(context::current(), s, tm.key))??;
      Ok((Term::new(tm1, self.clone()), Term::new(tm2, self.clone())))
    }

    /// Construct a abstraction.
    pub fn mk_abs(&self, th1: &Term, th2: &Term) -> Result<Term> {
      let tm = self.execute(self.interface().mk_abs(context::current(), th1.key, th2.key))??;
      Ok(Term::new(tm, self.clone()))
    } 

    /// Construct a combination.
    pub fn mk_comb(&self, th1: &Term, th2: &Term) -> Result<Term> {
      let tm = self.execute(self.interface().mk_comb(context::current(), th1.key, th2.key))??;
      Ok(Term::new(tm, self.clone()))
    } 

    /// Conclusion of a theorem.
    pub fn concl(&self, th: &Theorem) -> Result<Term> {
      let tm = self.execute(self.interface().concl(context::current(), th.key))??;
      Ok(Term::new(tm, self.clone()))
    }

    /// Return one hypothesis of a theorem. 
    pub fn hypth(&self, th: &Theorem) -> Result<Term> {
      let tm = self.execute(self.interface().hypth(context::current(), th.key))??;
      Ok(Term::new(tm, self.clone()))
    }

    /// Create a new type.
    pub fn new_type(&self, name: String, arity: u32) -> Result<()> {
        self.execute(self.interface().new_type(context::current(), name, arity))?
    }

    /// Declare a new constant.
    pub fn new_constant(&self, name: String, ty: &Type) -> Result<()> {
        self.execute(
            self.interface()
                .new_constant(context::current(), name, ty.key),
        )?
    }

    /// Set up a new axiom.
    pub fn new_axiom(&self, tm: &Term) -> Result<Theorem> {
        let key = self.execute(self.interface().new_axiom(context::current(), tm.key))??;
        Ok(Theorem::new(key, self.clone()))
    }

    /// Define a relation or family of relations inductively. 
    pub fn new_inductive_definition(&self, tm: &Term) -> Result<IndDef> {
      let key = self.execute(self.interface().new_inductive_definition(context::current(), tm.key))??;
      Ok(IndDef {
        def: Theorem::new(key.def, self.clone()),
        ind: Theorem::new(key.ind, self.clone()),
        cases: Theorem::new(key.cases, self.clone()),
      })
    }

    /// Proves a propositional tautology.
    pub fn taut(&self, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().taut(context::current(), tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Automatically proves natural number arithmetic theorems. 
    pub fn arith_rule(&self, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().arith_rule(context::current(), tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Proves integer theorems needing basic rearrangement and linear inequality reasoning only. 
    pub fn int_arith(&self, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().int_arith(context::current(), tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Get a theorem from the search database.
    pub fn get_theorem(&self, name: String) -> Result<Theorem> {
      let key = self.execute(self.interface().get_theorem(context::current(), name))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// `sep lift` conversion.
    pub fn sep_lift(&self, lft: &Term, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().sep_lift(context::current(), lft.key, tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// `which implies` conversion.
    pub fn which_implies(&self, state: &Term, trans: &Theorem) -> Result<Theorem> {
      let key = self.execute(self.interface().which_implies(context::current(), state.key, trans.key))??;
      Ok(Theorem::new(key, self.clone()))
    }

    /// Applies a conversion to the operand of an application. 
    pub fn rand_conv(&self, conv: &Conversion) -> Result<Conversion> {
      let key = self.execute(self.interface().rand_conv(context::current(), conv.key))??;
      Ok(Conversion::new(key, self.clone()))
    }

    /// Applies a conversion.
    pub fn apply_conv(&self, conv: &Conversion, tm: &Term) -> Result<Theorem> {
      let key = self.execute(self.interface().apply_conv(context::current(), conv.key, tm.key))??;
      Ok(Theorem::new(key, self.clone()))
    }
}
