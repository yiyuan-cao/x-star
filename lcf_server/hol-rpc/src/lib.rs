//! A tarpc service for interacting with the HOL Light theorem prover.
#![deny(missing_docs)]

#[macro_use]
pub mod caml_dyn_call;
pub mod client;
pub mod error;
mod interface_client;

use serde::{Deserialize, Serialize};

pub use crate::error::{Result, RpcError};

/// The RPC interface.
#[tarpc::service]
pub trait Interface {
    /// Dispose a term.
    async fn dispose_term(key: TermKey) -> Result<()>;

    /// Dispose a theorem.
    async fn dispose_theorem(key: TheoremKey) -> Result<()>;

    /// Dispose a type.
    async fn dispose_type(key: TypeKey) -> Result<()>;

    /// Dispose a conversion. 
    async fn dispose_conversion(key: ConversionKey) -> Result<()>;

    /// Parse a term from a string.
    async fn parse_term_from_string(s: String) -> Result<TermKey>;

    /// Parse a type from a string.
    async fn parse_type_from_string(s: String) -> Result<TypeKey>;

    /// Parse a conversion from a string.
    async fn parse_conv_from_string(s: String) -> Result<ConversionKey>;

    /// Convert a term to a string.
    async fn string_of_term(key: TermKey) -> Result<String>;

    /// Convert a theorem to a string.
    async fn string_of_thm(key: TheoremKey) -> Result<String>;

    /// Dump a Coq axiom.
    async fn dump_coq_axiom(name: String, key: TheoremKey) -> Result<String>;

    /// Theorem: A |- A
    async fn assume(term: TermKey) -> Result<TheoremKey>;

    /// Transitivity of equality.
    ///
    /// ```text
    /// A1 |- a = b  A2 |- b = c
    /// -------------------------
    /// A1, A2 |- a = c
    /// ```
    async fn trans(th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey>;

    /// Reflexivity.
    ///
    /// ```text
    /// ----------
    /// A |- a = a
    /// ```
    async fn refl(tm: TermKey) -> Result<TheoremKey>;

    /// Discharge an assumption.
    ///
    /// ```text
    /// A, u |- t
    /// ---------
    /// A |- u ==> t
    /// ```
    async fn disch(th: TheoremKey, tm: TermKey) -> Result<TheoremKey>;

    /// Undischarges the antecedent of an implicative theorem.
    /// 
    /// ```text
    /// A |- t1 ==> t2
    /// --------------
    ///   A, t1 |- t2
    /// ```
    async fn undisch(th: TheoremKey) -> Result<TheoremKey>;

    /// Generalize a free term in a theorem.
    ///
    /// ```text
    /// A |- t
    /// -------     (x not free in A)
    /// A |- !x. t
    /// ```
    async fn gen(tm: TermKey, th: TheoremKey) -> Result<TheoremKey>;

    /// Specializes the conclusion of a theorem with its own quantified variables.
    ///
    /// ```text
    /// A |- !x1...xn. t
    /// -------------------------
    /// A |- t[x1'/x1]...[xn'/xn]
    /// ```
    async fn spec_all(th: TheoremKey) -> Result<TheoremKey>;

    /// Specializes the conclusion of a theorem.
    ///
    /// ```text
    /// A |- !x. t
    /// ----------- SPEC `u`
    /// A |- t[u/x]
    /// ```
    async fn spec(tm: TermKey, th: TheoremKey) -> Result<TheoremKey>;

    /// Modus ponens with automatic matching.
    ///
    /// ```text
    /// A1 |- !x1..xn. t1 ==> t2   A2 |- t1'
    /// ------------------------------------
    /// A1, A2 |- !xa..xk. t2'
    /// ```
    async fn mp(th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey>;

    /// Equality version of the Modus Ponens rule.
    ///
    /// ```text
    /// A1 |- t1 <=> t2   A2 |- t1'
    /// ---------------------------
    ///       A1 u A2 |- t2
    /// ```
    async fn eq_mp(th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey>;

    /// Conjunction.
    ///
    /// ```text
    /// A1 |- t1  A2 |- t2
    /// ------------------
    /// A1, A2 |- t1 /\ t2
    /// ```
    async fn conjunct(th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey>;

    /// Extracts left conjunct of theorem.
    ///
    /// ```text
    /// A |- t1 /\ t2
    /// -------------
    ///    A |- t1
    /// ```
    async fn conjunct1(th: TheoremKey) -> Result<TheoremKey>;

    /// Extracts right conjunct of theorem.
    ///
    /// ```text
    /// A |- t1 /\ t2
    /// -------------
    ///    A |- t2
    /// ```
    async fn conjunct2(th: TheoremKey) -> Result<TheoremKey>;

    /// Symmetry.
    ///
    /// ```text
    /// A |- t1 = t2
    /// ------------
    /// A |- t2 = t1
    /// ```
    async fn symm(th: TheoremKey) -> Result<TheoremKey>;

    /// Eliminates disjunction by cases.
    ///
    /// ```text
    /// A |- t1 \/ t2   A1 |- t   A2 |- t
    /// ----------------------------------
    /// A u (A1 - {t1}) u (A2 - {t2}) |- t
    /// ```
    async fn disj_cases(th1: TheoremKey, th2: TheoremKey, th3: TheoremKey) -> Result<TheoremKey>;

    /// Deduces logical equivalence from deduction in both directions.
    ///
    /// ```text
    ///      A |- p        B |- q
    /// --------------------------------
    /// (A - {q}) u (B - {p}) |- p <=> q
    /// ```
    async fn deduct_antisym(th1: TheoremKey, th2: TheoremKey) -> Result<TheoremKey>;

    /// Existentially quantifies a hypothesis of a theorem.
    ///
    /// ```text
    /// A |- t   `x` is not free in `A |- t`
    /// ------------------------------------ CHOOSE `x` th
    ///            A |- ?x. t
    /// ```
    async fn choose(tm: TermKey, th: TheoremKey) -> Result<TheoremKey>;

    /// Define an inductive type.
    async fn define_type(tm: String) -> Result<IndTypeKey>;

    /// Define a new constant or function.
    async fn define(tm: TermKey) -> Result<TheoremKey>;

    /// Uses an instance of a given equation to rewrite a term.
    async fn rewrite(th: TheoremKey, tm: TermKey) -> Result<TheoremKey>;

    /// Uses an instance of a given equation to rewrite a theorem.
    async fn rewrite_rule(th: TheoremKey, t: TheoremKey) -> Result<TheoremKey>;

    /// Uses an instance of a given equation to rewrite a term only once.
    async fn once_rewrite(th: TheoremKey, tm: TermKey) -> Result<TheoremKey>;

    /// Uses an instance of a give equation to rewrite a theorem only once.
    async fn once_rewrite_rule(th: TheoremKey, t: TheoremKey) -> Result<TheoremKey>;

    /// Instantiation of induction principle.
    async fn induction_aux(th: TheoremKey, tm1: TermKey, tm2: TermKey) -> Result<TheoremKey>;

    /// Substitute terms for other terms inside a term.
    async fn subst(tm1: TermKey, tm2: TermKey, tm: TermKey) -> Result<TermKey>;

    /// Check if a term is a variable.
    async fn is_var(th: TermKey) -> Result<bool>;

    /// Check if a term is a constant.
    async fn is_const(th: TermKey) -> Result<bool>;

    /// Check if a term is an application.
    async fn is_comb(th: TermKey) -> Result<bool>;

    /// Check if a term is an abstraction.
    async fn is_abs(th: TermKey) -> Result<bool>;

    /// Check if a term is an application of the given binary operator. 
    async fn is_binop(op: TermKey, tm: TermKey) -> Result<bool>;

    /// Check if a term is a binder construct with named constant.
    async fn is_binder(s: String, tm: TermKey) -> Result<bool>;

    /// Destruct a variable.
    async fn dest_var(th: TermKey) -> Result<(String, TypeKey)>;

    /// Destruct a constant.
    async fn dest_const(th: TermKey) -> Result<(String, TypeKey)>;

    /// Destruct an application.
    async fn dest_comb(th: TermKey) -> Result<(TermKey, TermKey)>;

    /// Destruct an abstraction.
    async fn dest_abs(th: TermKey) -> Result<(TermKey, TermKey)>;

    /// Destruct an application of the given binary operator.
    async fn dest_binop(op: TermKey, tm: TermKey) -> Result<(TermKey, TermKey)>;

    /// Destruct a binder construct.
    async fn dest_binder(s: String, tm: TermKey) -> Result<(TermKey, TermKey)>;

    /// Construct a abstraction.
    async fn mk_abs(th1: TermKey, th2: TermKey) -> Result<TermKey>;

    /// Construct a combination.
    async fn mk_comb(th1: TermKey, th2: TermKey) -> Result<TermKey>;

    /// Conclusion of a theorem.
    async fn concl(th: TheoremKey) -> Result<TermKey>;

    /// Return one hypothesis of a theorem. 
    async fn hypth(th: TheoremKey) -> Result<TermKey>;

    /// Create a new type.
    async fn new_type(name: String, arity: u32) -> Result<()>;

    /// Declare a new constant.
    async fn new_constant(name: String, ty: TypeKey) -> Result<()>;

    /// Set up a new axiom.
    async fn new_axiom(tm: TermKey) -> Result<TheoremKey>;

    /// Define a relation or family of relations inductively.
    async fn new_inductive_definition(tm: TermKey) -> Result<IndDefKey>;

    /// Automatically proves natural number arithmetic theorems. 
    async fn arith_rule(tm: TermKey) -> Result<TheoremKey>;

    /// Get a theorem from the search database.
    async fn get_theorem(name: String) -> Result<TheoremKey>;

    /// `sep lift` conversion.
    async fn sep_lift(lft: TermKey, tm: TermKey) -> Result<TheoremKey>;

    /// `which implies` conversion.
    async fn which_implies(state: TermKey, trans: TheoremKey) -> Result<TheoremKey>;

    /// Applies a conversion to the operand of an application. 
    async fn rand_conv(conv: ConversionKey) -> Result<ConversionKey>;

    /// Applies a conversion.
    async fn apply_conv(conv: ConversionKey, tm: TermKey) -> Result<TheoremKey>;
}

slotmap::new_key_type! {
    /// Key for a term.
    pub struct TermKey;

    /// Key for a theorem.
    pub struct TheoremKey;

    /// Key for a type.
    pub struct TypeKey;

    /// Key for a conversion.
    pub struct ConversionKey; 
}

/// Key for an inductive type.
#[derive(Debug, Deserialize, Serialize)]
pub struct IndTypeKey {
    /// The inductive theorem.
    pub ind: TheoremKey,
    /// The recursion theorem.
    pub rec: TheoremKey,
}

/// Key for an inductive relation.
#[derive(Debug, Deserialize, Serialize)]
pub struct IndDefKey {
    /// definition.
    pub def: TheoremKey,
    /// inductive rule.
    pub ind: TheoremKey,
    /// cases rule.
    pub cases: TheoremKey,
}
