(** * OL/Hoare.v — Hoare Logic Subsumption (Theorem 3.4)

    Proves that standard Hoare Logic triples are subsumed by OL
    triples when assertions are restricted to atomic predicates
    over the nondeterministic powerset execution model.

    Main results:
    - [hoare_subsumption]:       {P} C {Q}       ↔  ⊨_pc ⟨P⟩ C ⟨Q⟩
    - [hoare_total_subsumption]: {P} C {Q}_total  ↔  ⊨ ⟨P⟩ C ⟨Q⟩

    The key insight is that Hoare partial correctness triples
    correspond to OL partial correctness triples [⊨_pc ⟨φ⟩ C ⟨ψ⟩]
    when φ and ψ are atomic assertions.  The postcondition
    [ψ ∨ ⊤⊕] allows the program to produce no outcomes (diverge
    or abort), which is exactly the partiality in Hoare Logic.

    For total correctness (every input produces at least one outcome),
    the exact OL triple [⊨ ⟨φ⟩ C ⟨ψ⟩] is the corresponding form.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Theorem 3.4, Appendix A *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang Triple.

(* ================================================================= *)
(** ** Hoare Triple Definitions                                       *)
(* ================================================================= *)

(** Standard Hoare partial correctness triple for the powerset model
    (Figure 3 of the paper):

      ⊨ {P} C {Q}  ≜  ∀σ. P(σ) → ∀τ ∈ ⟦C⟧(σ). Q(τ)

    If C aborts (⟦C⟧(σ) = ∅), the triple holds vacuously. *)

Definition hoare_valid {Sigma : Type}
    (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) : Prop :=
  forall sigma, P sigma ->
    forall tau, In _ (denote sigma) tau -> Q tau.

(** Hoare total correctness: partial correctness plus termination
    (non-empty outcomes for every input satisfying the precondition). *)

Definition hoare_total_valid {Sigma : Type}
    (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) : Prop :=
  forall sigma, P sigma ->
    (exists tau, In _ (denote sigma) tau) /\
    (forall tau, In _ (denote sigma) tau -> Q tau).

(* ================================================================= *)
(** ** Theorem 3.4 — Subsumption of Hoare Partial Correctness        *)
(* ================================================================= *)

(** The central result: Hoare partial correctness is equivalent to
    OL partial correctness when pre- and postconditions are atomic.

    ⊨ {P} C {Q}  ↔  ⊨_pc ⟨P⟩ C ⟨Q⟩

    The proof follows the paper's Appendix A argument:

    Forward (⇒): Given S ⊨ P (non-empty, all elements satisfy P),
    the collecting semantics ⟦C⟧†(S) = ⋃_{σ∈S} ⟦C⟧(σ) either
    is non-empty (and all elements satisfy Q by Hoare validity)
    or is empty (satisfying ⊤⊕).

    Backward (⇐): For any σ with P(σ), the singleton {σ} satisfies
    BiAtom P. Applying OL-pc gives ⟦C⟧(σ) ⊨ Q ∨ ⊤⊕, from which
    Q(τ) follows for any τ ∈ ⟦C⟧(σ). *)

Section HoareSubsumption.

  Context {Sigma : Type}.
  Variable denote : Sigma -> PSet Sigma.

  (* --------------------------------------------------------------- *)
  (** *** Partial Correctness                                          *)
  (* --------------------------------------------------------------- *)

  Lemma hoare_implies_ol_pc (P Q : Sigma -> Prop) :
    hoare_valid P denote Q ->
    ol_valid_pc nd_atom_sat denote (BiAtom P) (BiAtom Q).
  Proof.
    intros Hhoare m Hpre.
    simpl in Hpre. destruct Hpre as [[sigma0 Hne] HforallP].
    simpl.
    destruct (classic (exists tau, In _ (collect denote m) tau))
      as [Hne_post | Hempty_post].
    - (* Non-empty outcomes: all satisfy Q *)
      left. split.
      + exact Hne_post.
      + intros tau Htau.
        unfold collect, pset_bind, In in Htau.
        destruct Htau as [sigma [Hin_m Hin_den]].
        exact (Hhoare sigma (HforallP sigma Hin_m) tau Hin_den).
    - (* Empty outcomes: program aborted/diverged *)
      right.
      apply ensemble_ext. intro tau. split.
      + intro Hin. exfalso. exact (Hempty_post (ex_intro _ tau Hin)).
      + intro Hempty. inversion Hempty.
  Qed.

  Lemma ol_pc_implies_hoare (P Q : Sigma -> Prop) :
    ol_valid_pc nd_atom_sat denote (BiAtom P) (BiAtom Q) ->
    hoare_valid P denote Q.
  Proof.
    intros Hol sigma Hp tau Htau.
    assert (Hpre : bi_sat nd_atom_sat (pset_ret sigma) (BiAtom P)).
    { simpl. split.
      - exists sigma. constructor.
      - intros sigma' Hin. inversion Hin; subst. exact Hp. }
    specialize (Hol (pset_ret sigma) Hpre).
    assert (Hcol : collect denote (pset_ret sigma) = denote sigma).
    { unfold collect. apply pset_bind_ret_l. }
    rewrite Hcol in Hol. simpl in Hol.
    destruct Hol as [[_ HforallQ] | Hempty].
    - exact (HforallQ tau Htau).
    - rewrite Hempty in Htau. inversion Htau.
  Qed.

  (** Theorem 3.4 *)
  Theorem hoare_subsumption (P Q : Sigma -> Prop) :
    hoare_valid P denote Q <->
    ol_valid_pc nd_atom_sat denote (BiAtom P) (BiAtom Q).
  Proof.
    split; [apply hoare_implies_ol_pc | apply ol_pc_implies_hoare].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Total Correctness                                            *)
  (* --------------------------------------------------------------- *)

  (** Total correctness corresponds to the exact OL triple (no
      partiality disjunct), because OL's [nd_atom_sat] requires
      non-emptiness: the set of outcomes must be non-empty and
      all elements must satisfy Q. *)

  Lemma hoare_total_implies_ol (P Q : Sigma -> Prop) :
    hoare_total_valid P denote Q ->
    ol_valid nd_atom_sat denote (BiAtom P) (BiAtom Q).
  Proof.
    intros Htotal m Hpre.
    simpl in Hpre. destruct Hpre as [[sigma0 Hne0] HforallP].
    simpl. split.
    - destruct (Htotal sigma0 (HforallP sigma0 Hne0)) as [[tau0 Hin0] _].
      exists tau0. unfold collect, pset_bind, In.
      exists sigma0. split; assumption.
    - intros tau Htau.
      unfold collect, pset_bind, In in Htau.
      destruct Htau as [sigma [Hin_m Hin_den]].
      destruct (Htotal sigma (HforallP sigma Hin_m)) as [_ HforallQ].
      exact (HforallQ tau Hin_den).
  Qed.

  Lemma ol_implies_hoare_total (P Q : Sigma -> Prop) :
    ol_valid nd_atom_sat denote (BiAtom P) (BiAtom Q) ->
    hoare_total_valid P denote Q.
  Proof.
    intros Hol sigma Hp.
    assert (Hpre : bi_sat nd_atom_sat (pset_ret sigma) (BiAtom P)).
    { simpl. split.
      - exists sigma. constructor.
      - intros sigma' Hin. inversion Hin; subst. exact Hp. }
    specialize (Hol (pset_ret sigma) Hpre).
    assert (Hcol : collect denote (pset_ret sigma) = denote sigma).
    { unfold collect. apply pset_bind_ret_l. }
    rewrite Hcol in Hol. simpl in Hol.
    exact Hol.
  Qed.

  Theorem hoare_total_subsumption (P Q : Sigma -> Prop) :
    hoare_total_valid P denote Q <->
    ol_valid nd_atom_sat denote (BiAtom P) (BiAtom Q).
  Proof.
    split; [apply hoare_total_implies_ol | apply ol_implies_hoare_total].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Derived Properties                                           *)
  (* --------------------------------------------------------------- *)

  (** Total correctness implies partial correctness. *)
  Lemma hoare_total_implies_partial (P Q : Sigma -> Prop) :
    hoare_total_valid P denote Q ->
    hoare_valid P denote Q.
  Proof.
    intros Htotal sigma Hp tau Htau.
    destruct (Htotal sigma Hp) as [_ HQ]. exact (HQ tau Htau).
  Qed.

  (** Hoare consequence rule (pre-strengthening + post-weakening). *)
  Lemma hoare_consequence (P P' Q Q' : Sigma -> Prop) :
    (forall sigma, P sigma -> P' sigma) ->
    hoare_valid P' denote Q' ->
    (forall sigma, Q' sigma -> Q sigma) ->
    hoare_valid P denote Q.
  Proof.
    intros Hpre Hhoare Hpost sigma Hp tau Htau.
    exact (Hpost tau (Hhoare sigma (Hpre sigma Hp) tau Htau)).
  Qed.

  (** Hoare validity respects extensional equality of denotations. *)
  Lemma hoare_denote_ext (denote' : Sigma -> PSet Sigma)
      (P Q : Sigma -> Prop) :
    (forall sigma, denote sigma = denote' sigma) ->
    hoare_valid P denote Q ->
    hoare_valid P denote' Q.
  Proof.
    intros Heq Hhoare sigma Hp tau Htau.
    apply Hhoare with sigma; [exact Hp |].
    rewrite Heq. exact Htau.
  Qed.

End HoareSubsumption.
