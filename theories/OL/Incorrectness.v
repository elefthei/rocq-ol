(** * OL/Incorrectness.v — Incorrectness Logic Subsumption

    Formalizes Incorrectness Logic (IL) triples and their relationship
    to Outcome Logic, following the OOPSLA 2023 paper's claim that
    OL provides a unifying foundation for correctness and incorrectness.

    Main results:
    - [il_singleton_implies_ol_under]:  [{σ₀}] C [Q]  →  ⊨↓ ⟨{σ₀}⟩ C ⟨Q⟩
    - [il_iff_pointwise_reachability]:  [P] C [Q]  ↔  pointwise reachability
    - [il_implies_neg_hoare]:           [P] C [Q]  →  ¬{P} C {¬Q}
    - [il_consequence]:                 Pre-weakening + post-strengthening

    IL triple semantics (O'Hearn 2019):

        ⊨ [P] C [Q]  ≜  ∀τ. Q(τ) → ∃σ. P(σ) ∧ τ ∈ ⟦C⟧(σ)

    Every state satisfying postcondition Q must be *reachable* from
    some state satisfying precondition P.  This is backward reachability:
    "no false positives" — any bug reported actually occurs.

    Relationship to OL:
    - IL is strictly STRONGER than OL under-approx for atomic assertions
    - IL: ALL Q-states are reachable from P-states
    - OL under-approx: SOME Q-states appear in outcomes from P-states
    - For singleton preconditions, the embedding is direct
    - The full connection goes through falsification (Corollary 4.10)

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Sections 3 and 4 *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang Triple Hoare.

(* ================================================================= *)
(** ** IL Triple Definition                                           *)
(* ================================================================= *)

(** Incorrectness Logic triple (O'Hearn 2019):

      ⊨ [P] C [Q]  ≜  ∀τ. Q(τ) → ∃σ. P(σ) ∧ τ ∈ ⟦C⟧(σ)

    Backward reachability: every Q-state is reachable from some
    P-state via the program C.  Equivalently: Q ⊆ Post(P, C)
    where Post(P, C) = {τ | ∃σ⊨P. τ ∈ ⟦C⟧(σ)}. *)

Definition il_valid {Sigma : Type}
    (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) : Prop :=
  forall tau, Q tau ->
    exists sigma, P sigma /\ In _ (denote sigma) tau.

(* ================================================================= *)
(** ** OL Subsumes IL (Singleton Preconditions)                       *)
(* ================================================================= *)

Section ILSubsumption.

  Context {Sigma : Type}.
  Variable denote : Sigma -> PSet Sigma.

  (** For singleton preconditions [{σ₀}], IL triples directly
      embed into OL under-approximate triples.

      If all Q-states are reachable from σ₀, then running C
      on {σ₀} produces outcomes including some Q-states.

      This is the most direct "OL subsumes IL" result. *)

  Theorem il_singleton_implies_ol_under
      (sigma0 : Sigma) (Q : Sigma -> Prop) :
    (forall tau, Q tau -> In _ (denote sigma0) tau) ->
    (exists tau, Q tau) ->
    ol_valid_under nd_atom_sat denote (BiAtom (eq sigma0)) (BiAtom Q).
  Proof.
    intros Hil [tau0 Hq0] m Hpre.
    simpl in Hpre. destruct Hpre as [[s0 Hne] Hforall].
    simpl.
    (* tau0 is a Q-state reachable from sigma0 *)
    assert (Htau0_in : In _ (collect denote m) tau0).
    { unfold collect, pset_bind, In.
      exists s0. split.
      - exact Hne.
      - assert (Heq : sigma0 = s0) by exact (Hforall s0 Hne).
        subst s0. exact (Hil tau0 Hq0). }
    (* Split outcomes: Q-part ∪ rest *)
    exists (fun tau => In _ (collect denote m) tau /\ Q tau),
           (fun tau => In _ (collect denote m) tau /\ ~ Q tau).
    split.
    - (* Union decomposition: m1 ∪ m2 = collect denote m *)
      apply ensemble_ext. intro tau. split.
      + (* pset_union → collect *)
        intro Hin. destruct Hin as [? [Hin' _] | ? [Hin' _]]; exact Hin'.
      + (* collect → pset_union *)
        intro Hin.
        destruct (classic (Q tau)) as [HQ | HnQ].
        * apply Union_introl. exact (conj Hin HQ).
        * apply Union_intror. exact (conj Hin HnQ).
    - split.
      + split.
        * exists tau0. exact (conj Htau0_in Hq0).
        * intros tau [_ HQ]. exact HQ.
      + exact I.
  Qed.

  (* ================================================================= *)
  (** ** IL ↔ Pointwise Reachability                                   *)
  (* ================================================================= *)

  (** IL is equivalent to a pointwise condition: for each Q-state τ,
      the Hoare triple {P} C {σ ≠ τ} fails.  In other words, each
      Q-state τ cannot be excluded from the outcomes of P-states.

      This uses classical logic (NNPP) for the backward direction. *)

  Theorem il_iff_pointwise_reachability (P Q : Sigma -> Prop) :
    il_valid P denote Q <->
    (forall tau, Q tau ->
       ~ hoare_valid P denote (fun sigma => sigma <> tau)).
  Proof.
    split.
    - intros Hil tau HQ Hhoare.
      destruct (Hil tau HQ) as [sigma [Hp Hin]].
      exact (Hhoare sigma Hp tau Hin eq_refl).
    - intros Hpw tau HQ.
      specialize (Hpw tau HQ).
      apply NNPP. intro Habs.
      apply Hpw. intros sigma Hp tau' Htau' Heq.
      subst tau'. apply Habs. exists sigma. exact (conj Hp Htau').
  Qed.

  (* ================================================================= *)
  (** ** IL → Negated Hoare                                            *)
  (* ================================================================= *)

  (** IL implies the negation of the Hoare triple with complemented
      postcondition.  The converse does NOT hold in general:
      ¬{P}C{¬Q} gives ONE witness pair (σ, τ), while IL requires
      ALL Q-states to be reachable.

      IL is strictly stronger than ¬Hoare(¬Q). *)

  Lemma il_implies_neg_hoare (P Q : Sigma -> Prop) :
    il_valid P denote Q ->
    (exists tau, Q tau) ->
    ~ hoare_valid P denote (fun sigma => ~ Q sigma).
  Proof.
    intros Hil [tau0 Hq0] Hhoare.
    destruct (Hil tau0 Hq0) as [sigma [Hp Hin]].
    exact (Hhoare sigma Hp tau0 Hin Hq0).
  Qed.

  (** The converse gives only a single witness, not full IL. *)
  Lemma neg_hoare_implies_witness (P Q : Sigma -> Prop) :
    ~ hoare_valid P denote (fun sigma => ~ Q sigma) ->
    exists sigma tau, P sigma /\ In _ (denote sigma) tau /\ Q tau.
  Proof.
    intro Hfail.
    apply NNPP. intro Habs.
    apply Hfail. intros sigma Hp tau Hin HQ.
    apply Habs. exists sigma, tau. exact (conj Hp (conj Hin HQ)).
  Qed.

  (* ================================================================= *)
  (** ** Derived Properties                                            *)
  (* ================================================================= *)

  (** IL consequence: pre-WEAKENING + post-STRENGTHENING.
      Directions are flipped compared to Hoare Logic!

      In Hoare: pre-strengthen, post-weaken  (∀σ→∀τ).
      In IL:    pre-weaken, post-strengthen   (∀τ→∃σ).

      Weakening P makes it easier to find a P-witness.
      Strengthening Q reduces the Q-states to witness. *)

  Lemma il_consequence (P P' Q Q' : Sigma -> Prop) :
    (forall sigma, P sigma -> P' sigma) ->
    il_valid P denote Q ->
    (forall sigma, Q' sigma -> Q sigma) ->
    il_valid P' denote Q'.
  Proof.
    intros Hpre Hil Hpost tau HQ'.
    destruct (Hil tau (Hpost tau HQ')) as [sigma [Hp Hin]].
    exists sigma. split.
    - exact (Hpre sigma Hp).
    - exact Hin.
  Qed.

  (** IL with empty postcondition is vacuously true.
      (No Q-states to witness → nothing to prove.) *)
  Lemma il_empty (P : Sigma -> Prop) :
    il_valid P denote (fun _ => False).
  Proof.
    intros tau Habs. contradiction.
  Qed.

  (** IL respects extensional equality of denotations. *)
  Lemma il_denote_ext (denote' : Sigma -> PSet Sigma)
      (P Q : Sigma -> Prop) :
    (forall sigma, denote sigma = denote' sigma) ->
    il_valid P denote Q ->
    il_valid P denote' Q.
  Proof.
    intros Heq Hil tau HQ.
    destruct (Hil tau HQ) as [sigma [Hp Hin]].
    exists sigma. split; [exact Hp |].
    rewrite <- Heq. exact Hin.
  Qed.

End ILSubsumption.
