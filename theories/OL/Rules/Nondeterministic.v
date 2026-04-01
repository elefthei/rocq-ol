(** * OL/Rules/Nondeterministic.v — Nondeterministic Proof Rules

    Proves the nondeterministic-model-specific proof rules for
    Outcome Logic over the powerset monad:

    - **Plus**:  ⊨ ⟨φ⟩ C₁ ⟨ψ₁⟩  →  ⊨ ⟨φ⟩ C₂ ⟨ψ₂⟩  →  ⊨ ⟨φ⟩ C₁+C₂ ⟨ψ₁ ⊕ ψ₂⟩
    - **Induction**: various forms for reasoning about C⋆

    These rules are specific to the nondeterministic powerset execution
    model (where the PCM is set union).  They leverage the facts that
    ⟦C₁+C₂⟧(σ) = ⟦C₁⟧(σ) ∪ ⟦C₂⟧(σ) and ⟦C⋆⟧(σ) = ⋃ₙ ⟦Cⁿ⟧(σ).

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Figure 5 (nondeterministic rules) *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang Triple.

(* ================================================================= *)
(** ** Auxiliary Set Lemmas                                             *)
(* ================================================================= *)

Section Auxiliary.

  Context {A : Type}.

  (** Union absorbs subsets: if S₁ ⊆ S₂ then S₁ ∪ S₂ = S₂. *)
  Lemma pset_union_incl_r (S1 S2 : PSet A) :
    (forall x, In _ S1 x -> In _ S2 x) ->
    pset_union S1 S2 = S2.
  Proof.
    intro Hsub. apply ensemble_ext. intro x. split.
    - intro H. inversion H; subst; auto.
    - intro H. apply Union_intror. exact H.
  Qed.

  (** Interchange law: [(a₁ ∪ a₂) ∪ (b₁ ∪ b₂) = (a₁ ∪ b₁) ∪ (a₂ ∪ b₂)]. *)
  Lemma pset_union_interchange (a1 a2 b1 b2 : PSet A) :
    pset_union (pset_union a1 a2) (pset_union b1 b2) =
    pset_union (pset_union a1 b1) (pset_union a2 b2).
  Proof.
    rewrite (pset_union_assoc a1 a2 (pset_union b1 b2)).
    rewrite <- (pset_union_assoc a2 b1 b2).
    rewrite (pset_union_comm a2 b1).
    rewrite (pset_union_assoc b1 a2 b2).
    rewrite <- (pset_union_assoc a1 b1 (pset_union a2 b2)).
    reflexivity.
  Qed.

End Auxiliary.

(* ================================================================= *)
(** ** Semantic Lemmas — Plus                                          *)
(* ================================================================= *)

Section PlusSemantic.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** Bind distributes into pointwise union of the continuation:
      [bind m (λσ. f(σ) ∪ g(σ)) = bind(m, f) ∪ bind(m, g)]. *)
  Lemma pset_bind_union_pointwise (m : PSet Sigma)
      (f g : Sigma -> PSet Sigma) :
    pset_bind m (fun sigma => pset_union (f sigma) (g sigma)) =
      pset_union (pset_bind m f) (pset_bind m g).
  Proof.
    apply ensemble_ext. intro b. unfold pset_bind, pset_union. split.
    - intros [sigma [Hm Hunion]].
      inversion Hunion; subst.
      + apply Union_introl. exists sigma. auto.
      + apply Union_intror. exists sigma. auto.
    - intros Hunion. inversion Hunion; subst;
        destruct H as [sigma [Hm Hk]]; exists sigma; split; auto.
      + apply Union_introl. exact Hk.
      + apply Union_intror. exact Hk.
  Qed.

  (** Collecting semantics distributes over nondeterministic choice:
      [collect(⟦C₁+C₂⟧, m) = collect(⟦C₁⟧, m) ∪ collect(⟦C₂⟧, m)]. *)
  Lemma collect_denote_plus (C1 C2 : ol_prog Atom) (m : PSet Sigma) :
    collect (ol_denote atom_den (OLPlus C1 C2)) m =
      pset_union (collect (ol_denote atom_den C1) m)
                 (collect (ol_denote atom_den C2) m).
  Proof.
    unfold collect. simpl. apply pset_bind_union_pointwise.
  Qed.

End PlusSemantic.

(* ================================================================= *)
(** ** Semantic Lemmas — Sequential Composition                        *)
(* ================================================================= *)

Section SeqSemantic.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** Collecting semantics of sequential composition factors through
      the intermediate collecting:
      [collect(⟦C;D⟧, m) = collect(⟦D⟧, collect(⟦C⟧, m))]. *)
  Lemma collect_seq (C D : ol_prog Atom) (m : PSet Sigma) :
    collect (ol_denote atom_den (OLSeq C D)) m =
      collect (ol_denote atom_den D) (collect (ol_denote atom_den C) m).
  Proof.
    apply ensemble_ext. intro tau.
    unfold collect, pset_bind, In. split.
    - intros [sigma [Hm Hseq]].
      simpl in Hseq.
      destruct Hseq as [mid [Hc Hd]].
      exists mid. split; [| exact Hd].
      exists sigma. auto.
    - intros [mid [[sigma [Hm Hc]] Hd]].
      exists sigma. split; [exact Hm |].
      simpl. exists mid. auto.
  Qed.

End SeqSemantic.

(* ================================================================= *)
(** ** Semantic Lemmas — Star / Iteration                              *)
(* ================================================================= *)

Section StarSemantic.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** Outcomes of Cⁿ are a subset of outcomes of C⋆,
      lifted to collecting semantics. *)
  Lemma collect_iter_subset_star (C : ol_prog Atom) (n : nat)
      (m : PSet Sigma) :
    forall tau,
      In _ (collect (ol_denote atom_den (ol_iter C n)) m) tau ->
      In _ (collect (ol_denote atom_den (OLStar C)) m) tau.
  Proof.
    intros tau Hin.
    unfold collect, pset_bind, In in *.
    destruct Hin as [sigma [Hm Hiter]].
    exists sigma. split; [exact Hm |].
    apply iter_included_in_star with (n := n). exact Hiter.
  Qed.

  (** Characterization: [τ ∈ collect(⟦C⋆⟧, m)] iff
      [∃n, τ ∈ collect(⟦Cⁿ⟧, m)]. *)
  Lemma collect_star_iff_iter (C : ol_prog Atom) (m : PSet Sigma)
      (tau : Sigma) :
    In _ (collect (ol_denote atom_den (OLStar C)) m) tau <->
    exists n, In _ (collect (ol_denote atom_den (ol_iter C n)) m) tau.
  Proof.
    unfold collect, pset_bind, In. split.
    - intros [sigma [Hm Hstar]].
      simpl in Hstar.
      apply star_is_union_of_iters in Hstar.
      destruct Hstar as [n Hn].
      exists n, sigma. auto.
    - intros [n [sigma [Hm Hn]]].
      exists sigma. split; [exact Hm |].
      apply iter_included_in_star with (n := n). exact Hn.
  Qed.

  (** Set-level equality: [collect(⟦C⋆⟧, m)] is the "countable union"
      over all finite iteration collectings. *)
  Lemma collect_star_eq_iter_union (C : ol_prog Atom) (m : PSet Sigma) :
    collect (ol_denote atom_den (OLStar C)) m =
      (fun tau => exists n,
        In _ (collect (ol_denote atom_den (ol_iter C n)) m) tau).
  Proof.
    apply ensemble_ext. intro tau.
    apply collect_star_iff_iter.
  Qed.

  (** Star and its fixed-point unfolding have identical collecting
      semantics: [collect(⟦C⋆⟧, m) = collect(⟦𝟏 + C;C⋆⟧, m)]. *)
  Lemma collect_star_unfold_eq (C : ol_prog Atom) (m : PSet Sigma) :
    collect (ol_denote atom_den (OLStar C)) m =
      collect (ol_denote atom_den (OLPlus OLOne (OLSeq C (OLStar C)))) m.
  Proof.
    unfold collect. apply ensemble_ext. intro tau.
    unfold pset_bind, In. split;
      intros [sigma [Hm Hd]]; exists sigma; split; auto.
    - rewrite <- denote_star_unfold. exact Hd.
    - rewrite denote_star_unfold. exact Hd.
  Qed.

End StarSemantic.

(* ================================================================= *)
(** ** Plus Rule                                                       *)
(* ================================================================= *)

Section PlusRule.

  Context {Sigma Atom : Type}.
  Variable atom_sat : PSet Sigma -> Atom -> Prop.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** **PLUS**: The nondeterministic choice rule.

      If [⊨ ⟨φ⟩ C₁ ⟨ψ₁⟩] and [⊨ ⟨φ⟩ C₂ ⟨ψ₂⟩],
      then [⊨ ⟨φ⟩ C₁+C₂ ⟨ψ₁ ⊕ ψ₂⟩].

      The key insight: [⟦C₁+C₂⟧†(m) = ⟦C₁⟧†(m) ∪ ⟦C₂⟧†(m)],
      and since [⊕] is interpreted as [∪] (the PCM operation),
      the two collecting results serve as witnesses. *)

  Theorem ol_plus (C1 C2 : ol_prog Atom)
      (phi psi1 psi2 : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den C1) phi psi1 ->
    ol_valid atom_sat (ol_denote atom_den C2) phi psi2 ->
    ol_valid atom_sat (ol_denote atom_den (OLPlus C1 C2))
            phi (BiOPlus psi1 psi2).
  Proof.
    intros H1 H2 m Hpre.
    simpl.
    exists (collect (ol_denote atom_den C1) m),
           (collect (ol_denote atom_den C2) m).
    split.
    - symmetry. apply collect_denote_plus.
    - split.
      + apply H1. exact Hpre.
      + apply H2. exact Hpre.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Derived: under-approximate Plus                              *)
  (* --------------------------------------------------------------- *)

  (** Under-approximate Plus: if each branch under-approximately
      satisfies its postcondition, so does the choice.

      The proof first applies the exact Plus rule to get
      [(ψ₁ ⊕ ⊤) ⊕ (ψ₂ ⊕ ⊤)], then rearranges the four
      PCM components via the interchange law to obtain
      [(ψ₁ ⊕ ψ₂) ⊕ ⊤]. *)
  Theorem ol_plus_under (C1 C2 : ol_prog Atom)
      (phi psi1 psi2 : bi_formula Atom) :
    ol_valid_under atom_sat (ol_denote atom_den C1) phi psi1 ->
    ol_valid_under atom_sat (ol_denote atom_den C2) phi psi2 ->
    ol_valid_under atom_sat (ol_denote atom_den (OLPlus C1 C2))
            phi (BiOPlus psi1 psi2).
  Proof.
    intros H1 H2.
    unfold ol_valid_under in *.
    apply ol_valid_post_weaken with
      (psi := BiOPlus (BiOPlus psi1 BiTop) (BiOPlus psi2 BiTop)).
    - apply ol_plus; assumption.
    - intros S HS.
      simpl in HS.
      destruct HS as [m1 [m2 [Heq [Hm1 Hm2]]]].
      destruct Hm1 as [a1 [b1 [Hab1 [Ha1 _]]]].
      destruct Hm2 as [a2 [b2 [Hab2 [Ha2 _]]]].
      simpl.
      exists (pset_union a1 a2), (pset_union b1 b2).
      split.
      + rewrite pset_union_interchange.
        rewrite Hab1. rewrite Hab2. exact Heq.
      + split.
        * exists a1, a2. split; [reflexivity |]. auto.
        * exact I.
  Qed.

End PlusRule.

(* ================================================================= *)
(** ** Induction Rules                                                 *)
(* ================================================================= *)

Section InductionRules.

  Context {Sigma Atom : Type}.
  Variable atom_sat : PSet Sigma -> Atom -> Prop.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (* --------------------------------------------------------------- *)
  (** *** Union Closure                                                *)
  (* --------------------------------------------------------------- *)

  (** A BI formula [ψ] is *countably union-closed* if, whenever
      every member of a nat-indexed family satisfies [ψ], so does
      their union.  This is the side-condition needed for the full
      Induction rule. *)

  Definition countable_union_closed
      (psi : bi_formula Atom) : Prop :=
    forall (f : nat -> PSet Sigma),
      (forall n, bi_sat atom_sat (f n) psi) ->
      bi_sat atom_sat
        (fun tau => exists n, In _ (f n) tau)
        psi.

  (* --------------------------------------------------------------- *)
  (** *** Star from Unfolding                                          *)
  (* --------------------------------------------------------------- *)

  (** Validity of C⋆ follows from validity of its unfolding
      [𝟏 + C;C⋆], since they have the same denotation. *)

  Theorem ol_star_unfold (C : ol_prog Atom)
      (phi psi : bi_formula Atom) :
    ol_valid atom_sat
      (ol_denote atom_den (OLPlus OLOne (OLSeq C (OLStar C))))
      phi psi ->
    ol_valid atom_sat (ol_denote atom_den (OLStar C)) phi psi.
  Proof.
    apply ol_valid_denote_ext.
    intro sigma. symmetry. apply denote_star_unfold.
  Qed.

  (** Conversely, validity of the unfolding follows from C⋆. *)

  Theorem ol_star_unfold_rev (C : ol_prog Atom)
      (phi psi : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den (OLStar C)) phi psi ->
    ol_valid atom_sat
      (ol_denote atom_den (OLPlus OLOne (OLSeq C (OLStar C))))
      phi psi.
  Proof.
    apply ol_valid_denote_ext.
    intro sigma. apply denote_star_unfold.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Under-Approximate Induction from a Single Iteration          *)
  (* --------------------------------------------------------------- *)

  (** If some finite iteration Cⁿ satisfies postcondition ψ, then
      C⋆ under-approximately satisfies ψ.  Intuitively: the outcomes
      of Cⁿ are a subset of C⋆'s outcomes; we split C⋆'s outcomes
      into the Cⁿ part (satisfying ψ) and the rest (satisfying ⊤). *)

  Theorem ol_induction_iter (C : ol_prog Atom) (n : nat)
      (phi psi : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den (ol_iter C n)) phi psi ->
    ol_valid_under atom_sat (ol_denote atom_den (OLStar C)) phi psi.
  Proof.
    intros Hiter m Hpre.
    simpl.
    exists (collect (ol_denote atom_den (ol_iter C n)) m),
           (collect (ol_denote atom_den (OLStar C)) m).
    split.
    - apply pset_union_incl_r.
      intros tau Hin.
      apply collect_iter_subset_star with (n := n). exact Hin.
    - split.
      + apply Hiter. exact Hpre.
      + exact I.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Full Induction with Union Closure                            *)
  (* --------------------------------------------------------------- *)

  (** **INDUCTION**: If for every n, ⊨ ⟨φ⟩ Cⁿ ⟨ψ⟩, and ψ is
      countably union-closed, then ⊨ ⟨φ⟩ C⋆ ⟨ψ⟩.

      This uses the fact that [collect(⟦C⋆⟧, m) = ⋃ₙ collect(⟦Cⁿ⟧, m)]
      (by [collect_star_eq_iter_union]) and the closure property. *)

  Theorem ol_induction (C : ol_prog Atom)
      (phi psi : bi_formula Atom) :
    (forall n, ol_valid atom_sat (ol_denote atom_den (ol_iter C n))
                 phi psi) ->
    countable_union_closed psi ->
    ol_valid atom_sat (ol_denote atom_den (OLStar C)) phi psi.
  Proof.
    intros Hall Hclosed m Hpre.
    rewrite collect_star_eq_iter_union.
    apply Hclosed.
    intro n. apply Hall. exact Hpre.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Step-Invariant for Iterations                                *)
  (* --------------------------------------------------------------- *)

  (** If φ is a one-step invariant for C (i.e., [⊨ ⟨φ⟩ C ⟨φ⟩]),
      then φ is an invariant for every finite iteration Cⁿ. *)

  Lemma ol_valid_iter_invariant (C : ol_prog Atom)
      (phi : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    forall n, ol_valid atom_sat (ol_denote atom_den (ol_iter C n))
                phi phi.
  Proof.
    intros Hstep n. induction n as [| k IH].
    - (* n = 0: C⁰ = 𝟏, collecting is identity *)
      intros m Hpre.
      assert (Heq : collect (ol_denote atom_den (ol_iter C 0)) m = m).
      { unfold collect. simpl. apply pset_bind_ret_r. }
      rewrite Heq. exact Hpre.
    - (* n = S k: C^(k+1) = C; Cᵏ *)
      intros m Hpre.
      assert (Heq : collect (ol_denote atom_den (ol_iter C (S k))) m =
                    collect (ol_denote atom_den (ol_iter C k))
                            (collect (ol_denote atom_den C) m)).
      { apply collect_seq. }
      rewrite Heq.
      apply IH. apply Hstep. exact Hpre.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Star Invariant (combining step-invariant + induction)        *)
  (* --------------------------------------------------------------- *)

  (** If φ is a one-step invariant for C and countably union-closed,
      then φ is an invariant for C⋆. *)

  Theorem ol_star_invariant (C : ol_prog Atom)
      (phi : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    countable_union_closed phi ->
    ol_valid atom_sat (ol_denote atom_den (OLStar C)) phi phi.
  Proof.
    intros Hstep Hclosed.
    apply ol_induction; [| exact Hclosed].
    apply ol_valid_iter_invariant. exact Hstep.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Under-Approximate Star Invariant (no closure needed)         *)
  (* --------------------------------------------------------------- *)

  (** If φ is a one-step invariant, then ⊨↓ ⟨φ⟩ C⋆ ⟨φ⟩.
      This follows immediately since C⁰ = 𝟏 preserves φ. *)

  Theorem ol_star_invariant_under (C : ol_prog Atom)
      (phi : bi_formula Atom) :
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    ol_valid_under atom_sat (ol_denote atom_den (OLStar C)) phi phi.
  Proof.
    intro Hstep.
    apply ol_induction_iter with (n := 0).
    apply ol_valid_iter_invariant with (n := 0) in Hstep.
    exact Hstep.
  Qed.

End InductionRules.

Arguments countable_union_closed {Sigma Atom} _ _.

(* ================================================================= *)
(** ** nd_atom_sat: Countable Union Closure for Atoms                  *)
(* ================================================================= *)

Section NDAtomClosure.

  Context {Sigma : Type}.

  (** Atomic assertions via [nd_atom_sat] are countably union-closed.
      If every Sₙ satisfies P (non-empty, all elements satisfy P),
      then their countable union also satisfies P. *)

  Lemma nd_atom_countable_union_closed (P : Sigma -> Prop) :
    countable_union_closed (@nd_atom_sat Sigma) (BiAtom P).
  Proof.
    intros f Hall.
    simpl. simpl in Hall.
    split.
    - (* Non-emptiness: use the 0-th family member *)
      destruct (Hall 0) as [[sigma0 Hin0] _].
      exists sigma0. exists 0. exact Hin0.
    - (* Universal property *)
      intros sigma [n Hin].
      destruct (Hall n) as [_ Hforall].
      apply Hforall. exact Hin.
  Qed.

  (** Corollary: For atoms, the full star invariant holds without
      any closure hypothesis. *)

  Corollary nd_star_invariant_atom
      (atom_den : (Sigma -> Prop) -> Sigma -> PSet Sigma)
      (C : ol_prog (Sigma -> Prop)) (P : Sigma -> Prop) :
    ol_valid nd_atom_sat (ol_denote atom_den C) (BiAtom P) (BiAtom P) ->
    ol_valid nd_atom_sat (ol_denote atom_den (OLStar C))
             (BiAtom P) (BiAtom P).
  Proof.
    intro Hstep.
    apply ol_star_invariant.
    - exact Hstep.
    - apply nd_atom_countable_union_closed.
  Qed.

End NDAtomClosure.
