(** * OL/Triple.v — Outcome Logic Triple Validity

    Defines the central program logic predicates for Outcome Logic:
    - [ol_valid]       — full OL triple: ⊨ ⟨φ⟩ C ⟨ψ⟩
    - [ol_valid_under]  — under-approximate triple: ⊨↓ ⟨φ⟩ C ⟨ψ⟩
    - [ol_valid_pc]     — partial correctness triple: ⊨_pc ⟨φ⟩ C ⟨ψ⟩

    An OL triple [⊨ ⟨φ⟩ C ⟨ψ⟩] asserts: for every set of states [m]
    satisfying the precondition [φ], the collected outcomes
    [C†(m) = ⋃{⟦C⟧(σ) | σ ∈ m}] satisfy the postcondition [ψ].

    The under-approximate form [⊨↓ ⟨φ⟩ C ⟨ψ⟩] weakens the postcondition
    to [ψ ⊕ ⊤], allowing extra uncharacterized outcomes.

    The partial correctness form [⊨_pc ⟨φ⟩ C ⟨ψ⟩] uses postcondition
    [ψ ∨ ⊤⊕], allowing the program to produce no outcomes (diverge/abort).

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Sections 3–4 *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang.

(* ================================================================= *)
(** ** OL Triple Validity                                              *)
(* ================================================================= *)

(** [ol_valid atom_sat denote φ ψ] holds when, for every outcome set
    [m] satisfying the precondition [φ] under the powerset PCM, the
    collecting extension [collect denote m] satisfies the postcondition [ψ].

    Parameters:
    - [Sigma]    — the state type
    - [Atom]     — the atomic assertion type
    - [atom_sat] — satisfaction of atomic assertions over [PSet Sigma]
    - [denote]   — per-state denotation function [Σ → PSet Σ]
    - [phi, psi] — pre- and postcondition BI formulas

    The PCM on [PSet Sigma] is provided by the [PCM_PSet] instance
    (set union / empty set) from [Monad.v]. *)

Definition ol_valid {Sigma Atom : Type}
    (atom_sat : PSet Sigma -> Atom -> Prop)
    (denote : Sigma -> PSet Sigma)
    (phi psi : bi_formula Atom) : Prop :=
  forall (m : PSet Sigma),
    bi_sat atom_sat m phi ->
    bi_sat atom_sat (collect denote m) psi.

(* ================================================================= *)
(** ** Under-Approximate Triple                                        *)
(* ================================================================= *)

(** [ol_valid_under atom_sat denote φ ψ] is the under-approximate form:
    [⊨↓ ⟨φ⟩ C ⟨ψ⟩  ≜  ⊨ ⟨φ⟩ C ⟨ψ ⊕ ⊤⟩]

    This weakens the postcondition by allowing arbitrary additional
    outcomes beyond those characterized by [ψ].  This is the key form
    for incorrectness / reachability reasoning: it asserts that *some*
    outcomes satisfy [ψ], without constraining the rest. *)

Definition ol_valid_under {Sigma Atom : Type}
    (atom_sat : PSet Sigma -> Atom -> Prop)
    (denote : Sigma -> PSet Sigma)
    (phi psi : bi_formula Atom) : Prop :=
  ol_valid atom_sat denote phi (BiOPlus psi BiTop).

(* ================================================================= *)
(** ** Partial Correctness Triple                                      *)
(* ================================================================= *)

(** [ol_valid_pc atom_sat denote φ ψ] is the partial correctness form:
    [⊨_pc ⟨φ⟩ C ⟨ψ⟩  ≜  ⊨ ⟨φ⟩ C ⟨ψ ∨ ⊤⊕⟩]

    This allows the program to produce no outcomes (diverge or abort)
    as a valid behavior.  When [ψ = BiAtom P] and the execution model
    is deterministic, this collapses to standard Hoare partial
    correctness (Theorem 3.4 in the paper). *)

Definition ol_valid_pc {Sigma Atom : Type}
    (atom_sat : PSet Sigma -> Atom -> Prop)
    (denote : Sigma -> PSet Sigma)
    (phi psi : bi_formula Atom) : Prop :=
  ol_valid atom_sat denote phi (BiOr psi BiEmpty).

(* ================================================================= *)
(** ** Unfolding Lemmas                                                *)
(* ================================================================= *)

Section Unfolding.

  Context {Sigma Atom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).
  Context (denote : Sigma -> PSet Sigma).

  (** Direct characterization of [ol_valid]. *)
  Lemma ol_valid_unfold (phi psi : bi_formula Atom) :
    ol_valid atom_sat denote phi psi <->
    forall m, bi_sat atom_sat m phi ->
              bi_sat atom_sat (collect denote m) psi.
  Proof. unfold ol_valid. split; auto. Qed.

  (** Direct characterization of [ol_valid_under]. *)
  Lemma ol_valid_under_unfold (phi psi : bi_formula Atom) :
    ol_valid_under atom_sat denote phi psi <->
    forall m, bi_sat atom_sat m phi ->
              bi_sat atom_sat (collect denote m) (BiOPlus psi BiTop).
  Proof. unfold ol_valid_under, ol_valid. split; auto. Qed.

  (** Direct characterization of [ol_valid_pc]. *)
  Lemma ol_valid_pc_unfold (phi psi : bi_formula Atom) :
    ol_valid_pc atom_sat denote phi psi <->
    forall m, bi_sat atom_sat m phi ->
              bi_sat atom_sat (collect denote m) (BiOr psi BiEmpty).
  Proof. unfold ol_valid_pc, ol_valid. split; auto. Qed.

End Unfolding.

(* ================================================================= *)
(** ** Structural Properties                                           *)
(* ================================================================= *)

Section StructuralProperties.

  Context {Sigma Atom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).
  Context (denote : Sigma -> PSet Sigma).

  (* --------------------------------------------------------------- *)
  (** *** Exact validity implies under-approximate validity            *)
  (* --------------------------------------------------------------- *)

  (** If the exact triple holds, then the under-approximate triple holds. *)
  Lemma ol_valid_implies_under (phi psi : bi_formula Atom) :
    ol_valid atom_sat denote phi psi ->
    ol_valid_under atom_sat denote phi psi.
  Proof.
    intros Hvalid m Hpre.
    apply bi_weaken_oplus_top.
    apply Hvalid. exact Hpre.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Exact validity implies partial correctness                   *)
  (* --------------------------------------------------------------- *)

  (** If the exact triple holds, then the partial correctness triple holds. *)
  Lemma ol_valid_implies_pc (phi psi : bi_formula Atom) :
    ol_valid atom_sat denote phi psi ->
    ol_valid_pc atom_sat denote phi psi.
  Proof.
    intros Hvalid m Hpre.
    simpl. left.
    apply Hvalid. exact Hpre.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Consequence (pre-strengthening, post-weakening)              *)
  (* --------------------------------------------------------------- *)

  (** Postcondition weakening for [ol_valid]. *)
  Lemma ol_valid_post_weaken (phi psi psi' : bi_formula Atom) :
    ol_valid atom_sat denote phi psi ->
    bi_entails atom_sat psi psi' ->
    ol_valid atom_sat denote phi psi'.
  Proof.
    intros Hvalid Hent m Hpre.
    apply Hent. apply Hvalid. exact Hpre.
  Qed.

  (** Precondition strengthening for [ol_valid]. *)
  Lemma ol_valid_pre_strengthen (phi phi' psi : bi_formula Atom) :
    ol_valid atom_sat denote phi psi ->
    bi_entails atom_sat phi' phi ->
    ol_valid atom_sat denote phi' psi.
  Proof.
    intros Hvalid Hent m Hpre.
    apply Hvalid. apply Hent. exact Hpre.
  Qed.

  (** Full consequence rule. *)
  Lemma ol_valid_consequence (phi phi' psi psi' : bi_formula Atom) :
    bi_entails atom_sat phi' phi ->
    ol_valid atom_sat denote phi psi ->
    bi_entails atom_sat psi psi' ->
    ol_valid atom_sat denote phi' psi'.
  Proof.
    intros Hpre Hvalid Hpost.
    apply ol_valid_post_weaken with (psi := psi); [| exact Hpost].
    apply ol_valid_pre_strengthen with (phi := phi); [exact Hvalid | exact Hpre].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Consequence for derived forms                                *)
  (* --------------------------------------------------------------- *)

  (** Postcondition weakening for [ol_valid_under]. *)
  Lemma ol_valid_under_post_weaken (phi psi psi' : bi_formula Atom) :
    ol_valid_under atom_sat denote phi psi ->
    bi_entails atom_sat psi psi' ->
    ol_valid_under atom_sat denote phi psi'.
  Proof.
    unfold ol_valid_under.
    intros Hvalid Hent.
    apply ol_valid_post_weaken with (psi := BiOPlus psi BiTop).
    - exact Hvalid.
    - apply bi_oplus_mono.
      + exact Hent.
      + apply bi_entails_refl.
  Qed.

  (** Precondition strengthening for [ol_valid_under]. *)
  Lemma ol_valid_under_pre_strengthen (phi phi' psi : bi_formula Atom) :
    ol_valid_under atom_sat denote phi psi ->
    bi_entails atom_sat phi' phi ->
    ol_valid_under atom_sat denote phi' psi.
  Proof.
    unfold ol_valid_under.
    intros Hvalid Hent.
    apply ol_valid_pre_strengthen with (phi := phi); [exact Hvalid | exact Hent].
  Qed.

  (** Postcondition weakening for [ol_valid_pc]. *)
  Lemma ol_valid_pc_post_weaken (phi psi psi' : bi_formula Atom) :
    ol_valid_pc atom_sat denote phi psi ->
    bi_entails atom_sat psi psi' ->
    ol_valid_pc atom_sat denote phi psi'.
  Proof.
    unfold ol_valid_pc.
    intros Hvalid Hent.
    apply ol_valid_post_weaken with (psi := BiOr psi BiEmpty).
    - exact Hvalid.
    - intros m [Hpsi | Hempty].
      + left. apply Hent. exact Hpsi.
      + right. exact Hempty.
  Qed.

  (** Precondition strengthening for [ol_valid_pc]. *)
  Lemma ol_valid_pc_pre_strengthen (phi phi' psi : bi_formula Atom) :
    ol_valid_pc atom_sat denote phi psi ->
    bi_entails atom_sat phi' phi ->
    ol_valid_pc atom_sat denote phi' psi.
  Proof.
    unfold ol_valid_pc.
    intros Hvalid Hent.
    apply ol_valid_pre_strengthen with (phi := phi); [exact Hvalid | exact Hent].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Trivial triples                                              *)
  (* --------------------------------------------------------------- *)

  (** Any precondition maps to [⊤] — the trivially true postcondition. *)
  Lemma ol_valid_top (phi : bi_formula Atom) :
    ol_valid atom_sat denote phi BiTop.
  Proof.
    intros m _. simpl. exact I.
  Qed.

  (** From [⊥], anything follows — ex falso. *)
  Lemma ol_valid_bot (psi : bi_formula Atom) :
    ol_valid atom_sat denote BiBot psi.
  Proof.
    intros m Hbot. simpl in Hbot. contradiction.
  Qed.

  (** Under-approximate: top postcondition is trivially valid. *)
  Lemma ol_valid_under_top (phi : bi_formula Atom) :
    ol_valid_under atom_sat denote phi BiTop.
  Proof.
    apply ol_valid_implies_under.
    apply ol_valid_top.
  Qed.

  (** Under-approximate: ex falso. *)
  Lemma ol_valid_under_bot (psi : bi_formula Atom) :
    ol_valid_under atom_sat denote BiBot psi.
  Proof.
    apply ol_valid_implies_under.
    apply ol_valid_bot.
  Qed.

  (** Partial correctness: top postcondition is trivially valid. *)
  Lemma ol_valid_pc_top (phi : bi_formula Atom) :
    ol_valid_pc atom_sat denote phi BiTop.
  Proof.
    apply ol_valid_implies_pc.
    apply ol_valid_top.
  Qed.

  (** Partial correctness: ex falso. *)
  Lemma ol_valid_pc_bot (psi : bi_formula Atom) :
    ol_valid_pc atom_sat denote BiBot psi.
  Proof.
    apply ol_valid_implies_pc.
    apply ol_valid_bot.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Denotation-level equivalence                                 *)
  (* --------------------------------------------------------------- *)

  (** [ol_valid] respects extensional equality of denotations. *)
  Lemma ol_valid_denote_ext (denote' : Sigma -> PSet Sigma)
      (phi psi : bi_formula Atom) :
    (forall sigma, denote sigma = denote' sigma) ->
    ol_valid atom_sat denote phi psi ->
    ol_valid atom_sat denote' phi psi.
  Proof.
    intros Heq Hvalid m Hpre.
    assert (Hcol : collect denote m = collect denote' m).
    { unfold collect, pset_bind.
      apply ensemble_ext. intro tau. split;
        intros [sigma [Hin Hden]]; exists sigma; split; auto.
      - rewrite <- Heq. exact Hden.
      - rewrite Heq. exact Hden.
    }
    rewrite <- Hcol. apply Hvalid. exact Hpre.
  Qed.

End StructuralProperties.

(* ================================================================= *)
(** ** Relationships Between Triple Forms                              *)
(* ================================================================= *)

Section TripleRelationships.

  Context {Sigma Atom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).
  Context (denote : Sigma -> PSet Sigma).

  (** Under-approximate validity is weaker than partial correctness
      when the exact triple holds. *)
  Lemma ol_valid_pc_implies_under_with_empty (phi psi : bi_formula Atom) :
    ol_valid_pc atom_sat denote phi psi ->
    ol_valid_under atom_sat denote phi (BiOr psi BiEmpty).
  Proof.
    apply ol_valid_implies_under.
  Qed.

  (** Under-approximate form is monotone in the triple direction:
      if [⊨ ⟨φ⟩ C ⟨ψ⟩] then [⊨↓ ⟨φ'⟩ C ⟨ψ'⟩] whenever
      [φ' ⊨ φ] and [ψ ⊨ ψ']. *)
  Lemma ol_valid_under_from_exact (phi phi' psi psi' : bi_formula Atom) :
    bi_entails atom_sat phi' phi ->
    ol_valid atom_sat denote phi psi ->
    bi_entails atom_sat psi psi' ->
    ol_valid_under atom_sat denote phi' psi'.
  Proof.
    intros Hpre Hvalid Hpost.
    apply ol_valid_implies_under.
    apply ol_valid_consequence with (phi := phi) (psi := psi);
      assumption.
  Qed.

End TripleRelationships.

(* ================================================================= *)
(** ** Collecting Semantics Interaction                                *)
(* ================================================================= *)

Section CollectInteraction.

  Context {Sigma Atom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).

  (** If [denote] maps every state to the empty set (abort),
      then collecting over any [m] yields the empty set. *)
  Lemma collect_abort (m : PSet Sigma) :
    collect (fun _ : Sigma => pset_empty) m = pset_empty.
  Proof.
    unfold collect, pset_bind, pset_empty.
    apply ensemble_ext. intro tau. split.
    - intros [sigma [_ Hempty]]. inversion Hempty.
    - intro H. inversion H.
  Qed.

  (** If [denote] is the identity (skip), then collecting is
      the identity on sets. *)
  Lemma collect_skip (m : PSet Sigma) :
    collect pset_ret m = m.
  Proof.
    unfold collect. apply pset_bind_ret_r.
  Qed.

  (** Collecting preserves the empty set. *)
  Lemma collect_empty_set (denote : Sigma -> PSet Sigma) :
    collect denote pset_empty = pset_empty.
  Proof.
    apply collect_empty.
  Qed.

  (** Collecting distributes over set union. *)
  Lemma collect_union_set (denote : Sigma -> PSet Sigma)
      (m1 m2 : PSet Sigma) :
    collect denote (pset_union m1 m2) =
      pset_union (collect denote m1) (collect denote m2).
  Proof.
    apply collect_union.
  Qed.

End CollectInteraction.

(* ================================================================= *)
(** ** Notation                                                        *)
(* ================================================================= *)

Declare Scope ol_triple_scope.
Delimit Scope ol_triple_scope with ol.

(** We do not define triple notation here because it would require
    fixing the [atom_sat] and [denote] parameters.  Instead, each
    concrete instantiation (e.g., the nondeterministic powerset model
    with [nd_atom_sat]) should define its own notation in a local scope.

    Suggested pattern for instantiations:

    [Notation "⊨ ⟨ φ ⟩ C ⟨ ψ ⟩" :=
       (ol_valid my_atom_sat (ol_denote my_atom_den C) φ ψ) : my_scope.]

    [Notation "⊨↓ ⟨ φ ⟩ C ⟨ ψ ⟩" :=
       (ol_valid_under my_atom_sat (ol_denote my_atom_den C) φ ψ) : my_scope.]
*)
