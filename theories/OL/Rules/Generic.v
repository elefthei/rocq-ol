(** * OL/Rules/Generic.v — Generic Proof Rules for Outcome Logic

    Proves soundness of the 9 generic proof rules from Figure 5 (top
    section) of the Outcome Logic paper.  These rules are valid for
    ALL OL instances — they depend only on the PCM structure and BI
    satisfaction, not on the specific monad or execution model.

    Rules proved:
    - [ol_zero]        — ⊨ ⟨φ⟩ 𝟎 ⟨⊤⊕⟩
    - [ol_one]         — ⊨ ⟨φ⟩ 𝟏 ⟨φ⟩
    - [ol_seq]         — ⊨ ⟨φ⟩ C₁ ⟨ψ⟩ → ⊨ ⟨ψ⟩ C₂ ⟨θ⟩ → ⊨ ⟨φ⟩ C₁;C₂ ⟨θ⟩
    - [ol_for]         — ⊨ ⟨φ⟩ C ⟨φ⟩ → ⊨ ⟨φ⟩ Cⁿ ⟨φ⟩
    - [ol_split]       — ⊨ ⟨φ₁⟩ C ⟨ψ₁⟩ → ⊨ ⟨φ₂⟩ C ⟨ψ₂⟩ → ⊨ ⟨φ₁⊕φ₂⟩ C ⟨ψ₁⊕ψ₂⟩
    - [ol_consequence] — φ'⊨φ → ⊨ ⟨φ⟩ C ⟨ψ⟩ → ψ⊨ψ' → ⊨ ⟨φ'⟩ C ⟨ψ'⟩
    - [ol_empty]       — ⊨ ⟨⊤⊕⟩ C ⟨⊤⊕⟩
    - [ol_true]        — ⊨ ⟨φ⟩ C ⟨⊤⟩
    - [ol_false]       — ⊨ ⟨⊥⟩ C ⟨ψ⟩

    Under-approximate and partial-correctness derived forms are also
    proved for each rule.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 4, Figure 5 *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang Triple.

(* ================================================================= *)
(** ** Section Context                                                 *)
(* ================================================================= *)

(** All rules are parametric over:
    - [Sigma]    — the state type
    - [Atom]     — the assertion atom type
    - [CAtom]    — the command atom type
    - [atom_sat] — BI atomic satisfaction for [PSet Sigma]
    - [atom_den] — atomic command denotation *)

Section GenericRules.

  Context {Sigma : Type}.
  Context {Atom : Type}.
  Context {CAtom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).
  Context (atom_den : CAtom -> Sigma -> PSet Sigma).

  (** Convenience: the denotation of a program *)
  Local Notation "'⟦' C '⟧'" := (ol_denote atom_den C)
    (at level 0, C at level 99).

  (** Convenience: OL triple validity for a program *)
  Local Notation "'⊨' '⟨' phi '⟩' C '⟨' psi '⟩'" :=
    (ol_valid atom_sat (ol_denote atom_den C) phi psi)
    (at level 70, phi at level 99, C at level 99, psi at level 99).

  (* ================================================================= *)
  (** ** Rule 1: Zero — ⊨ ⟨φ⟩ 𝟎 ⟨⊤⊕⟩                                 *)
  (* ================================================================= *)

  (** [𝟎] aborts: [⟦𝟎⟧(σ) = ∅] for all [σ], so [collect(⟦𝟎⟧, m) = ∅]
      for any [m].  The empty set is the PCM identity, so [∅ ⊨ ⊤⊕]. *)

  Theorem ol_zero (phi : bi_formula Atom) :
    ⊨ ⟨ phi ⟩ (@OLZero CAtom) ⟨ BiEmpty ⟩.
  Proof.
    intros m _.
    simpl.
    apply collect_abort.
  Qed.

  (* ================================================================= *)
  (** ** Rule 2: One — ⊨ ⟨φ⟩ 𝟏 ⟨φ⟩                                   *)
  (* ================================================================= *)

  (** [𝟏] is skip: [⟦𝟏⟧(σ) = {σ}], so [collect(⟦𝟏⟧, m) = m].
      The postcondition is the same as the precondition. *)

  Theorem ol_one (phi : bi_formula Atom) :
    ⊨ ⟨ phi ⟩ (@OLOne CAtom) ⟨ phi ⟩.
  Proof.
    intros m Hpre.
    unfold ol_valid, collect. simpl.
    rewrite pset_bind_ret_r.
    exact Hpre.
  Qed.

  (* ================================================================= *)
  (** ** Rule 3: Seq — Sequential Composition                          *)
  (* ================================================================= *)

  (** If [⊨ ⟨φ⟩ C₁ ⟨ψ⟩] and [⊨ ⟨ψ⟩ C₂ ⟨θ⟩] then
      [⊨ ⟨φ⟩ C₁;C₂ ⟨θ⟩].

      Proof sketch: [collect(⟦C₁;C₂⟧, m) = collect(⟦C₂⟧, collect(⟦C₁⟧, m))]
      by associativity of bind.  Apply [H1] to get [ψ] for the
      intermediate, then [H2] to get [θ]. *)

  Theorem ol_seq (phi psi theta : bi_formula Atom)
      (C1 C2 : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
    ⊨ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
    ⊨ ⟨ phi ⟩ (OLSeq C1 C2) ⟨ theta ⟩.
  Proof.
    intros H1 H2 m Hpre.
    unfold ol_valid, collect in *.
    simpl.
    (* collect(⟦C₁;C₂⟧, m) = bind(m, λσ. bind(⟦C₁⟧(σ), ⟦C₂⟧))
       = bind(bind(m, ⟦C₁⟧), ⟦C₂⟧)   by associativity
       = collect(⟦C₂⟧, collect(⟦C₁⟧, m)) *)
    assert (Hassoc :
      pset_bind m (fun sigma => pset_bind (⟦ C1 ⟧ sigma) ⟦ C2 ⟧) =
      pset_bind (pset_bind m ⟦ C1 ⟧) ⟦ C2 ⟧).
    { symmetry. apply pset_bind_assoc. }
    rewrite Hassoc.
    apply H2.
    apply H1.
    exact Hpre.
  Qed.

  (* ================================================================= *)
  (** ** Rule 4: For — Bounded Iteration                               *)
  (* ================================================================= *)

  (** If [⊨ ⟨φ⟩ C ⟨φ⟩] (an invariant) then [⊨ ⟨φ⟩ Cⁿ ⟨φ⟩]
      for any [n].  This is the bounded iteration rule from Figure 5. *)

  Theorem ol_for (phi : bi_formula Atom)
      (C : ol_prog CAtom) (n : nat) :
    ⊨ ⟨ phi ⟩ C ⟨ phi ⟩ ->
    ⊨ ⟨ phi ⟩ (ol_for n C) ⟨ phi ⟩.
  Proof.
    intro Hinv.
    unfold ol_for.
    induction n as [| k IH].
    - (* n = 0: ol_iter C 0 = OLOne, so this is ol_one *)
      simpl. apply ol_one.
    - (* n = S k: ol_iter C (S k) = OLSeq C (ol_iter C k) *)
      simpl.
      apply ol_seq with (psi := phi).
      + exact Hinv.
      + exact IH.
  Qed.

  (* ================================================================= *)
  (** ** Rule 5: Split — Outcome Splitting                             *)
  (* ================================================================= *)

  (** The key OL-specific rule: if we can analyze [C] with two
      separate pre/postcondition pairs, we can join the results
      using outcome conjunction [⊕].

      [⊨ ⟨φ₁⟩ C ⟨ψ₁⟩] and [⊨ ⟨φ₂⟩ C ⟨ψ₂⟩] imply
      [⊨ ⟨φ₁ ⊕ φ₂⟩ C ⟨ψ₁ ⊕ ψ₂⟩].

      Proof: given [m ⊨ φ₁ ⊕ φ₂], there exist [m₁, m₂] with
      [m = m₁ ∪ m₂], [m₁ ⊨ φ₁], [m₂ ⊨ φ₂].  Since collecting
      distributes over union:
      [collect(⟦C⟧, m) = collect(⟦C⟧, m₁) ∪ collect(⟦C⟧, m₂)].
      Apply each hypothesis to get [ψ₁] and [ψ₂]. *)

  Theorem ol_split (phi1 phi2 psi1 psi2 : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
    ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
    ⊨ ⟨ BiOPlus phi1 phi2 ⟩ C ⟨ BiOPlus psi1 psi2 ⟩.
  Proof.
    intros H1 H2 m Hpre.
    (* [m ⊨ φ₁ ⊕ φ₂] gives us [m₁] and [m₂] *)
    simpl in Hpre.
    destruct Hpre as [m1 [m2 [Heq [Hphi1 Hphi2]]]].
    (* Show that collecting distributes over the PCM split *)
    simpl.
    exists (collect ⟦ C ⟧ m1), (collect ⟦ C ⟧ m2).
    split.
    - (* collect(⟦C⟧, m1 ∪ m2) = collect(⟦C⟧, m1) ∪ collect(⟦C⟧, m2) *)
      unfold collect.
      rewrite <- Heq.
      symmetry. apply pset_bind_union.
    - split.
      + apply H1. exact Hphi1.
      + apply H2. exact Hphi2.
  Qed.

  (* ================================================================= *)
  (** ** Rule 6: Consequence — Pre-Strengthening / Post-Weakening      *)
  (* ================================================================= *)

  (** The standard consequence rule:
      [φ' ⊨ φ] and [⊨ ⟨φ⟩ C ⟨ψ⟩] and [ψ ⊨ ψ'] imply
      [⊨ ⟨φ'⟩ C ⟨ψ'⟩]. *)

  Theorem ol_consequence (phi phi' psi psi' : bi_formula Atom)
      (C : ol_prog CAtom) :
    bi_entails atom_sat phi' phi ->
    ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
    bi_entails atom_sat psi psi' ->
    ⊨ ⟨ phi' ⟩ C ⟨ psi' ⟩.
  Proof.
    intros Hpre Hvalid Hpost.
    apply ol_valid_consequence with (phi := phi) (psi := psi);
      assumption.
  Qed.

  (* ================================================================= *)
  (** ** Rule 7: Empty — ⊨ ⟨⊤⊕⟩ C ⟨⊤⊕⟩                               *)
  (* ================================================================= *)

  (** The empty set of outcomes stays empty after any command.
      [⊤⊕] is satisfied only by the PCM unit (empty set),
      and collecting over the empty set yields the empty set. *)

  Theorem ol_empty (C : ol_prog CAtom) :
    ⊨ ⟨ BiEmpty ⟩ C ⟨ BiEmpty ⟩.
  Proof.
    intros m Hpre.
    simpl in Hpre. subst m.
    simpl.
    unfold collect.
    rewrite pset_bind_empty.
    reflexivity.
  Qed.

  (* ================================================================= *)
  (** ** Rule 8: True — ⊨ ⟨φ⟩ C ⟨⊤⟩                                  *)
  (* ================================================================= *)

  (** Any postcondition of [⊤] is trivially satisfied: [⊤] holds
      for every element.  This is the universal postcondition. *)

  Theorem ol_true (phi : bi_formula Atom) (C : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C ⟨ BiTop ⟩.
  Proof.
    intros m _.
    simpl. exact I.
  Qed.

  (* ================================================================= *)
  (** ** Rule 9: False — ⊨ ⟨⊥⟩ C ⟨ψ⟩                                 *)
  (* ================================================================= *)

  (** From a false precondition, any postcondition follows (ex falso).
      No [m] satisfies [⊥], so the universal quantification is vacuous. *)

  Theorem ol_false (psi : bi_formula Atom) (C : ol_prog CAtom) :
    ⊨ ⟨ BiBot ⟩ C ⟨ psi ⟩.
  Proof.
    intros m Hbot.
    simpl in Hbot. contradiction.
  Qed.

  (* ================================================================= *)
  (** ** Under-Approximate Derived Rules                                *)
  (* ================================================================= *)

  (** Each exact rule implies an under-approximate counterpart via
      the embedding [⊨ ⟨φ⟩ C ⟨ψ⟩ → ⊨↓ ⟨φ⟩ C ⟨ψ⟩]. *)

  Local Notation "'⊨↓' '⟨' phi '⟩' C '⟨' psi '⟩'" :=
    (ol_valid_under atom_sat (ol_denote atom_den C) phi psi)
    (at level 70, phi at level 99, C at level 99, psi at level 99).

  Theorem ol_zero_under (phi : bi_formula Atom) :
    ⊨↓ ⟨ phi ⟩ (@OLZero CAtom) ⟨ BiEmpty ⟩.
  Proof.
    apply ol_valid_implies_under. apply ol_zero.
  Qed.

  Theorem ol_one_under (phi : bi_formula Atom) :
    ⊨↓ ⟨ phi ⟩ (@OLOne CAtom) ⟨ phi ⟩.
  Proof.
    apply ol_valid_implies_under. apply ol_one.
  Qed.

  Theorem ol_seq_under (phi psi theta : bi_formula Atom)
      (C1 C2 : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
    ⊨ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
    ⊨↓ ⟨ phi ⟩ (OLSeq C1 C2) ⟨ theta ⟩.
  Proof.
    intros H1 H2.
    apply ol_valid_implies_under.
    exact (ol_seq phi psi theta C1 C2 H1 H2).
  Qed.

  Theorem ol_for_under (phi : bi_formula Atom)
      (C : ol_prog CAtom) (n : nat) :
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    ol_valid_under atom_sat (ol_denote atom_den (ol_iter C n)) phi phi.
  Proof.
    intro Hinv.
    apply ol_valid_implies_under.
    exact (ol_for phi C n Hinv).
  Qed.

  Theorem ol_split_under (phi1 phi2 psi1 psi2 : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
    ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
    ⊨↓ ⟨ BiOPlus phi1 phi2 ⟩ C ⟨ BiOPlus psi1 psi2 ⟩.
  Proof.
    intros H1 H2.
    apply ol_valid_implies_under.
    exact (ol_split phi1 phi2 psi1 psi2 C H1 H2).
  Qed.

  Theorem ol_consequence_under (phi phi' psi psi' : bi_formula Atom)
      (C : ol_prog CAtom) :
    bi_entails atom_sat phi' phi ->
    ⊨↓ ⟨ phi ⟩ C ⟨ psi ⟩ ->
    bi_entails atom_sat psi psi' ->
    ⊨↓ ⟨ phi' ⟩ C ⟨ psi' ⟩.
  Proof.
    intros Hpre Hvalid Hpost.
    unfold ol_valid_under in *.
    apply ol_valid_consequence with
      (phi := phi) (psi := BiOPlus psi BiTop).
    - exact Hpre.
    - exact Hvalid.
    - apply bi_oplus_mono.
      + exact Hpost.
      + apply bi_entails_refl.
  Qed.

  Theorem ol_empty_under (C : ol_prog CAtom) :
    ⊨↓ ⟨ BiEmpty ⟩ C ⟨ BiEmpty ⟩.
  Proof.
    apply ol_valid_implies_under. apply ol_empty.
  Qed.

  Theorem ol_true_under (phi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨↓ ⟨ phi ⟩ C ⟨ BiTop ⟩.
  Proof.
    apply ol_valid_implies_under. apply ol_true.
  Qed.

  Theorem ol_false_under (psi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨↓ ⟨ BiBot ⟩ C ⟨ psi ⟩.
  Proof.
    apply ol_valid_implies_under. apply ol_false.
  Qed.

  (* ================================================================= *)
  (** ** Partial-Correctness Derived Rules                              *)
  (* ================================================================= *)

  Local Notation "'⊨pc' '⟨' phi '⟩' C '⟨' psi '⟩'" :=
    (ol_valid_pc atom_sat (ol_denote atom_den C) phi psi)
    (at level 70, phi at level 99, C at level 99, psi at level 99).

  Theorem ol_zero_pc (phi : bi_formula Atom) :
    ⊨pc ⟨ phi ⟩ (@OLZero CAtom) ⟨ BiEmpty ⟩.
  Proof.
    apply ol_valid_implies_pc. apply ol_zero.
  Qed.

  Theorem ol_one_pc (phi : bi_formula Atom) :
    ⊨pc ⟨ phi ⟩ (@OLOne CAtom) ⟨ phi ⟩.
  Proof.
    apply ol_valid_implies_pc. apply ol_one.
  Qed.

  Theorem ol_seq_pc (phi psi theta : bi_formula Atom)
      (C1 C2 : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C1 ⟨ psi ⟩ ->
    ⊨ ⟨ psi ⟩ C2 ⟨ theta ⟩ ->
    ⊨pc ⟨ phi ⟩ (OLSeq C1 C2) ⟨ theta ⟩.
  Proof.
    intros H1 H2.
    apply ol_valid_implies_pc.
    exact (ol_seq phi psi theta C1 C2 H1 H2).
  Qed.

  Theorem ol_for_pc (phi : bi_formula Atom)
      (C : ol_prog CAtom) (n : nat) :
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    ol_valid_pc atom_sat (ol_denote atom_den (ol_iter C n)) phi phi.
  Proof.
    intro Hinv.
    apply ol_valid_implies_pc.
    exact (ol_for phi C n Hinv).
  Qed.

  Theorem ol_split_pc (phi1 phi2 psi1 psi2 : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
    ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
    ⊨pc ⟨ BiOPlus phi1 phi2 ⟩ C ⟨ BiOPlus psi1 psi2 ⟩.
  Proof.
    intros H1 H2.
    apply ol_valid_implies_pc.
    exact (ol_split phi1 phi2 psi1 psi2 C H1 H2).
  Qed.

  Theorem ol_consequence_pc (phi phi' psi psi' : bi_formula Atom)
      (C : ol_prog CAtom) :
    bi_entails atom_sat phi' phi ->
    ⊨pc ⟨ phi ⟩ C ⟨ psi ⟩ ->
    bi_entails atom_sat psi psi' ->
    ⊨pc ⟨ phi' ⟩ C ⟨ psi' ⟩.
  Proof.
    intros Hpre Hvalid Hpost.
    unfold ol_valid_pc in *.
    apply ol_valid_consequence with
      (phi := phi) (psi := BiOr psi BiEmpty).
    - exact Hpre.
    - exact Hvalid.
    - intros m [Hpsi | Hempty].
      + left. apply Hpost. exact Hpsi.
      + right. exact Hempty.
  Qed.

  Theorem ol_empty_pc (C : ol_prog CAtom) :
    ⊨pc ⟨ BiEmpty ⟩ C ⟨ BiEmpty ⟩.
  Proof.
    apply ol_valid_implies_pc. apply ol_empty.
  Qed.

  Theorem ol_true_pc (phi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨pc ⟨ phi ⟩ C ⟨ BiTop ⟩.
  Proof.
    apply ol_valid_implies_pc. apply ol_true.
  Qed.

  Theorem ol_false_pc (psi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨pc ⟨ BiBot ⟩ C ⟨ psi ⟩.
  Proof.
    apply ol_valid_implies_pc. apply ol_false.
  Qed.

  (* ================================================================= *)
  (** ** Additional Derived Rules                                       *)
  (* ================================================================= *)

  (** Split + Empty: splitting with the empty set on one side *)
  Theorem ol_split_empty_l (phi psi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
    ⊨ ⟨ BiOPlus BiEmpty phi ⟩ C ⟨ BiOPlus BiEmpty psi ⟩.
  Proof.
    intro H.
    apply ol_split.
    - apply ol_empty.
    - exact H.
  Qed.

  Theorem ol_split_empty_r (phi psi : bi_formula Atom)
      (C : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C ⟨ psi ⟩ ->
    ⊨ ⟨ BiOPlus phi BiEmpty ⟩ C ⟨ BiOPlus psi BiEmpty ⟩.
  Proof.
    intro H.
    apply ol_split.
    - exact H.
    - apply ol_empty.
  Qed.

  (** Seq chain: three-part sequential composition *)
  Theorem ol_seq3 (phi psi1 psi2 theta : bi_formula Atom)
      (C1 C2 C3 : ol_prog CAtom) :
    ⊨ ⟨ phi ⟩ C1 ⟨ psi1 ⟩ ->
    ⊨ ⟨ psi1 ⟩ C2 ⟨ psi2 ⟩ ->
    ⊨ ⟨ psi2 ⟩ C3 ⟨ theta ⟩ ->
    ⊨ ⟨ phi ⟩ (OLSeq C1 (OLSeq C2 C3)) ⟨ theta ⟩.
  Proof.
    intros H1 H2 H3.
    apply ol_seq with (psi := psi1).
    - exact H1.
    - apply ol_seq with (psi := psi2).
      + exact H2.
      + exact H3.
  Qed.

  (** For + Consequence: iterate with weakening *)
  Theorem ol_for_weaken (phi phi' : bi_formula Atom)
      (C : ol_prog CAtom) (n : nat) :
    bi_entails atom_sat phi' phi ->
    ol_valid atom_sat (ol_denote atom_den C) phi phi ->
    bi_entails atom_sat phi phi' ->
    ol_valid atom_sat (ol_denote atom_den (ol_iter C n)) phi' phi'.
  Proof.
    intros Hpre Hinv Hpost.
    apply ol_consequence with (phi := phi) (psi := phi).
    - exact Hpre.
    - apply ol_for. exact Hinv.
    - exact Hpost.
  Qed.

  (** Split is monotone in entailment (combines Split + Consequence) *)
  Theorem ol_split_consequence
      (phi1 phi1' phi2 phi2' psi1 psi1' psi2 psi2' : bi_formula Atom)
      (C : ol_prog CAtom) :
    bi_entails atom_sat phi1' phi1 ->
    bi_entails atom_sat phi2' phi2 ->
    ⊨ ⟨ phi1 ⟩ C ⟨ psi1 ⟩ ->
    ⊨ ⟨ phi2 ⟩ C ⟨ psi2 ⟩ ->
    bi_entails atom_sat psi1 psi1' ->
    bi_entails atom_sat psi2 psi2' ->
    ⊨ ⟨ BiOPlus phi1' phi2' ⟩ C ⟨ BiOPlus psi1' psi2' ⟩.
  Proof.
    intros Hpre1 Hpre2 H1 H2 Hpost1 Hpost2.
    apply ol_split.
    - apply ol_consequence with (phi := phi1) (psi := psi1);
        assumption.
    - apply ol_consequence with (phi := phi2) (psi := psi2);
        assumption.
  Qed.

End GenericRules.

(* ================================================================= *)
(** ** Tactic-Friendly Wrappers                                       *)
(* ================================================================= *)

(** These versions use [eapply]-friendly signatures so intermediate
    assertions can be left as existential variables during proof. *)

Section TacticFriendly.

  Context {Sigma Atom CAtom : Type}.
  Context (atom_sat : PSet Sigma -> Atom -> Prop).
  Context (atom_den : CAtom -> Sigma -> PSet Sigma).

  Lemma ol_seq_evar (phi psi theta : bi_formula Atom)
      (C1 C2 : ol_prog CAtom) :
    ol_valid atom_sat (ol_denote atom_den C1) phi psi ->
    ol_valid atom_sat (ol_denote atom_den C2) psi theta ->
    ol_valid atom_sat (ol_denote atom_den (OLSeq C1 C2)) phi theta.
  Proof.
    apply ol_seq.
  Qed.

End TacticFriendly.
