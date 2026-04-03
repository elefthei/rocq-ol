(** * OL/Heap/Assertion.v — Separation Logic Assertions for Heaps

    Defines the heap model, separation logic assertion syntax,
    satisfaction relation, and structural lemmas needed to reason
    about heap-manipulating programs in Outcome Logic.

    Components:
    - [Heap]           — Heap as partial function [nat → option nat]
    - [heap_disjoint]  — Domain disjointness for two heaps
    - [heap_union]     — Disjoint union of heaps
    - [sl_assert]      — Deep-embedded SL formula syntax
    - [sl_sat]         — Satisfaction of SL assertions over a store and heap
    - SL notation      — Unicode notation scope [sl_scope]
    - Structural lemmas (∗ commutativity, associativity, emp identity, etc.)

    The heap model is purely functional (no alists) and independent of
    any particular imperative language definition.  The [err_assert]
    wrapper from [OL/Heap/Error.v] lifts these assertions to error-tagged
    states; this file provides the *underlying* assertion logic.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5 *)

From Stdlib Require Import Ensembles Classical_Prop PeanoNat.
From OL Require Import Monad Assertion.

(* ================================================================= *)
(** ** Heap and Store Model                                           *)
(* ================================================================= *)

(** A [Heap] is a partial function from addresses (nat) to values (nat).
    [None] means the address is unallocated. *)

Definition Heap  : Type := nat -> option nat.

(** The empty heap: no address is allocated. *)
Definition heap_empty : Heap := fun _ => None.

(** Singleton heap: [l ↦ v] and nothing else. *)
Definition heap_singleton (l v : nat) : Heap :=
  fun a => if Nat.eqb a l then Some v else None.

(* ================================================================= *)
(** ** Heap Disjointness                                              *)
(* ================================================================= *)

(** Two heaps are disjoint when their domains do not overlap:
    for every address [a], at most one of [h1 a] and [h2 a] is [Some]. *)
Definition heap_disjoint (h1 h2 : Heap) : Prop :=
  forall a, h1 a = None \/ h2 a = None.

(* ================================================================= *)
(** ** Heap Union                                                     *)
(* ================================================================= *)

(** Disjoint union of two heaps.  When the heaps are disjoint,
    [heap_union h1 h2] is the heap that contains all bindings from
    both.  When they overlap (which should not happen in well-formed
    separation logic derivations), the left binding wins. *)
Definition heap_union (h1 h2 : Heap) : Heap :=
  fun a =>
    match h1 a with
    | Some v => Some v
    | None   => h2 a
    end.

(* ================================================================= *)
(** ** Expression Type (Simplified)                                   *)
(* ================================================================= *)

(** For a standalone SL assertion logic, expressions are simply natural
    numbers (literal values).  When integrated with a concrete language
    such as HeapImp, these would be replaced with the language's
    expression type and evaluated against the store. *)

Definition SLVal := nat.

(* ================================================================= *)
(** ** SL Assertion Syntax                                            *)
(* ================================================================= *)

(** Deep-embedded separation logic formulas.  The assertion language
    is independent of the programming language and can be instantiated
    with HeapImp or any other heap-manipulating language.

    Connectives:
    - [SLEmp]         — emp (empty heap)
    - [SLPointsTo]    — e₁ ↦ e₂ (singleton heap)
    - [SLPointsAny]   — e ↦ − (allocated, any value)
    - [SLInvalid]     — e ↛ (not allocated / dangling)
    - [SLStar]        — p ∗ q (separating conjunction)
    - [SLWand]        — p −∗ q (separating implication / magic wand)
    - [SLPure]        — ⌜P⌝ (pure assertion, no heap footprint)
    - [SLAnd]         — p ∧ q
    - [SLOr]          — p ∨ q
    - [SLExists]      — ∃x. p(x)
    - [SLForall]      — ∀x. p(x)
    - [SLTrue]        — True (holds for any heap)
    - [SLFalse]       — False *)

Inductive sl_assert : Type :=
  | SLEmp                                     (* emp *)
  | SLPointsTo (e1 e2 : SLVal)               (* e₁ ↦ e₂ *)
  | SLPointsAny (e : SLVal)                  (* e ↦ − *)
  | SLInvalid (e : SLVal)                    (* e ↛ *)
  | SLStar (p q : sl_assert)                 (* p ∗ q *)
  | SLWand (p q : sl_assert)                 (* p −∗ q *)
  | SLPure (P : Prop)                        (* ⌜P⌝ *)
  | SLAnd (p q : sl_assert)                  (* p ∧ q *)
  | SLOr (p q : sl_assert)                   (* p ∨ q *)
  | SLExists (f : nat -> sl_assert)          (* ∃x. p(x) *)
  | SLForall (f : nat -> sl_assert)          (* ∀x. p(x) *)
  | SLTrue                                    (* True *)
  | SLFalse                                   (* False *)
  .

(* ================================================================= *)
(** ** SL Satisfaction Relation                                       *)
(* ================================================================= *)

(** [sl_sat h p] holds when heap [h] satisfies the assertion [p].

    Note: in this standalone model, stores are not threaded through
    the assertion logic — expressions are literal values.  When
    integrated with a language, one would add a store parameter and
    evaluate expressions against it.

    Key clauses:
    - [SLEmp]: the heap is empty
    - [SLPointsTo e1 e2]: the heap is exactly [{e1 ↦ e2}]
    - [SLStar p q]: the heap splits into disjoint parts
    - [SLWand p q]: for all disjoint extensions satisfying [p],
                    the combined heap satisfies [q]
    - [SLInvalid e]: address [e] is not allocated *)

Fixpoint sl_sat (h : Heap) (p : sl_assert) : Prop :=
  match p with
  | SLEmp =>
      h = heap_empty
  | SLPointsTo e1 e2 =>
      h = heap_singleton e1 e2
  | SLPointsAny e =>
      exists v, h = heap_singleton e v
  | SLInvalid e =>
      h e = None
  | SLStar p q =>
      exists h1 h2,
        heap_disjoint h1 h2 /\
        heap_union h1 h2 = h /\
        sl_sat h1 p /\ sl_sat h2 q
  | SLWand p q =>
      forall h',
        heap_disjoint h h' ->
        sl_sat h' p ->
        sl_sat (heap_union h h') q
  | SLPure P =>
      P /\ h = heap_empty
  | SLAnd p q =>
      sl_sat h p /\ sl_sat h q
  | SLOr p q =>
      sl_sat h p \/ sl_sat h q
  | SLExists f =>
      exists x, sl_sat h (f x)
  | SLForall f =>
      forall x, sl_sat h (f x)
  | SLTrue =>
      True
  | SLFalse =>
      False
  end.

(* ================================================================= *)
(** ** Heap Extensionality                                            *)
(* ================================================================= *)

(** Two heaps are equal when they agree on every address. *)
Axiom heap_ext : forall (h1 h2 : Heap),
  (forall a, h1 a = h2 a) -> h1 = h2.

(* ================================================================= *)
(** ** Heap Disjointness Lemmas                                      *)
(* ================================================================= *)

Section HeapDisjointLemmas.

  (** Disjointness is symmetric. *)
  Lemma heap_disjoint_sym (h1 h2 : Heap) :
    heap_disjoint h1 h2 -> heap_disjoint h2 h1.
  Proof.
    intros Hdisj a.
    destruct (Hdisj a) as [H | H]; [right | left]; exact H.
  Qed.

  (** The empty heap is disjoint from everything. *)
  Lemma heap_disjoint_empty_l (h : Heap) :
    heap_disjoint heap_empty h.
  Proof.
    intros a. left. reflexivity.
  Qed.

  Lemma heap_disjoint_empty_r (h : Heap) :
    heap_disjoint h heap_empty.
  Proof.
    intros a. right. reflexivity.
  Qed.

  (** If [h1] and [h2] are disjoint and [h1 a = Some v],
      then [h2 a = None]. *)
  Lemma heap_disjoint_some_l (h1 h2 : Heap) (a : nat) (v : nat) :
    heap_disjoint h1 h2 -> h1 a = Some v -> h2 a = None.
  Proof.
    intros Hdisj Hsome.
    destruct (Hdisj a) as [H | H].
    - rewrite Hsome in H. discriminate H.
    - exact H.
  Qed.

  Lemma heap_disjoint_some_r (h1 h2 : Heap) (a : nat) (v : nat) :
    heap_disjoint h1 h2 -> h2 a = Some v -> h1 a = None.
  Proof.
    intros Hdisj Hsome.
    destruct (Hdisj a) as [H | H].
    - exact H.
    - rewrite Hsome in H. discriminate H.
  Qed.

  (** Singleton heaps at different addresses are disjoint. *)
  Lemma heap_disjoint_singleton (l1 l2 v1 v2 : nat) :
    l1 <> l2 ->
    heap_disjoint (heap_singleton l1 v1) (heap_singleton l2 v2).
  Proof.
    intros Hneq a.
    unfold heap_singleton.
    destruct (Nat.eqb a l1) eqn:E1, (Nat.eqb a l2) eqn:E2.
    - apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2.
      subst. exfalso. apply Hneq. reflexivity.
    - right. reflexivity.
    - left. reflexivity.
    - left. reflexivity.
  Qed.

End HeapDisjointLemmas.

(* ================================================================= *)
(** ** Heap Union Lemmas                                              *)
(* ================================================================= *)

Section HeapUnionLemmas.

  (** Union with the empty heap (left identity). *)
  Lemma heap_union_empty_l (h : Heap) :
    heap_union heap_empty h = h.
  Proof.
    apply heap_ext. intro a.
    unfold heap_union, heap_empty.
    reflexivity.
  Qed.

  (** Union with the empty heap (right identity). *)
  Lemma heap_union_empty_r (h : Heap) :
    heap_union h heap_empty = h.
  Proof.
    apply heap_ext. intro a.
    unfold heap_union, heap_empty.
    destruct (h a); reflexivity.
  Qed.

  (** Disjoint union is commutative. *)
  Lemma heap_union_comm (h1 h2 : Heap) :
    heap_disjoint h1 h2 ->
    heap_union h1 h2 = heap_union h2 h1.
  Proof.
    intros Hdisj.
    apply heap_ext. intro a.
    unfold heap_union.
    destruct (Hdisj a) as [H1 | H2].
    - rewrite H1. destruct (h2 a); reflexivity.
    - rewrite H2. destruct (h1 a) eqn:E; reflexivity.
  Qed.

  (** Disjoint union is associative (when all three are pairwise disjoint). *)
  Lemma heap_union_assoc (h1 h2 h3 : Heap) :
    heap_disjoint h1 h2 ->
    heap_disjoint (heap_union h1 h2) h3 ->
    heap_union (heap_union h1 h2) h3 =
      heap_union h1 (heap_union h2 h3).
  Proof.
    intros Hdisj12 Hdisj12_3.
    apply heap_ext. intro a.
    unfold heap_union.
    destruct (h1 a) eqn:E1; reflexivity.
  Qed.

  (** [heap_union h1 h2] at an address in [h1] returns [h1]'s value. *)
  Lemma heap_union_l (h1 h2 : Heap) (a : nat) (v : nat) :
    h1 a = Some v -> heap_union h1 h2 a = Some v.
  Proof.
    intro H. unfold heap_union. rewrite H. reflexivity.
  Qed.

  (** [heap_union h1 h2] at an address not in [h1] returns [h2]'s value. *)
  Lemma heap_union_r (h1 h2 : Heap) (a : nat) :
    h1 a = None -> heap_union h1 h2 a = h2 a.
  Proof.
    intro H. unfold heap_union. rewrite H. reflexivity.
  Qed.

  (** Three-way disjointness: if h1⊥h2 and (h1∪h2)⊥h3, then h2⊥h3. *)
  Lemma heap_disjoint_union_l (h1 h2 h3 : Heap) :
    heap_disjoint h1 h2 ->
    heap_disjoint (heap_union h1 h2) h3 ->
    heap_disjoint h2 h3.
  Proof.
    intros Hdisj12 Hdisj_u3 a.
    destruct (Hdisj_u3 a) as [Hu | H3].
    - unfold heap_union in Hu.
      destruct (h1 a) eqn:E1.
      + discriminate Hu.
      + left. exact Hu.
    - right. exact H3.
  Qed.

  (** Three-way disjointness: if h1⊥h2 and (h1∪h2)⊥h3, then h1⊥h3. *)
  Lemma heap_disjoint_union_r (h1 h2 h3 : Heap) :
    heap_disjoint h1 h2 ->
    heap_disjoint (heap_union h1 h2) h3 ->
    heap_disjoint h1 h3.
  Proof.
    intros Hdisj12 Hdisj_u3 a.
    destruct (Hdisj12 a) as [H1 | H2].
    - left. exact H1.
    - destruct (Hdisj_u3 a) as [Hu | H3].
      + unfold heap_union in Hu.
        destruct (h1 a) eqn:E1.
        * discriminate Hu.
        * left. reflexivity.
      + right. exact H3.
  Qed.

  (** Re-association helper: if h1⊥h2 and (h1∪h2)⊥h3,
      then h1⊥(h2∪h3) and (h2∪h3) is disjoint from nothing new. *)
  Lemma heap_disjoint_union_reassoc (h1 h2 h3 : Heap) :
    heap_disjoint h1 h2 ->
    heap_disjoint (heap_union h1 h2) h3 ->
    heap_disjoint h1 (heap_union h2 h3).
  Proof.
    intros Hdisj12 Hdisj_u3 a.
    destruct (Hdisj12 a) as [H1 | H2].
    - left. exact H1.
    - destruct (Hdisj_u3 a) as [Hu | H3].
      + unfold heap_union in Hu.
        destruct (h1 a) eqn:E1.
        * discriminate Hu.
        * left. reflexivity.
      + right. unfold heap_union. rewrite H2. exact H3.
  Qed.

End HeapUnionLemmas.

(* ================================================================= *)
(** ** SL Satisfaction Lemmas                                         *)
(* ================================================================= *)

Section SLSatLemmas.

  (* --------------------------------------------------------------- *)
  (** *** Emp                                                          *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_emp (h : Heap) :
    sl_sat h SLEmp <-> h = heap_empty.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** PointsTo                                                     *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_pointsto (h : Heap) (l v : nat) :
    sl_sat h (SLPointsTo l v) <-> h = heap_singleton l v.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** PointsAny                                                    *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_pointsany (h : Heap) (l : nat) :
    sl_sat h (SLPointsAny l) <-> exists v, h = heap_singleton l v.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Invalid (dangling pointer)                                   *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_invalid (h : Heap) (l : nat) :
    sl_sat h (SLInvalid l) <-> h l = None.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Star (separating conjunction)                                *)
  (* --------------------------------------------------------------- *)

  (** [∗] is commutative *)
  Lemma sl_star_comm (p q : sl_assert) (h : Heap) :
    sl_sat h (SLStar p q) <-> sl_sat h (SLStar q p).
  Proof.
    simpl. split; intros [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
    - exists h2, h1.
      split; [apply heap_disjoint_sym; exact Hdisj |].
      split; [rewrite (heap_union_comm h2 h1 (heap_disjoint_sym h1 h2 Hdisj));
              exact Hunion |].
      split; [exact H2 | exact H1].
    - exists h2, h1.
      split; [apply heap_disjoint_sym; exact Hdisj |].
      split; [rewrite (heap_union_comm h2 h1 (heap_disjoint_sym h1 h2 Hdisj));
              exact Hunion |].
      split; [exact H2 | exact H1].
  Qed.

  (** [∗] is associative *)
  Lemma sl_star_assoc (p q r : sl_assert) (h : Heap) :
    sl_sat h (SLStar (SLStar p q) r) <->
    sl_sat h (SLStar p (SLStar q r)).
  Proof.
    simpl. split.
    - intros [h12 [h3 [Hdisj12_3 [Hunion12_3
               [[h1 [h2 [Hdisj12 [Hunion12 [Hp Hq]]]]] Hr]]]]].
      subst h12.
      exists h1, (heap_union h2 h3).
      split.
      + apply heap_disjoint_union_reassoc; assumption.
      + split.
        * rewrite <- heap_union_assoc; [exact Hunion12_3 | exact Hdisj12 | exact Hdisj12_3].
        * split.
          -- exact Hp.
          -- exists h2, h3.
             split; [eapply heap_disjoint_union_l; eassumption |].
             split; [reflexivity |].
             split; [exact Hq | exact Hr].
    - intros [h1 [h23 [Hdisj1_23 [Hunion1_23
               [Hp [h2 [h3 [Hdisj23 [Hunion23 [Hq Hr]]]]]]]]]].
      subst h23.
      assert (Hdisj12 : heap_disjoint h1 h2).
      { intros a.
        destruct (Hdisj1_23 a) as [H1 | H23].
        - left. exact H1.
        - unfold heap_union in H23.
          destruct (h2 a) eqn:E2.
          + discriminate H23.
          + right. reflexivity. }
      assert (Hdisj12_3 : heap_disjoint (heap_union h1 h2) h3).
      { intros a. unfold heap_union.
        destruct (h1 a) eqn:E1.
        - destruct (Hdisj1_23 a) as [H1' | H23].
          + rewrite E1 in H1'. discriminate H1'.
          + unfold heap_union in H23.
            destruct (h2 a) eqn:E2.
            * discriminate H23.
            * right. exact H23.
        - destruct (Hdisj23 a) as [H2 | H3].
          + rewrite H2. left. reflexivity.
          + right. exact H3. }
      exists (heap_union h1 h2), h3.
      split; [exact Hdisj12_3 |].
      split.
      + rewrite (heap_union_assoc h1 h2 h3 Hdisj12 Hdisj12_3).
        exact Hunion1_23.
      + split.
        * exists h1, h2.
          split; [exact Hdisj12 |].
          split; [reflexivity |].
          split; [exact Hp | exact Hq].
        * exact Hr.
  Qed.

  (** [emp] is the left identity for [∗] *)
  Lemma sl_star_emp_l (p : sl_assert) (h : Heap) :
    sl_sat h (SLStar SLEmp p) <-> sl_sat h p.
  Proof.
    simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [Hemp Hp]]]]].
      subst h1.
      rewrite heap_union_empty_l in Hunion.
      subst h. exact Hp.
    - intro Hp.
      exists heap_empty, h.
      split; [apply heap_disjoint_empty_l |].
      split; [apply heap_union_empty_l |].
      split; [reflexivity | exact Hp].
  Qed.

  (** [emp] is the right identity for [∗] *)
  Lemma sl_star_emp_r (p : sl_assert) (h : Heap) :
    sl_sat h (SLStar p SLEmp) <-> sl_sat h p.
  Proof.
    split.
    - intro H. apply sl_star_comm in H.
      apply sl_star_emp_l. exact H.
    - intro H. apply sl_star_comm.
      apply sl_star_emp_l. exact H.
  Qed.

  (** [∗] is monotone *)
  Lemma sl_star_mono (p1 q1 p2 q2 : sl_assert) :
    (forall h, sl_sat h p1 -> sl_sat h p2) ->
    (forall h, sl_sat h q1 -> sl_sat h q2) ->
    forall h, sl_sat h (SLStar p1 q1) -> sl_sat h (SLStar p2 q2).
  Proof.
    intros Hp Hq h [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
    exists h1, h2.
    split; [exact Hdisj |].
    split; [exact Hunion |].
    split; [apply Hp; exact H1 | apply Hq; exact H2].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Pure assertions                                              *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_pure (P : Prop) (h : Heap) :
    sl_sat h (SLPure P) <-> P /\ h = heap_empty.
  Proof. simpl. split; auto. Qed.

  (** Pure assertions absorbed by [∗]: [⌜P⌝ ∗ p ⟺ P ∧ p]
      (when the heap for [⌜P⌝] is empty) *)
  Lemma sl_star_pure_l (P : Prop) (p : sl_assert) (h : Heap) :
    sl_sat h (SLStar (SLPure P) p) <-> (P /\ sl_sat h p).
  Proof.
    simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [[HP Hempty] Hp]]]]].
      subst h1.
      rewrite heap_union_empty_l in Hunion.
      subst h. auto.
    - intros [HP Hp].
      exists heap_empty, h.
      split; [apply heap_disjoint_empty_l |].
      split; [apply heap_union_empty_l |].
      split; [split; [exact HP | reflexivity] | exact Hp].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** True / False                                                 *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_true (h : Heap) :
    sl_sat h SLTrue.
  Proof. exact I. Qed.

  Lemma sl_sat_false (h : Heap) :
    ~ sl_sat h SLFalse.
  Proof. intro H. exact H. Qed.

  (* --------------------------------------------------------------- *)
  (** *** And / Or                                                     *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_and (p q : sl_assert) (h : Heap) :
    sl_sat h (SLAnd p q) <-> sl_sat h p /\ sl_sat h q.
  Proof. simpl. split; auto. Qed.

  Lemma sl_sat_or (p q : sl_assert) (h : Heap) :
    sl_sat h (SLOr p q) <-> sl_sat h p \/ sl_sat h q.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Exists / Forall                                              *)
  (* --------------------------------------------------------------- *)

  Lemma sl_sat_exists (f : nat -> sl_assert) (h : Heap) :
    sl_sat h (SLExists f) <-> exists x, sl_sat h (f x).
  Proof. simpl. split; auto. Qed.

  Lemma sl_sat_forall (f : nat -> sl_assert) (h : Heap) :
    sl_sat h (SLForall f) <-> forall x, sl_sat h (f x).
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** PointsTo / Singleton heap properties                         *)
  (* --------------------------------------------------------------- *)

  (** A singleton heap is disjoint from another singleton at a
      different address. *)
  Lemma sl_pointsto_star_diff (l1 l2 v1 v2 : nat) (h : Heap) :
    l1 <> l2 ->
    sl_sat h (SLStar (SLPointsTo l1 v1) (SLPointsTo l2 v2)) <->
    h = heap_union (heap_singleton l1 v1) (heap_singleton l2 v2).
  Proof.
    intros Hneq. simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
      subst h1 h2. symmetry. exact Hunion.
    - intro Heq. subst h.
      exists (heap_singleton l1 v1), (heap_singleton l2 v2).
      split; [apply heap_disjoint_singleton; exact Hneq |].
      split; [reflexivity |].
      split; reflexivity.
  Qed.

  (** The singleton heap at [l] has [l] in its domain. *)
  Lemma heap_singleton_lookup (l v : nat) :
    heap_singleton l v l = Some v.
  Proof.
    unfold heap_singleton. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (** The singleton heap at [l] has [None] at other addresses. *)
  Lemma heap_singleton_other (l l' v : nat) :
    l <> l' -> heap_singleton l v l' = None.
  Proof.
    intro Hneq.
    unfold heap_singleton.
    destruct (Nat.eqb l' l) eqn:E.
    - apply Nat.eqb_eq in E. symmetry in E. contradiction.
    - reflexivity.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Invalid (dangling) properties                                *)
  (* --------------------------------------------------------------- *)

  (** [e ↛] holds for the empty heap *)
  Lemma sl_invalid_empty (e : nat) :
    sl_sat heap_empty (SLInvalid e).
  Proof. simpl. reflexivity. Qed.

  (** [l ↛] is incompatible with [l ↦ v] on the same heap *)
  Lemma sl_invalid_pointsto_contra (l v : nat) (h : Heap) :
    sl_sat h (SLPointsTo l v) -> ~ sl_sat h (SLInvalid l).
  Proof.
    simpl. intros Heq Hinv.
    subst h.
    rewrite heap_singleton_lookup in Hinv.
    discriminate Hinv.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Magic Wand (−∗)                                              *)
  (* --------------------------------------------------------------- *)

  (** Modus ponens for separating implication:
      [p ∗ (p −∗ q)] entails [q]. *)
  Lemma sl_wand_mp (p q : sl_assert) (h : Heap) :
    sl_sat h (SLStar p (SLWand p q)) -> sl_sat h q.
  Proof.
    simpl.
    intros [h1 [h2 [Hdisj [Hunion [Hp Hwand]]]]].
    subst h.
    rewrite (heap_union_comm h1 h2 Hdisj).
    apply Hwand.
    - apply heap_disjoint_sym. exact Hdisj.
    - exact Hp.
  Qed.

  (** Introduction rule for wand:
      if [p ∗ q] entails [r], then [q] entails [p −∗ r]. *)
  Lemma sl_wand_intro (p q r : sl_assert) :
    (forall h, sl_sat h (SLStar p q) -> sl_sat h r) ->
    forall h, sl_sat h q -> sl_sat h (SLWand p r).
  Proof.
    intros Hstar h Hq h' Hdisj Hp.
    apply Hstar.
    simpl.
    exists h', h.
    split; [apply heap_disjoint_sym; exact Hdisj |].
    split; [rewrite (heap_union_comm h' h (heap_disjoint_sym h h' Hdisj));
            reflexivity |].
    split; [exact Hp | exact Hq].
  Qed.

End SLSatLemmas.

(* ================================================================= *)
(** ** SL Entailment                                                  *)
(* ================================================================= *)

(** Semantic entailment for SL assertions: [p] entails [q] when
    every heap satisfying [p] also satisfies [q]. *)
Definition sl_entails (p q : sl_assert) : Prop :=
  forall h, sl_sat h p -> sl_sat h q.

Section SLEntailment.

  Lemma sl_entails_refl (p : sl_assert) :
    sl_entails p p.
  Proof. intros h H. exact H. Qed.

  Lemma sl_entails_trans (p q r : sl_assert) :
    sl_entails p q -> sl_entails q r -> sl_entails p r.
  Proof.
    intros H1 H2 h Hp. apply H2. apply H1. exact Hp.
  Qed.

  (** [emp] entails [True] *)
  Lemma sl_emp_entails_true : sl_entails SLEmp SLTrue.
  Proof. intros h _. exact I. Qed.

  (** [False] entails anything *)
  Lemma sl_false_entails (p : sl_assert) : sl_entails SLFalse p.
  Proof. intros h Hfalse. contradiction. Qed.

  (** [∗]-monotonicity for entailment *)
  Lemma sl_entails_star_mono (p1 q1 p2 q2 : sl_assert) :
    sl_entails p1 p2 ->
    sl_entails q1 q2 ->
    sl_entails (SLStar p1 q1) (SLStar p2 q2).
  Proof.
    intros Hp Hq.
    intros h Hstar.
    apply (sl_star_mono p1 q1 p2 q2 Hp Hq).
    exact Hstar.
  Qed.

End SLEntailment.

(* ================================================================= *)
(** ** Integration with BI Assertion Logic                            *)
(* ================================================================= *)

(** [sl_atom_sat] makes [sl_assert] usable as atomic assertions
    in the BI framework from [OL/Assertion.v].  A heap [h] satisfies
    an [sl_assert] atom [p] exactly when [sl_sat h p] holds. *)

Definition sl_atom_sat (h : Heap) (p : sl_assert) : Prop :=
  sl_sat h p.

(* ================================================================= *)
(** ** Notation                                                        *)
(* ================================================================= *)

Declare Scope sl_scope.
Delimit Scope sl_scope with sl.

Notation "'emp'" := SLEmp : sl_scope.
Notation "e1 '↦' e2" := (SLPointsTo e1 e2)
  (at level 30, no associativity) : sl_scope.
Notation "e '↦' '−'" := (SLPointsAny e)
  (at level 30, no associativity) : sl_scope.
Notation "e '↛'" := (SLInvalid e)
  (at level 30, no associativity) : sl_scope.
Notation "p '∗' q" := (SLStar p q)
  (at level 40, left associativity) : sl_scope.
Notation "p '−∗' q" := (SLWand p q)
  (at level 55, right associativity) : sl_scope.
Notation "'⌜' P '⌝'" := (SLPure P) : sl_scope.
Notation "p '∧ₛ' q" := (SLAnd p q)
  (at level 40, left associativity) : sl_scope.
Notation "p '∨ₛ' q" := (SLOr p q)
  (at level 50, left associativity) : sl_scope.
Notation "'∃ₛ' x , p" := (SLExists (fun x => p))
  (at level 60, x binder, right associativity) : sl_scope.
Notation "'∀ₛ' x , p" := (SLForall (fun x => p))
  (at level 60, x binder, right associativity) : sl_scope.

(** Notation for SL satisfaction and entailment *)
Notation "h '⊨ₛ' p" := (sl_sat h p)
  (at level 70, no associativity) : sl_scope.
Notation "p '⊢ₛ' q" := (sl_entails p q)
  (at level 80, no associativity) : sl_scope.

(* ================================================================= *)
(** ** SL Structural Lemmas — Star                                    *)
(* ================================================================= *)

Module SLStructural.

Section SLStarStructural.

  (** [p ∗ q] is commutative: [sl_sat h (SLStar p q) <-> sl_sat h (SLStar q p)] *)
  Lemma sl_star_comm (h : Heap) (p q : sl_assert) :
    sl_sat h (SLStar p q) <-> sl_sat h (SLStar q p).
  Proof.
    simpl. split; intros [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
    - exists h2, h1.
      split; [apply heap_disjoint_sym; exact Hdisj |].
      split; [rewrite (heap_union_comm h2 h1 (heap_disjoint_sym h1 h2 Hdisj));
              exact Hunion |].
      split; [exact H2 | exact H1].
    - exists h2, h1.
      split; [apply heap_disjoint_sym; exact Hdisj |].
      split; [rewrite (heap_union_comm h2 h1 (heap_disjoint_sym h1 h2 Hdisj));
              exact Hunion |].
      split; [exact H2 | exact H1].
  Qed.

  (** [p ∗ emp ⊣⊢ p] *)
  Lemma sl_star_emp_r (h : Heap) (p : sl_assert) :
    sl_sat h (SLStar p SLEmp) <-> sl_sat h p.
  Proof.
    simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [Hp Hemp]]]]].
      subst h2. rewrite heap_union_empty_r in Hunion.
      subst h. exact Hp.
    - intro Hp.
      exists h, heap_empty.
      split; [apply heap_disjoint_empty_r |].
      split; [apply heap_union_empty_r |].
      split; [exact Hp | reflexivity].
  Qed.

  Lemma sl_star_emp_l (h : Heap) (p : sl_assert) :
    sl_sat h (SLStar SLEmp p) <-> sl_sat h p.
  Proof.
    simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [Hemp Hp]]]]].
      subst h1. rewrite heap_union_empty_l in Hunion.
      subst h. exact Hp.
    - intro Hp.
      exists heap_empty, h.
      split; [apply heap_disjoint_empty_l |].
      split; [apply heap_union_empty_l |].
      split; [reflexivity | exact Hp].
  Qed.

  (** [(p ∗ q) ∗ r ⊣⊢ p ∗ (q ∗ r)] *)
  Lemma sl_star_assoc (h : Heap) (p q r : sl_assert) :
    sl_sat h (SLStar (SLStar p q) r) <-> sl_sat h (SLStar p (SLStar q r)).
  Proof.
    simpl. split.
    - intros [h12 [h3 [Hdisj12_3 [Hunion12_3
               [[h1 [h2 [Hdisj12 [Hunion12 [Hp Hq]]]]] Hr]]]]].
      subst h12.
      exists h1, (heap_union h2 h3).
      split.
      + apply heap_disjoint_union_reassoc; assumption.
      + split.
        * rewrite <- heap_union_assoc;
            [exact Hunion12_3 | exact Hdisj12 | exact Hdisj12_3].
        * split.
          -- exact Hp.
          -- exists h2, h3.
             split; [eapply heap_disjoint_union_l; eassumption |].
             split; [reflexivity |].
             split; [exact Hq | exact Hr].
    - intros [h1 [h23 [Hdisj1_23 [Hunion1_23
               [Hp [h2 [h3 [Hdisj23 [Hunion23 [Hq Hr]]]]]]]]]].
      subst h23.
      assert (Hdisj12 : heap_disjoint h1 h2).
      { intros a.
        destruct (Hdisj1_23 a) as [H1 | H23].
        - left. exact H1.
        - unfold heap_union in H23.
          destruct (h2 a) eqn:E2.
          + discriminate H23.
          + right. reflexivity. }
      assert (Hdisj12_3 : heap_disjoint (heap_union h1 h2) h3).
      { intros a. unfold heap_union.
        destruct (h1 a) eqn:E1.
        - destruct (Hdisj1_23 a) as [H1' | H23].
          + rewrite E1 in H1'. discriminate H1'.
          + unfold heap_union in H23.
            destruct (h2 a) eqn:E2.
            * discriminate H23.
            * right. exact H23.
        - destruct (Hdisj23 a) as [H2 | H3].
          + rewrite H2. left. reflexivity.
          + right. exact H3. }
      exists (heap_union h1 h2), h3.
      split; [exact Hdisj12_3 |].
      split.
      + rewrite (heap_union_assoc h1 h2 h3 Hdisj12 Hdisj12_3).
        exact Hunion1_23.
      + split.
        * exists h1, h2.
          split; [exact Hdisj12 |].
          split; [reflexivity |].
          split; [exact Hp | exact Hq].
        * exact Hr.
  Qed.

  (** Monotonicity: if p₁⊢p₂ and q₁⊢q₂ then p₁∗q₁ ⊢ p₂∗q₂ *)
  Lemma sl_star_mono (p1 p2 q1 q2 : sl_assert) :
    (forall h, sl_sat h p1 -> sl_sat h p2) ->
    (forall h, sl_sat h q1 -> sl_sat h q2) ->
    forall h, sl_sat h (SLStar p1 q1) -> sl_sat h (SLStar p2 q2).
  Proof.
    intros Hp Hq h [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
    exists h1, h2.
    split; [exact Hdisj |].
    split; [exact Hunion |].
    split; [apply Hp; exact H1 | apply Hq; exact H2].
  Qed.

  (** Weakening: p ∗ q ⊢ p ∗ true *)
  Lemma sl_star_weaken_r (h : Heap) (p q : sl_assert) :
    sl_sat h (SLStar p q) -> sl_sat h (SLStar p SLTrue).
  Proof.
    intros [h1 [h2 [Hdisj [Hunion [Hp Hq]]]]].
    exists h1, h2.
    split; [exact Hdisj |].
    split; [exact Hunion |].
    split; [exact Hp | exact I].
  Qed.

End SLStarStructural.

(* ================================================================= *)
(** ** SL Structural Lemmas — Wand                                    *)
(* ================================================================= *)

Section SLWandStructural.

  (** Modus ponens for wand: [p ∗ (p −∗ q) ⊢ q] *)
  Lemma sl_wand_elim (h : Heap) (p q : sl_assert) :
    sl_sat h (SLStar p (SLWand p q)) -> sl_sat h q.
  Proof.
    simpl.
    intros [h1 [h2 [Hdisj [Hunion [Hp Hwand]]]]].
    subst h.
    rewrite (heap_union_comm h1 h2 Hdisj).
    apply Hwand.
    - apply heap_disjoint_sym. exact Hdisj.
    - exact Hp.
  Qed.

  (** Introduction for wand *)
  Lemma sl_wand_intro (h : Heap) (p q : sl_assert) :
    (forall h', heap_disjoint h h' -> sl_sat h' p -> sl_sat (heap_union h h') q) ->
    sl_sat h (SLWand p q).
  Proof.
    intro H. simpl. exact H.
  Qed.

End SLWandStructural.

(* ================================================================= *)
(** ** SL Structural Lemmas — Misc                                    *)
(* ================================================================= *)

Section SLMiscStructural.

  (** [l ↛] and [l ↦ v] are contradictory on the same heap *)
  Lemma sl_invalid_not_points (h : Heap) (l v : nat) :
    sl_sat h (SLInvalid l) -> sl_sat h (SLPointsTo l v) -> False.
  Proof.
    simpl. intros Hinv Hpts.
    subst h.
    rewrite heap_singleton_lookup in Hinv.
    discriminate Hinv.
  Qed.

  (** [l ↦ v₁] and [l ↦ v₂] on same heap implies v₁ = v₂ *)
  Lemma sl_points_functional (h : Heap) (l v1 v2 : nat) :
    sl_sat h (SLPointsTo l v1) -> sl_sat h (SLPointsTo l v2) -> v1 = v2.
  Proof.
    simpl. intros H1 H2.
    subst h.
    assert (Heq : heap_singleton l v1 l = heap_singleton l v2 l).
    { rewrite H2. reflexivity. }
    rewrite heap_singleton_lookup in Heq.
    rewrite heap_singleton_lookup in Heq.
    injection Heq as Heq. exact Heq.
  Qed.

  (** Exists distributes over star (right) *)
  Lemma sl_exists_star_distr_r (h : Heap) (f : nat -> sl_assert) (q : sl_assert) :
    sl_sat h (SLStar (SLExists f) q) <-> sl_sat h (SLExists (fun x => SLStar (f x) q)).
  Proof.
    simpl. split.
    - intros [h1 [h2 [Hdisj [Hunion [[x Hfx] Hq]]]]].
      exists x, h1, h2.
      split; [exact Hdisj |].
      split; [exact Hunion |].
      split; [exact Hfx | exact Hq].
    - intros [x [h1 [h2 [Hdisj [Hunion [Hfx Hq]]]]]].
      exists h1, h2.
      split; [exact Hdisj |].
      split; [exact Hunion |].
      split; [exists x; exact Hfx | exact Hq].
  Qed.

End SLMiscStructural.

End SLStructural.
