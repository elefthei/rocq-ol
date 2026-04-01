(** * OL/Heap/Rules.v — Separation Logic Rules for Outcome Logic

    Defines heap primitive operations and proves their separation logic
    specifications as Outcome Logic triples.  Also proves the Frame rule,
    Lifting lemma, and Error Propagation for heap reasoning.

    Components:
    - Heap primitive operations (alloc, free, store, load) as
      [Heap → PSet (err_state Heap)] functions
    - SL small axioms: each operation's specification as an OL triple
    - Frame rule: operations preserve disjoint frame heaps
    - Lifting: connect SL heap-level reasoning to BI outcome assertions
    - Error Propagation: errors propagate through frames

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5, Figure 5 *)

From Stdlib Require Import Ensembles Classical_Prop PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Rules Require Import Generic.
From OL.Heap Require Import Assertion Error Lang.

(* ================================================================= *)
(** ** Heap Primitive Operations                                      *)
(* ================================================================= *)

(** Each heap operation takes a heap and returns a set of error-tagged
    heaps via the powerset monad.  Operations that access unallocated
    memory produce error outcomes; successful operations produce ok
    outcomes.  These match the mGCL operations from the paper. *)

(** [heap_alloc l v h] allocates address [l] with value [v].
    If [l] is already allocated, this is an error (double-alloc).
    Otherwise, the result is the extended heap. *)
Definition heap_alloc (l v : nat) (h : Heap) : PSet (err_state Heap) :=
  match h l with
  | Some _ => pset_ret (Er h)
  | None   => pset_ret (Ok (heap_union (heap_singleton l v) h))
  end.

(** [heap_free l h] frees address [l].
    If [l] is allocated, it is removed.  If unallocated, error. *)
Definition heap_free (l : nat) (h : Heap) : PSet (err_state Heap) :=
  match h l with
  | Some _ => pset_ret (Ok (fun a => if Nat.eqb a l then None else h a))
  | None   => pset_ret (Er h)
  end.

(** [heap_store l v h] writes value [v] to address [l].
    If [l] is allocated, the value is updated.  If unallocated, error. *)
Definition heap_store (l v : nat) (h : Heap) : PSet (err_state Heap) :=
  match h l with
  | Some _ => pset_ret (Ok (fun a => if Nat.eqb a l then Some v else h a))
  | None   => pset_ret (Er h)
  end.

(** [heap_load l h] reads the value at address [l].
    Returns the heap unchanged if [l] is allocated; error if not.
    (In a full language, the read value would be placed in a register;
     here we model just the heap effect.) *)
Definition heap_load (l : nat) (h : Heap) : PSet (err_state Heap) :=
  match h l with
  | Some _ => pset_ret (Ok h)
  | None   => pset_ret (Er h)
  end.

(** Error-tagged wrappers: propagate errors unchanged. *)
Definition heap_alloc_err (l v : nat) (s : err_state Heap)
  : PSet (err_state Heap) :=
  match s with
  | Ok h  => heap_alloc l v h
  | Er h  => pset_ret (Er h)
  end.

Definition heap_free_err (l : nat) (s : err_state Heap)
  : PSet (err_state Heap) :=
  match s with
  | Ok h  => heap_free l h
  | Er h  => pset_ret (Er h)
  end.

Definition heap_store_err (l v : nat) (s : err_state Heap)
  : PSet (err_state Heap) :=
  match s with
  | Ok h  => heap_store l v h
  | Er h  => pset_ret (Er h)
  end.

Definition heap_load_err (l : nat) (s : err_state Heap)
  : PSet (err_state Heap) :=
  match s with
  | Ok h  => heap_load l h
  | Er h  => pset_ret (Er h)
  end.

(* ================================================================= *)
(** ** Helper Lemmas                                                  *)
(* ================================================================= *)

Section Helpers.

  Lemma heap_union_none_l (h1 hf : Heap) (a : nat) :
    h1 a = None -> heap_union h1 hf a = hf a.
  Proof. intro H. unfold heap_union. rewrite H. reflexivity. Qed.

  Lemma heap_union_some_l (h1 hf : Heap) (a : nat) (v : nat) :
    h1 a = Some v -> heap_union h1 hf a = Some v.
  Proof. intro H. unfold heap_union. rewrite H. reflexivity. Qed.

  Lemma heap_remove_singleton (l : nat) (v : nat) (h : Heap) :
    heap_disjoint (heap_singleton l v) h ->
    (fun a => if Nat.eqb a l then None else heap_union (heap_singleton l v) h a) =
    h.
  Proof.
    intro Hdisj.
    apply heap_ext. intro a.
    destruct (Nat.eqb a l) eqn:Eal.
    - apply Nat.eqb_eq in Eal. subst a.
      destruct (Hdisj l) as [H1 | H2].
      + unfold heap_singleton in H1. rewrite Nat.eqb_refl in H1. discriminate H1.
      + symmetry. exact H2.
    - unfold heap_union, heap_singleton.
      rewrite Eal. reflexivity.
  Qed.

  Lemma heap_store_singleton (l old_v new_v : nat) (h : Heap) :
    heap_disjoint (heap_singleton l old_v) h ->
    (fun a => if Nat.eqb a l then Some new_v
              else heap_union (heap_singleton l old_v) h a) =
    heap_union (heap_singleton l new_v) h.
  Proof.
    intro Hdisj.
    apply heap_ext. intro a.
    destruct (Nat.eqb a l) eqn:Eal.
    - apply Nat.eqb_eq in Eal. subst a.
      unfold heap_union, heap_singleton. rewrite Nat.eqb_refl. reflexivity.
    - unfold heap_union, heap_singleton. rewrite Eal. reflexivity.
  Qed.

  Lemma heap_singleton_disjoint_lookup (l v : nat) (hf : Heap) :
    heap_disjoint (heap_singleton l v) hf ->
    hf l = None.
  Proof.
    intro Hdisj.
    destruct (Hdisj l) as [H | H].
    - unfold heap_singleton in H. rewrite Nat.eqb_refl in H. discriminate H.
    - exact H.
  Qed.

End Helpers.

(* ================================================================= *)
(** ** SL Small Axioms — Pointwise                                    *)
(* ================================================================= *)

Section SmallAxioms.

  (** Alloc: unallocated address. *)
  Lemma alloc_ok (l v : nat) (h : Heap) :
    sl_sat h (SLInvalid l) ->
    In _ (heap_alloc l v h) (Ok (heap_union (heap_singleton l v) h)).
  Proof.
    simpl. intro Hnone.
    unfold heap_alloc. rewrite Hnone. constructor.
  Qed.

  Lemma alloc_er (l v : nat) (h : Heap) :
    h l <> None ->
    In _ (heap_alloc l v h) (Er h).
  Proof.
    intro Hsome. unfold heap_alloc.
    destruct (h l) eqn:Ehl.
    - constructor.
    - exfalso. apply Hsome. reflexivity.
  Qed.

  (** Free: allocated address. *)
  Lemma free_singleton_ok (l v : nat) :
    In _ (heap_free l (heap_singleton l v)) (Ok heap_empty).
  Proof.
    unfold heap_free, heap_singleton.
    rewrite Nat.eqb_refl.
    assert (H : (fun a => if Nat.eqb a l then None
                          else (fun a0 => if Nat.eqb a0 l then Some v else None) a)
                = heap_empty).
    { apply heap_ext. intro a.
      destruct (Nat.eqb a l) eqn:E; reflexivity. }
    rewrite H. constructor.
  Qed.

  Lemma free_ok (l : nat) (v : nat) (h : Heap) :
    h l = Some v ->
    In _ (heap_free l h) (Ok (fun a => if Nat.eqb a l then None else h a)).
  Proof.
    intro Hsome. unfold heap_free. rewrite Hsome. constructor.
  Qed.

  Lemma free_er (l : nat) (h : Heap) :
    h l = None ->
    In _ (heap_free l h) (Er h).
  Proof.
    intro Hnone. unfold heap_free. rewrite Hnone. constructor.
  Qed.

  (** Store: allocated address. *)
  Lemma store_singleton_ok (l old_v new_v : nat) :
    In _ (heap_store l new_v (heap_singleton l old_v))
         (Ok (heap_singleton l new_v)).
  Proof.
    unfold heap_store, heap_singleton.
    rewrite Nat.eqb_refl.
    assert (H : (fun a => if Nat.eqb a l then Some new_v
                          else (fun a0 => if Nat.eqb a0 l then Some old_v else None) a)
                = heap_singleton l new_v).
    { apply heap_ext. intro a. unfold heap_singleton.
      destruct (Nat.eqb a l) eqn:E; reflexivity. }
    rewrite H. constructor.
  Qed.

  Lemma store_ok (l old_v new_v : nat) (h : Heap) :
    h l = Some old_v ->
    In _ (heap_store l new_v h)
         (Ok (fun a => if Nat.eqb a l then Some new_v else h a)).
  Proof.
    intro Hsome. unfold heap_store. rewrite Hsome. constructor.
  Qed.

  Lemma store_er (l v : nat) (h : Heap) :
    h l = None ->
    In _ (heap_store l v h) (Er h).
  Proof.
    intro Hnone. unfold heap_store. rewrite Hnone. constructor.
  Qed.

  (** Load: allocated address. *)
  Lemma load_ok (l : nat) (v : nat) (h : Heap) :
    h l = Some v ->
    In _ (heap_load l h) (Ok h).
  Proof.
    intro Hsome. unfold heap_load. rewrite Hsome. constructor.
  Qed.

  Lemma load_er (l : nat) (h : Heap) :
    h l = None ->
    In _ (heap_load l h) (Er h).
  Proof.
    intro Hnone. unfold heap_load. rewrite Hnone. constructor.
  Qed.

End SmallAxioms.

(* ================================================================= *)
(** ** Concrete Frame Lemmas                                          *)
(* ================================================================= *)

(** For each concrete heap operation, we prove the frame property
    directly: if the precondition holds on the small heap and the
    frame is disjoint, the operation on the combined heap yields
    the expected result with the frame preserved. *)

Section ConcreteFrame.

  Lemma free_frame (l v : nat) (hf : Heap) :
    heap_disjoint (heap_singleton l v) hf ->
    exists h',
      In _ (heap_free l (heap_union (heap_singleton l v) hf)) (Ok h') /\
      h' = hf.
  Proof.
    intro Hdisj.
    exists hf. split.
    - unfold heap_free.
      unfold heap_union at 1. unfold heap_singleton at 1.
      rewrite Nat.eqb_refl.
      rewrite (heap_remove_singleton l v hf Hdisj).
      constructor.
    - reflexivity.
  Qed.

  Lemma store_frame (l old_v new_v : nat) (hf : Heap) :
    heap_disjoint (heap_singleton l old_v) hf ->
    exists h',
      In _ (heap_store l new_v (heap_union (heap_singleton l old_v) hf)) (Ok h') /\
      h' = heap_union (heap_singleton l new_v) hf.
  Proof.
    intro Hdisj.
    exists (heap_union (heap_singleton l new_v) hf). split.
    - unfold heap_store.
      unfold heap_union at 1. unfold heap_singleton at 1.
      rewrite Nat.eqb_refl.
      rewrite (heap_store_singleton l old_v new_v hf Hdisj).
      constructor.
    - reflexivity.
  Qed.

  Lemma load_frame (l v : nat) (hf : Heap) :
    heap_disjoint (heap_singleton l v) hf ->
    In _ (heap_load l (heap_union (heap_singleton l v) hf))
         (Ok (heap_union (heap_singleton l v) hf)).
  Proof.
    intro Hdisj.
    unfold heap_load.
    unfold heap_union at 1. unfold heap_singleton at 1.
    rewrite Nat.eqb_refl.
    constructor.
  Qed.

  Lemma alloc_frame (l v : nat) (h hf : Heap) :
    heap_disjoint h hf ->
    h l = None ->
    hf l = None ->
    In _ (heap_alloc l v (heap_union h hf))
         (Ok (heap_union (heap_singleton l v) (heap_union h hf))).
  Proof.
    intros Hdisj Hh Hhf.
    unfold heap_alloc.
    rewrite (heap_union_none_l h hf l Hh).
    rewrite Hhf.
    constructor.
  Qed.

End ConcreteFrame.

(* ================================================================= *)
(** ** OL Satisfaction: PSet (err_state Heap)                         *)
(* ================================================================= *)

(** Lift [sl_sat] to error-tagged PSet-level satisfaction for use
    as the atomic satisfaction in BI formulas.

    This is the composition [nd_atom_sat ∘ err_atom_sat ∘ sl_sat]:
    - [nd_atom_sat] (from Assertion.v) provides non-emptiness + universal
      satisfaction over powerset elements
    - [err_atom_sat] (from Error.v) dispatches Ok/Er tags
    - [sl_sat] (from Assertion.v) provides heap-level SL satisfaction

    We define it separately (rather than reusing [nd_atom_sat] directly)
    because the carrier type is [PSet (err_state Heap)] and the atom
    type is [err_assert sl_assert], requiring the composed satisfaction. *)

Definition heap_nd_atom_sat (S : PSet (err_state Heap)) (a : err_assert sl_assert) : Prop :=
  (exists s, In _ S s) /\
  (forall s, In _ S s -> err_atom_sat sl_sat s a).

(** OL triple over heap operations. *)
Definition heap_ol_valid
    (denote : err_state Heap -> PSet (err_state Heap))
    (phi psi : bi_formula (err_assert sl_assert)) : Prop :=
  ol_valid heap_nd_atom_sat denote phi psi.

(** Under-approximate OL triple. *)
Definition heap_ol_valid_under
    (denote : err_state Heap -> PSet (err_state Heap))
    (phi psi : bi_formula (err_assert sl_assert)) : Prop :=
  ol_valid_under heap_nd_atom_sat denote phi psi.

(* ================================================================= *)
(** ** Lifting: SL Pointwise → OL Triple                              *)
(* ================================================================= *)

(** The Lifting lemma connects pointwise SL heap-level reasoning
    to the BI outcome assertion logic. *)

Section Lifting.

  (** Lifting for singleton ok states. *)
  Lemma lift_ok_singleton (h : Heap) (P : sl_assert) :
    sl_sat h P ->
    bi_sat heap_nd_atom_sat (pset_ret (Ok h)) (BiAtom (AOk P)).
  Proof.
    intro Hsat. simpl. unfold heap_nd_atom_sat, nd_atom_sat.
    split.
    - exists (Ok h). constructor.
    - intros s Hin. inversion Hin; subst. simpl. exact Hsat.
  Qed.

  Lemma lift_er_singleton (h : Heap) (Q : sl_assert) :
    sl_sat h Q ->
    bi_sat heap_nd_atom_sat (pset_ret (Er h)) (BiAtom (AEr Q)).
  Proof.
    intro Hsat. simpl. unfold heap_nd_atom_sat, nd_atom_sat.
    split.
    - exists (Er h). constructor.
    - intros s Hin. inversion Hin; subst. simpl. exact Hsat.
  Qed.

  (** Extraction from ok satisfaction. *)
  Lemma lift_ok_extract (h : Heap) (P : sl_assert) :
    bi_sat heap_nd_atom_sat (pset_ret (Ok h)) (BiAtom (AOk P)) ->
    sl_sat h P.
  Proof.
    simpl. unfold heap_nd_atom_sat, nd_atom_sat.
    intros [_ Hforall].
    apply (Hforall (Ok h)). constructor.
  Qed.

  Lemma lift_er_extract (h : Heap) (Q : sl_assert) :
    bi_sat heap_nd_atom_sat (pset_ret (Er h)) (BiAtom (AEr Q)) ->
    sl_sat h Q.
  Proof.
    simpl. unfold heap_nd_atom_sat, nd_atom_sat.
    intros [_ Hforall].
    apply (Hforall (Er h)). constructor.
  Qed.

  Lemma collect_singleton (f : err_state Heap -> PSet (err_state Heap))
      (s : err_state Heap) :
    collect f (pset_ret s) = f s.
  Proof. unfold collect. apply pset_bind_ret_l. Qed.

  (** Full Lifting: pointwise ok-spec → OL triple. *)
  Lemma lifting_ok
      (op : err_state Heap -> PSet (err_state Heap))
      (P Q : sl_assert) :
    (forall h, sl_sat h P ->
               exists h', op (Ok h) = pset_ret (Ok h') /\ sl_sat h' Q) ->
    heap_ol_valid op (BiAtom (AOk P)) (BiAtom (AOk Q)).
  Proof.
    intros Hspec m Hpre.
    simpl in Hpre. destruct Hpre as [Hne Hforall].
    unfold collect, pset_bind.
    simpl. split.
    - destruct Hne as [s Hs].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + destruct (Hspec h Hforall) as [h' [Heq HsatQ]].
        exists (Ok h'). exists (Ok h). split; [exact Hs |].
        rewrite Heq. constructor.
      + simpl in Hforall. contradiction.
    - intros tau [s [Hs Htau]].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + destruct (Hspec h Hforall) as [h' [Heq HsatQ]].
        rewrite Heq in Htau. inversion Htau; subst.
        simpl. exact HsatQ.
      + simpl in Hforall. contradiction.
  Qed.

  (** Lifting for error outcomes. *)
  Lemma lifting_er
      (op : err_state Heap -> PSet (err_state Heap))
      (P Q : sl_assert) :
    (forall h, sl_sat h P ->
               exists h', op (Ok h) = pset_ret (Er h') /\ sl_sat h' Q) ->
    heap_ol_valid op (BiAtom (AOk P)) (BiAtom (AEr Q)).
  Proof.
    intros Hspec m Hpre.
    simpl in Hpre. destruct Hpre as [Hne Hforall].
    unfold collect, pset_bind.
    simpl. split.
    - destruct Hne as [s Hs].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + destruct (Hspec h Hforall) as [h' [Heq HsatQ]].
        exists (Er h'). exists (Ok h). split; [exact Hs |].
        rewrite Heq. constructor.
      + simpl in Hforall. contradiction.
    - intros tau [s [Hs Htau]].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + destruct (Hspec h Hforall) as [h' [Heq HsatQ]].
        rewrite Heq in Htau. inversion Htau; subst.
        simpl. exact HsatQ.
      + simpl in Hforall. contradiction.
  Qed.

End Lifting.

(* ================================================================= *)
(** ** Error Propagation                                              *)
(* ================================================================= *)

Section ErrorPropagation.

  Definition err_preserving (op : err_state Heap -> PSet (err_state Heap)) : Prop :=
    forall h, op (Er h) = pset_ret (Er h).

  Lemma alloc_err_preserving (l v : nat) : err_preserving (heap_alloc_err l v).
  Proof. intros h. reflexivity. Qed.

  Lemma free_err_preserving (l : nat) : err_preserving (heap_free_err l).
  Proof. intros h. reflexivity. Qed.

  Lemma store_err_preserving (l v : nat) : err_preserving (heap_store_err l v).
  Proof. intros h. reflexivity. Qed.

  Lemma load_err_preserving (l : nat) : err_preserving (heap_load_err l).
  Proof. intros h. reflexivity. Qed.

  (** Error Propagation triple: errors pass through unchanged.
      [⊨ ⟨er:P⟩ op ⟨er:P⟩] *)
  Lemma error_propagation
      (op : err_state Heap -> PSet (err_state Heap))
      (P : sl_assert) :
    err_preserving op ->
    heap_ol_valid op (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof.
    intros Hpres m Hpre.
    simpl in Hpre. destruct Hpre as [Hne Hforall].
    unfold collect, pset_bind.
    simpl. split.
    - destruct Hne as [s Hs].
      specialize (Hforall s Hs) as Hsat.
      destruct s as [h | h].
      + simpl in Hsat. contradiction.
      + exists (Er h). exists (Er h). split; [exact Hs |].
        rewrite (Hpres h). constructor.
    - intros tau [s [Hs Htau]].
      specialize (Hforall s Hs) as Hsat.
      destruct s as [h | h].
      + simpl in Hsat. contradiction.
      + rewrite (Hpres h) in Htau. inversion Htau; subst.
        simpl. exact Hsat.
  Qed.

  (** Error propagation through sequential composition. *)
  Lemma err_preserving_seq
      (op1 op2 : err_state Heap -> PSet (err_state Heap)) :
    err_preserving op1 ->
    err_preserving op2 ->
    err_preserving (fun s => pset_bind (op1 s) op2).
  Proof.
    intros Hp1 Hp2 h.
    unfold pset_bind. rewrite (Hp1 h).
    apply ensemble_ext. intro tau. split.
    - intros [s [Hin Htau]].
      inversion Hin; subst.
      rewrite (Hp2 h) in Htau. inversion Htau; subst.
      constructor.
    - intro Hret. inversion Hret; subst.
      exists (Er h). split; [constructor |].
      rewrite (Hp2 h). constructor.
  Qed.

  Lemma error_propagation_seq
      (op1 op2 : err_state Heap -> PSet (err_state Heap))
      (P : sl_assert) :
    err_preserving op1 ->
    err_preserving op2 ->
    heap_ol_valid (fun s => pset_bind (op1 s) op2)
      (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof.
    intros Hp1 Hp2.
    apply error_propagation.
    apply err_preserving_seq; assumption.
  Qed.

End ErrorPropagation.

(* ================================================================= *)
(** ** Concrete OL Triples for Heap Operations                        *)
(* ================================================================= *)

Section ConcreteTriples.

  (** Alloc: [⊨ ⟨ok:(l ↛)⟩ alloc(l,v) ⟨ok:((l ↦ v) ∗ (l ↛))⟩] *)
  Lemma alloc_ol_triple (l v : nat) :
    heap_ol_valid (heap_alloc_err l v)
      (BiAtom (AOk (SLInvalid l)))
      (BiAtom (AOk (SLStar (SLPointsTo l v) (SLInvalid l)))).
  Proof.
    apply lifting_ok.
    intros h Hsat. simpl in Hsat.
    exists (heap_union (heap_singleton l v) h).
    split.
    - simpl. unfold heap_alloc. rewrite Hsat. reflexivity.
    - simpl. exists (heap_singleton l v), h.
      split.
      + intros a. unfold heap_singleton.
        destruct (Nat.eqb a l) eqn:Eal.
        * apply Nat.eqb_eq in Eal. subst a. right. exact Hsat.
        * left. reflexivity.
      + split; [reflexivity |].
        split; [reflexivity | simpl; exact Hsat].
  Qed.

  (** Free: [⊨ ⟨ok:(l ↦ v)⟩ free(l) ⟨ok:emp⟩] *)
  Lemma free_ol_triple (l v : nat) :
    heap_ol_valid (heap_free_err l)
      (BiAtom (AOk (SLPointsTo l v)))
      (BiAtom (AOk SLEmp)).
  Proof.
    apply lifting_ok.
    intros h Hsat. simpl in Hsat. subst h.
    exists heap_empty. split.
    - simpl. unfold heap_free, heap_singleton.
      rewrite Nat.eqb_refl.
      assert (Heq : (fun a : nat => if Nat.eqb a l then None
                     else (if Nat.eqb a l then Some v else None))
                    = heap_empty).
      { apply heap_ext. intro a.
        destruct (Nat.eqb a l) eqn:E; reflexivity. }
      rewrite Heq. reflexivity.
    - simpl. reflexivity.
  Qed.

  (** Store: [⊨ ⟨ok:(l ↦ old_v)⟩ store(l,new_v) ⟨ok:(l ↦ new_v)⟩] *)
  Lemma store_ol_triple (l old_v new_v : nat) :
    heap_ol_valid (heap_store_err l new_v)
      (BiAtom (AOk (SLPointsTo l old_v)))
      (BiAtom (AOk (SLPointsTo l new_v))).
  Proof.
    apply lifting_ok.
    intros h Hsat. simpl in Hsat. subst h.
    exists (heap_singleton l new_v). split.
    - simpl. unfold heap_store, heap_singleton.
      rewrite Nat.eqb_refl.
      assert (Heq : (fun a : nat => if Nat.eqb a l then Some new_v
                     else (if Nat.eqb a l then Some old_v else None))
                    = heap_singleton l new_v).
      { apply heap_ext. intro a. unfold heap_singleton.
        destruct (Nat.eqb a l) eqn:E; reflexivity. }
      rewrite Heq. reflexivity.
    - simpl. reflexivity.
  Qed.

  (** Load: [⊨ ⟨ok:(l ↦ v)⟩ load(l) ⟨ok:(l ↦ v)⟩] *)
  Lemma load_ol_triple (l v : nat) :
    heap_ol_valid (heap_load_err l)
      (BiAtom (AOk (SLPointsTo l v)))
      (BiAtom (AOk (SLPointsTo l v))).
  Proof.
    apply lifting_ok.
    intros h Hsat. simpl in Hsat. subst h.
    exists (heap_singleton l v). split.
    - simpl. unfold heap_load, heap_singleton.
      rewrite Nat.eqb_refl. reflexivity.
    - simpl. reflexivity.
  Qed.

  (** Free error: [⊨ ⟨ok:(l ↛)⟩ free(l) ⟨er:(l ↛)⟩] *)
  Lemma free_error_triple (l : nat) :
    heap_ol_valid (heap_free_err l)
      (BiAtom (AOk (SLInvalid l)))
      (BiAtom (AEr (SLInvalid l))).
  Proof.
    apply lifting_er.
    intros h Hsat. simpl in Hsat.
    exists h. split.
    - simpl. unfold heap_free. rewrite Hsat. reflexivity.
    - simpl. exact Hsat.
  Qed.

  (** Store error: [⊨ ⟨ok:(l ↛)⟩ store(l,v) ⟨er:(l ↛)⟩] *)
  Lemma store_error_triple (l v : nat) :
    heap_ol_valid (heap_store_err l v)
      (BiAtom (AOk (SLInvalid l)))
      (BiAtom (AEr (SLInvalid l))).
  Proof.
    apply lifting_er.
    intros h Hsat. simpl in Hsat.
    exists h. split.
    - simpl. unfold heap_store. rewrite Hsat. reflexivity.
    - simpl. exact Hsat.
  Qed.

  (** Load error: [⊨ ⟨ok:(l ↛)⟩ load(l) ⟨er:(l ↛)⟩] *)
  Lemma load_error_triple (l : nat) :
    heap_ol_valid (heap_load_err l)
      (BiAtom (AOk (SLInvalid l)))
      (BiAtom (AEr (SLInvalid l))).
  Proof.
    apply lifting_er.
    intros h Hsat. simpl in Hsat.
    exists h. split.
    - simpl. unfold heap_load. rewrite Hsat. reflexivity.
    - simpl. exact Hsat.
  Qed.

  (** Error propagation for all operations. *)
  Lemma alloc_error_prop (l v : nat) (P : sl_assert) :
    heap_ol_valid (heap_alloc_err l v) (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof. apply error_propagation, alloc_err_preserving. Qed.

  Lemma free_error_prop (l : nat) (P : sl_assert) :
    heap_ol_valid (heap_free_err l) (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof. apply error_propagation, free_err_preserving. Qed.

  Lemma store_error_prop (l v : nat) (P : sl_assert) :
    heap_ol_valid (heap_store_err l v) (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof. apply error_propagation, store_err_preserving. Qed.

  Lemma load_error_prop (l : nat) (P : sl_assert) :
    heap_ol_valid (heap_load_err l) (BiAtom (AEr P)) (BiAtom (AEr P)).
  Proof. apply error_propagation, load_err_preserving. Qed.

End ConcreteTriples.

(* ================================================================= *)
(** ** Frame Rule — SL Level                                          *)
(* ================================================================= *)

(** The SL Frame Rule: if a heap operation transforms a small
    footprint satisfying [P] into one satisfying [Q], then on
    the extended heap [P ∗ R], it yields [Q ∗ R]. *)

Section FrameRule.

  (** Generic SL frame for deterministic operations. *)
  Lemma sl_frame_rule_det
      (op : Heap -> PSet (err_state Heap))
      (P Q R : sl_assert) :
    (forall h, sl_sat h P ->
               exists h', op h = pset_ret (Ok h') /\ sl_sat h' Q) ->
    (forall h1 hf,
        heap_disjoint h1 hf ->
        sl_sat h1 P ->
        forall h1', op h1 = pset_ret (Ok h1') ->
        exists h',
          op (heap_union h1 hf) = pset_ret (Ok h') /\
          heap_disjoint h1' hf /\
          h' = heap_union h1' hf) ->
    forall h, sl_sat h (SLStar P R) ->
              exists h', op h = pset_ret (Ok h') /\ sl_sat h' (SLStar Q R).
  Proof.
    intros Hspec Hlocal h Hstar.
    simpl in Hstar.
    destruct Hstar as [h1 [h2 [Hdisj [Hunion [HsatP HsatR]]]]].
    subst h.
    destruct (Hspec h1 HsatP) as [h1' [Heq1 HsatQ]].
    destruct (Hlocal h1 h2 Hdisj HsatP h1' Heq1) as [h' [Heq' [Hdisj' Hh']]].
    exists h'. split.
    - exact Heq'.
    - subst h'. simpl.
      exists h1', h2.
      split; [exact Hdisj' |].
      split; [reflexivity |].
      split; [exact HsatQ | exact HsatR].
  Qed.

  (** Lift SL frame to OL triple. *)
  Lemma sl_frame_lifted
      (op_raw : Heap -> PSet (err_state Heap))
      (P Q R : sl_assert) :
    (forall h, sl_sat h P ->
               exists h', op_raw h = pset_ret (Ok h') /\ sl_sat h' Q) ->
    (forall h1 hf,
        heap_disjoint h1 hf ->
        sl_sat h1 P ->
        forall h1', op_raw h1 = pset_ret (Ok h1') ->
        exists h',
          op_raw (heap_union h1 hf) = pset_ret (Ok h') /\
          heap_disjoint h1' hf /\
          h' = heap_union h1' hf) ->
    let op := fun s : err_state Heap =>
                match s with
                | Ok h  => op_raw h
                | Er h  => pset_ret (Er h)
                end in
    heap_ol_valid op (BiAtom (AOk (SLStar P R))) (BiAtom (AOk (SLStar Q R))).
  Proof.
    intros Hspec Hlocal op.
    apply lifting_ok.
    intros h Hstar.
    destruct (sl_frame_rule_det op_raw P Q R Hspec Hlocal h Hstar) as [h' [Heq Hsat]].
    exists h'. split.
    - simpl. exact Heq.
    - exact Hsat.
  Qed.

End FrameRule.

(* ================================================================= *)
(** ** Frame Rule — Concrete Instances with OL Triples                *)
(* ================================================================= *)

Section ConcreteFrameTriples.

  (** Store with frame:
      [⊨ ⟨ok:((l ↦ old_v) ∗ R)⟩ store(l,new_v) ⟨ok:((l ↦ new_v) ∗ R)⟩] *)
  Lemma store_frame_triple (l old_v new_v : nat) (R : sl_assert) :
    heap_ol_valid (heap_store_err l new_v)
      (BiAtom (AOk (SLStar (SLPointsTo l old_v) R)))
      (BiAtom (AOk (SLStar (SLPointsTo l new_v) R))).
  Proof.
    apply lifting_ok.
    intros h Hstar.
    simpl in Hstar.
    destruct Hstar as [h1 [h2 [Hdisj [Hunion [Hpt HsatR]]]]].
    simpl in Hpt. subst h1.
    assert (Hh2l : h2 l = None).
    { apply (heap_singleton_disjoint_lookup l old_v). exact Hdisj. }
    exists (heap_union (heap_singleton l new_v) h2). split.
    - simpl. subst h. unfold heap_store.
      unfold heap_union at 1. unfold heap_singleton at 1.
      rewrite Nat.eqb_refl.
      rewrite (heap_store_singleton l old_v new_v h2 Hdisj).
      reflexivity.
    - simpl.
      exists (heap_singleton l new_v), h2.
      split.
      + intros a. unfold heap_singleton.
        destruct (Nat.eqb a l) eqn:Eal.
        * apply Nat.eqb_eq in Eal. subst a.
          right. exact Hh2l.
        * left. reflexivity.
      + split; [reflexivity |].
        split; [reflexivity | exact HsatR].
  Qed.

  (** Load with frame:
      [⊨ ⟨ok:((l ↦ v) ∗ R)⟩ load(l) ⟨ok:((l ↦ v) ∗ R)⟩] *)
  Lemma load_frame_triple (l v : nat) (R : sl_assert) :
    heap_ol_valid (heap_load_err l)
      (BiAtom (AOk (SLStar (SLPointsTo l v) R)))
      (BiAtom (AOk (SLStar (SLPointsTo l v) R))).
  Proof.
    apply lifting_ok.
    intros h Hstar.
    exists h. split.
    - simpl.
      simpl in Hstar.
      destruct Hstar as [h1 [h2 [Hdisj [Hunion [Hpt HsatR]]]]].
      simpl in Hpt. subst h1. subst h.
      unfold heap_load.
      unfold heap_union at 1. unfold heap_singleton at 1.
      rewrite Nat.eqb_refl. reflexivity.
    - exact Hstar.
  Qed.

  (** Free with frame:
      [⊨ ⟨ok:((l ↦ v) ∗ R)⟩ free(l) ⟨ok:R⟩] *)
  Lemma free_frame_triple (l v : nat) (R : sl_assert) :
    heap_ol_valid (heap_free_err l)
      (BiAtom (AOk (SLStar (SLPointsTo l v) R)))
      (BiAtom (AOk R)).
  Proof.
    apply lifting_ok.
    intros h Hstar.
    simpl in Hstar.
    destruct Hstar as [h1 [h2 [Hdisj [Hunion [Hpt HsatR]]]]].
    simpl in Hpt. subst h1.
    exists h2. split.
    - simpl. subst h. unfold heap_free.
      unfold heap_union at 1. unfold heap_singleton at 1.
      rewrite Nat.eqb_refl.
      rewrite (heap_remove_singleton l v h2 Hdisj).
      reflexivity.
    - exact HsatR.
  Qed.

  (** Alloc with frame:
      [⊨ ⟨ok:R⟩ alloc(l,v) ⟨ok:((l ↦ v) ∗ R)⟩]
      when [R] implies [l] is unallocated. *)
  Lemma alloc_frame_triple (l v : nat) (R : sl_assert) :
    (forall h, sl_sat h R -> h l = None) ->
    heap_ol_valid (heap_alloc_err l v)
      (BiAtom (AOk R))
      (BiAtom (AOk (SLStar (SLPointsTo l v) R))).
  Proof.
    intros Hfresh.
    apply lifting_ok.
    intros h HsatR.
    specialize (Hfresh h HsatR).
    exists (heap_union (heap_singleton l v) h). split.
    - simpl. unfold heap_alloc. rewrite Hfresh. reflexivity.
    - simpl.
      exists (heap_singleton l v), h.
      split.
      + intros a. unfold heap_singleton.
        destruct (Nat.eqb a l) eqn:Eal.
        * apply Nat.eqb_eq in Eal. subst a. right. exact Hfresh.
        * left. reflexivity.
      + split; [reflexivity |].
        split; [reflexivity | exact HsatR].
  Qed.

End ConcreteFrameTriples.

(* ================================================================= *)
(** ** OL-Level Frame Rule (⊕)                                       *)
(* ================================================================= *)

(** The Frame Rule at the BI outcome logic level using [⊕].
    If [⊨ ⟨φ⟩ op ⟨ψ⟩] and the frame [R] is preserved by [op]
    pointwise (i.e., for each element satisfying [R], [op] maps
    it to an element satisfying [R]), then
    [⊨ ⟨φ ⊕ R⟩ op ⟨ψ ⊕ R⟩]. *)

Section OLFrameRule.

  (** A formula [R] is [op]-stable if for every element [s]
      in a set satisfying [R], [op(s)] also yields a set satisfying [R]. *)
  Definition bi_stable
      (op : err_state Heap -> PSet (err_state Heap))
      (R : bi_formula (err_assert sl_assert)) : Prop :=
    forall (m : PSet (err_state Heap)),
      bi_sat heap_nd_atom_sat m R ->
      bi_sat heap_nd_atom_sat (collect op m) R.

  (** OL Frame Rule: given stability of R. *)
  Lemma ol_oplus_frame
      (op : err_state Heap -> PSet (err_state Heap))
      (phi psi R : bi_formula (err_assert sl_assert)) :
    heap_ol_valid op phi psi ->
    bi_stable op R ->
    heap_ol_valid op (BiOPlus phi R) (BiOPlus psi R).
  Proof.
    intros Hvalid Hstable m Hpre.
    simpl in Hpre.
    destruct Hpre as [m1 [m2 [Heq [Hphi HR]]]].
    simpl.
    exists (collect op m1), (collect op m2).
    split.
    - subst m. symmetry. apply collect_union.
    - split.
      + apply Hvalid. exact Hphi.
      + apply Hstable. exact HR.
  Qed.

  (** Stability of [BiTop]. *)
  Lemma bi_stable_top (op : err_state Heap -> PSet (err_state Heap)) :
    bi_stable op BiTop.
  Proof. intros m _. simpl. exact I. Qed.

  (** Stability of [BiEmpty] when [op] maps empty-set to empty-set. *)
  Lemma bi_stable_empty (op : err_state Heap -> PSet (err_state Heap)) :
    bi_stable op BiEmpty.
  Proof.
    intros m Hm.
    simpl in Hm. simpl.
    subst m.
    unfold collect.
    apply pset_bind_empty.
  Qed.

  (** Corollary: OL under-approximate frame.
      [⊨ ⟨φ⟩ op ⟨ψ⟩ → ⊨ ⟨φ ⊕ ⊤⟩ op ⟨ψ ⊕ ⊤⟩] *)
  Lemma ol_oplus_frame_top
      (op : err_state Heap -> PSet (err_state Heap))
      (phi psi : bi_formula (err_assert sl_assert)) :
    heap_ol_valid op phi psi ->
    heap_ol_valid op (BiOPlus phi BiTop) (BiOPlus psi BiTop).
  Proof.
    intro H. apply ol_oplus_frame.
    - exact H.
    - apply bi_stable_top.
  Qed.

  (** Stability of [BiAtom (AEr P)] when [op] preserves errors. *)
  Lemma bi_stable_er_atom
      (op : err_state Heap -> PSet (err_state Heap))
      (P : sl_assert) :
    err_preserving op ->
    bi_stable op (BiAtom (AEr P)).
  Proof.
    intros Hpres m Hm.
    simpl in Hm. destruct Hm as [Hne Hforall].
    simpl. unfold collect, pset_bind.
    split.
    - destruct Hne as [s Hs].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + simpl in Hforall. contradiction.
      + exists (Er h). exists (Er h). split; [exact Hs |].
        rewrite (Hpres h). constructor.
    - intros tau [s [Hs Htau]].
      specialize (Hforall s Hs).
      destruct s as [h | h].
      + simpl in Hforall. contradiction.
      + rewrite (Hpres h) in Htau.
        inversion Htau; subst. simpl. exact Hforall.
  Qed.

  (** OL Frame with error preservation:
      If [⊨ ⟨ok:P⟩ op ⟨ok:Q⟩] and [op] preserves errors, then
      [⊨ ⟨ok:P ⊕ er:R⟩ op ⟨ok:Q ⊕ er:R⟩]. *)
  Lemma ol_err_frame
      (op : err_state Heap -> PSet (err_state Heap))
      (P Q R : sl_assert) :
    heap_ol_valid op (BiAtom (AOk P)) (BiAtom (AOk Q)) ->
    err_preserving op ->
    heap_ol_valid op
      (BiOPlus (BiAtom (AOk P)) (BiAtom (AEr R)))
      (BiOPlus (BiAtom (AOk Q)) (BiAtom (AEr R))).
  Proof.
    intros Hvalid Hpres.
    apply ol_oplus_frame.
    - exact Hvalid.
    - apply bi_stable_er_atom. exact Hpres.
  Qed.

End OLFrameRule.

(* ================================================================= *)
(** ** GCL Assume Rule                                                *)
(* ================================================================= *)

(** The assume rule: if every heap satisfying [P] also satisfies [g],
    then [assume g] is the identity on [ok:P] states.

    ⊨ ⟨ok:P⟩ assume(g) ⟨ok:P⟩   when P entails g *)

Section AssumeRule.

  Lemma assume_ol_triple (g : Heap -> Prop) (P : sl_assert) :
    (forall h, sl_sat h P -> g h) ->
    heap_ol_valid (mgcl_den (MAssume g))
      (BiAtom (AOk P)) (BiAtom (AOk P)).
  Proof.
    intro Hentails.
    apply lifting_ok.
    intros h Hsat.
    exists h. split.
    - apply mgcl_den_assume_true. exact (Hentails h Hsat).
    - exact Hsat.
  Qed.

End AssumeRule.

(* ================================================================= *)
(** ** GCL If-Then-Else Rule                                          *)
(* ================================================================= *)

(** The if rule, derived from assume + seq + split:

    P₁ ⊨ g      ⊨ ⟨ok:P₁⟩ C₁ ⟨ok:Q₁⟩
    P₂ ⊨ ¬g     ⊨ ⟨ok:P₂⟩ C₂ ⟨ok:Q₂⟩
    ─────────────────────────────────────
    ⊨ ⟨ok:P₁ ⊕ ok:P₂⟩ if g then C₁ else C₂ ⟨ok:Q₁ ⊕ ok:Q₂⟩ *)

Section IfRule.

  Open Scope mgcl_scope.

  Theorem if_ol_triple
      (g : Heap -> Prop) (C1 C2 : mgcl_prog)
      (P1 P2 Q1 Q2 : sl_assert) :
    (forall h, sl_sat h P1 -> g h) ->
    (forall h, sl_sat h P2 -> ~ g h) ->
    mgcl_valid (BiAtom (AOk P1)) (BiAtom (AOk Q1)) C1 ->
    mgcl_valid (BiAtom (AOk P2)) (BiAtom (AOk Q2)) C2 ->
    mgcl_valid
      (BiOPlus (BiAtom (AOk P1)) (BiAtom (AOk P2)))
      (BiOPlus (BiAtom (AOk Q1)) (BiAtom (AOk Q2)))
      (mgcl_if g C1 C2).
  Proof.
    intros Hg Hng HC1 HC2.
    unfold mgcl_if, mgcl_assume.
    apply (@ol_split _ _ _ mgcl_atom_sat mgcl_den
             (BiAtom (AOk P1)) (BiAtom (AOk P2))
             (BiAtom (AOk Q1)) (BiAtom (AOk Q2))).
    - (* ⊨ ⟨ok:P₁⟩ if g C1 C2 ⟨ok:Q₁⟩ *)
      intros m Hpre. simpl in Hpre. destruct Hpre as [Hne Hforall].
      (* Pointwise: from P1 states, the ¬g branch is empty *)
      assert (Hpw : forall s, In _ m s ->
        ol_denote mgcl_den
          (OLPlus (OLSeq (OLAtom (MAssume g)) C1)
                  (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2)) s =
        ol_denote mgcl_den (OLSeq (OLAtom (MAssume g)) C1) s).
      { intros s Hs.
        specialize (Hforall s Hs).
        destruct s as [h | h]; [| simpl in Hforall; contradiction].
        cbn [ol_denote].
        assert (Hng_h : ~ (fun h' : Heap => ~ g h') h)
          by (intro HH; exact (HH (Hg h Hforall))).
        rewrite (mgcl_den_assume_false _ _ Hng_h).
        rewrite pset_bind_empty.
        apply pset_union_empty_r. }
      (* Lift to collect *)
      assert (Hcol : collect (ol_denote mgcl_den
                (OLPlus (OLSeq (OLAtom (MAssume g)) C1)
                        (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2))) m =
                     collect (ol_denote mgcl_den (OLSeq (OLAtom (MAssume g)) C1)) m).
      { unfold collect. apply ensemble_ext. intro x. unfold pset_bind. split.
        - intros [s [Hs Hx]]. exists s. split; [exact Hs |].
          rewrite (Hpw s Hs) in Hx. exact Hx.
        - intros [s [Hs Hx]]. exists s. split; [exact Hs |].
          rewrite (Hpw s Hs). exact Hx. }
      rewrite Hcol.
      exact (@ol_seq _ _ _ mgcl_atom_sat mgcl_den
               (BiAtom (AOk P1)) (BiAtom (AOk P1)) (BiAtom (AOk Q1))
               (OLAtom (MAssume g)) C1
               (assume_ol_triple g P1 Hg) HC1
               m (conj Hne Hforall)).
    - (* ⊨ ⟨ok:P₂⟩ if g C1 C2 ⟨ok:Q₂⟩ *)
      intros m Hpre. simpl in Hpre. destruct Hpre as [Hne Hforall].
      assert (Hpw : forall s, In _ m s ->
        ol_denote mgcl_den
          (OLPlus (OLSeq (OLAtom (MAssume g)) C1)
                  (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2)) s =
        ol_denote mgcl_den (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2) s).
      { intros s Hs.
        specialize (Hforall s Hs).
        destruct s as [h | h]; [| simpl in Hforall; contradiction].
        cbn [ol_denote].
        rewrite (mgcl_den_assume_false _ _ (Hng h Hforall)).
        rewrite pset_bind_empty.
        apply pset_union_empty_l. }
      assert (Hcol : collect (ol_denote mgcl_den
                (OLPlus (OLSeq (OLAtom (MAssume g)) C1)
                        (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2))) m =
                     collect (ol_denote mgcl_den
                       (OLSeq (OLAtom (MAssume (fun h => ~ g h))) C2)) m).
      { unfold collect. apply ensemble_ext. intro x. unfold pset_bind. split.
        - intros [s [Hs Hx]]. exists s. split; [exact Hs |].
          rewrite (Hpw s Hs) in Hx. exact Hx.
        - intros [s [Hs Hx]]. exists s. split; [exact Hs |].
          rewrite (Hpw s Hs). exact Hx. }
      rewrite Hcol.
      exact (@ol_seq _ _ _ mgcl_atom_sat mgcl_den
               (BiAtom (AOk P2)) (BiAtom (AOk P2)) (BiAtom (AOk Q2))
               (OLAtom (MAssume (fun h => ~ g h))) C2
               (assume_ol_triple _ P2 Hng) HC2
               m (conj Hne Hforall)).
  Qed.

End IfRule.

(* ================================================================= *)
(** ** GCL Star Rule (BiAtom invariant)                                *)
(* ================================================================= *)

(** The star rule: if [C] preserves an invariant [ok:I] then
    [C⋆] also preserves [ok:I].

    ⊨ ⟨ok:I⟩ C ⟨ok:I⟩
    ─────────────────
    ⊨ ⟨ok:I⟩ C⋆ ⟨ok:I⟩

    Proof idea: [C⋆] = ⋃ₙ Cⁿ.  Non-emptiness comes from 0 iterations
    (identity). Universality: any outcome ρ of [C⋆] from σ∈m is an
    outcome of [Cⁿ] for some [n]; by [ol_for], [Cⁿ] preserves [ok:I]. *)

Section StarRule.

  Lemma star_ol_triple_atom (C : mgcl_prog) (I : sl_assert) :
    mgcl_valid (BiAtom (AOk I)) (BiAtom (AOk I)) C ->
    mgcl_valid (BiAtom (AOk I)) (BiAtom (AOk I)) (OLStar C).
  Proof.
    intro Hinv.
    intros m Hpre. simpl in Hpre. destruct Hpre as [Hne Hfa].
    simpl. split.
    - (* Non-empty: 0 iterations gives identity *)
      destruct Hne as [sigma Hsigma].
      exists sigma. unfold collect, pset_bind, In.
      exists sigma. split; [exact Hsigma |].
      simpl. apply star_set_refl.
    - (* Universality: each outcome comes from some Cⁿ *)
      intros rho Hrho.
      unfold collect, pset_bind, In in Hrho.
      destruct Hrho as [sigma [Hsigma Hstar]].
      simpl in Hstar.
      apply star_is_union_of_iters in Hstar.
      destruct Hstar as [n Hiter].
      (* By ol_for, Cⁿ preserves ok:I *)
      assert (Hpre' : bi_sat mgcl_atom_sat m (BiAtom (AOk I)))
        by (simpl; exact (conj Hne Hfa)).
      pose proof (@ol_for _ _ _ mgcl_atom_sat mgcl_den
                    (BiAtom (AOk I)) C n Hinv m Hpre') as Hn.
      simpl in Hn. destruct Hn as [_ Hfa_n].
      apply Hfa_n.
      unfold collect, pset_bind, In.
      exists sigma. split; [exact Hsigma | exact Hiter].
  Qed.

End StarRule.

(* ================================================================= *)
(** ** GCL While Rule                                                  *)
(* ================================================================= *)

(** The while rule, derived from star + seq + assume:

    ⊨ ⟨ok:I⟩ (assume g ; C) ⟨ok:I⟩     ⊨ ⟨ok:I⟩ assume ¬g ⟨ok:Q⟩
    ─────────────────────────────────────────────────────────────────
    ⊨ ⟨ok:I⟩ while g C ⟨ok:Q⟩

    The first premise says the loop body preserves the invariant [I].
    The second says that from I-states, the exit guard [assume ¬g]
    produces a non-empty set satisfying [Q]. *)

Section WhileRule.

  Theorem while_ol_triple (g : Heap -> Prop) (C : mgcl_prog)
      (I Q : sl_assert) :
    mgcl_valid (BiAtom (AOk I)) (BiAtom (AOk I))
      (OLSeq (mgcl_assume g) C) ->
    mgcl_valid (BiAtom (AOk I)) (BiAtom (AOk Q))
      (mgcl_assume (fun h => ~ g h)) ->
    mgcl_valid (BiAtom (AOk I)) (BiAtom (AOk Q))
      (mgcl_while g C).
  Proof.
    intros Hbody Hexit.
    unfold mgcl_while.
    apply (@ol_seq _ _ _ mgcl_atom_sat mgcl_den
             (BiAtom (AOk I)) (BiAtom (AOk I)) (BiAtom (AOk Q))
             (OLStar (OLSeq (mgcl_assume g) C))
             (mgcl_assume (fun h => ~ g h))).
    - exact (star_ol_triple_atom _ I Hbody).
    - exact Hexit.
  Qed.

End WhileRule.

(* ================================================================= *)
(** ** Summary: All Proved Rules                                      *)
(* ================================================================= *)

(** For reference, the key rules proved in this file:

    *** SL Small Axioms (OL Triples) ***
    - [alloc_ol_triple]:     ⊨ ⟨ok:(l ↛)⟩ alloc(l,v) ⟨ok:((l ↦ v) ∗ (l ↛))⟩
    - [free_ol_triple]:      ⊨ ⟨ok:(l ↦ v)⟩ free(l) ⟨ok:emp⟩
    - [store_ol_triple]:     ⊨ ⟨ok:(l ↦ old)⟩ store(l,new) ⟨ok:(l ↦ new)⟩
    - [load_ol_triple]:      ⊨ ⟨ok:(l ↦ v)⟩ load(l) ⟨ok:(l ↦ v)⟩

    *** Error Rules ***
    - [free_error_triple]:   ⊨ ⟨ok:(l ↛)⟩ free(l) ⟨er:(l ↛)⟩
    - [store_error_triple]:  ⊨ ⟨ok:(l ↛)⟩ store(l,v) ⟨er:(l ↛)⟩
    - [load_error_triple]:   ⊨ ⟨ok:(l ↛)⟩ load(l) ⟨er:(l ↛)⟩

    *** Error Propagation ***
    - [error_propagation]:       ⊨ ⟨er:P⟩ op ⟨er:P⟩  (when op preserves errors)
    - [error_propagation_seq]:   sequential composition preserves errors
    - [{alloc,free,store,load}_error_prop]: concrete instances

    *** Frame Rule (SL level) ***
    - [store_frame_triple]:  ⊨ ⟨ok:((l↦old)∗R)⟩ store(l,new) ⟨ok:((l↦new)∗R)⟩
    - [load_frame_triple]:   ⊨ ⟨ok:((l↦v)∗R)⟩ load(l) ⟨ok:((l↦v)∗R)⟩
    - [free_frame_triple]:   ⊨ ⟨ok:((l↦v)∗R)⟩ free(l) ⟨ok:R⟩
    - [alloc_frame_triple]:  ⊨ ⟨ok:R⟩ alloc(l,v) ⟨ok:((l↦v)∗R)⟩  (R fresh for l)

    *** Frame Rule (OL ⊕ level) ***
    - [ol_oplus_frame]:      ⊨ ⟨φ⟩ op ⟨ψ⟩ → ⊨ ⟨φ⊕R⟩ op ⟨ψ⊕R⟩  (R stable)
    - [ol_oplus_frame_top]:  ⊨ ⟨φ⟩ op ⟨ψ⟩ → ⊨ ⟨φ⊕⊤⟩ op ⟨ψ⊕⊤⟩
    - [ol_err_frame]:        ⊨ ⟨ok:P⟩ op ⟨ok:Q⟩ → ⊨ ⟨ok:P⊕er:R⟩ op ⟨ok:Q⊕er:R⟩

    *** GCL Control Flow ***
    - [assume_ol_triple]:      ⊨ ⟨ok:P⟩ assume(g) ⟨ok:P⟩  (when P entails g)
    - [if_ol_triple]:          ⊨ ⟨ok:P₁⊕ok:P₂⟩ if g C₁ C₂ ⟨ok:Q₁⊕ok:Q₂⟩
    - [star_ol_triple_atom]:   ⊨ ⟨ok:I⟩ C ⟨ok:I⟩ → ⊨ ⟨ok:I⟩ C⋆ ⟨ok:I⟩
    - [while_ol_triple]:       ⊨ ⟨ok:I⟩ while g C ⟨ok:Q⟩

    *** Lifting ***
    - [lifting_ok]:   pointwise ok-spec → OL triple
    - [lifting_er]:   pointwise er-spec → OL triple
    - [sl_frame_lifted]:  SL frame + locality → OL triple
*)
