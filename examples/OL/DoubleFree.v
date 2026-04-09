(** * examples/OL/DoubleFree.v — Double-Free Detection

    Verifies that freeing the same location twice produces an error.

    Program: free(l); free(l)
    Starting state: ok: l ↦ v

    Triple: ⊨↓ ⟨ok: l ↦ v⟩ free(l); free(l) ⟨er: l ↛⟩

    The first free succeeds (deallocates l), the second free
    errors because l is no longer allocated.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL Require Import Error.
From OL.Heap Require Import Assertion Lang Rules.
From OL.Heap Require Import Manifest.

Open Scope mgcl_scope.

(* ================================================================= *)
(** ** The Program                                                    *)
(* ================================================================= *)

(** [double_free l] models [free(l); free(l)] for a fixed address [l].
    The first free deallocates [l]; the second free attempts to
    deallocate [l] again, which errors because [l] is no longer
    allocated. *)

Definition double_free (l : nat) : mgcl_prog :=
  (FREE l) ;; (FREE l).

(* ================================================================= *)
(** ** Helper: heap_remove on a singleton yields the empty heap       *)
(* ================================================================= *)

Lemma heap_remove_singleton_empty (l v : nat) :
  heap_remove (heap_singleton l v) l = heap_empty.
Proof.
  apply heap_ext. intro a.
  unfold heap_remove, heap_singleton, heap_empty.
  destruct (Nat.eqb a l); reflexivity.
Qed.

(* ================================================================= *)
(** ** Denotation of double_free                                      *)
(* ================================================================= *)

(** On [Ok (heap_singleton l v)], [free(l)] succeeds producing
    [Ok heap_empty], then [free(l)] on [Ok heap_empty] errors
    because [heap_empty l = None]. *)

Lemma double_free_denote (l v : nat) :
  mgcl_denote (double_free l) (Ok (heap_singleton l v)) =
    pset_ret (Er heap_empty).
Proof.
  unfold double_free.
  rewrite mgcl_denote_seq.
  rewrite mgcl_denote_atom.
  (* First free: l is allocated in heap_singleton l v *)
  assert (Hsome : heap_singleton l v l = Some v).
  { unfold heap_singleton. rewrite Nat.eqb_refl. reflexivity. }
  rewrite (mgcl_den_free_ok _ l v Hsome).
  rewrite pset_bind_ret_l.
  (* heap_remove (heap_singleton l v) l = heap_empty *)
  rewrite heap_remove_singleton_empty.
  rewrite mgcl_denote_atom.
  (* Second free: l is not allocated in heap_empty *)
  assert (Hnone : heap_empty l = None).
  { unfold heap_empty. reflexivity. }
  rewrite (mgcl_den_free_er _ l Hnone).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Precondition characterization                                  *)
(* ================================================================= *)

(** Any set satisfying [BiAtom (AOk (SLPointsTo l v))] is exactly
    [{Ok (heap_singleton l v)}]. *)

Lemma ok_pts_is_singleton (l v : nat)
    (m : PSet (err_state Heap)) :
  bi_sat mgcl_atom_sat m (BiAtom (AOk (SLPointsTo l v))) ->
  m = pset_ret (Ok (heap_singleton l v)).
Proof.
  simpl. unfold mgcl_atom_sat, nd_atom_sat.
  intros [[s0 Hne] Hforall].
  apply ensemble_ext. intro s. split.
  - intro Hin.
    specialize (Hforall s Hin).
    destruct s as [h | h].
    + simpl in Hforall. subst h. constructor.
    + simpl in Hforall. contradiction.
  - intro Hin.
    inversion Hin; subst; clear Hin.
    specialize (Hforall s0 Hne).
    destruct s0 as [h0 | h0].
    + simpl in Hforall. subst h0. exact Hne.
    + simpl in Hforall. contradiction.
Qed.

(* ================================================================= *)
(** ** Postcondition satisfaction                                     *)
(* ================================================================= *)

(** [heap_empty] satisfies [SLInvalid l] for any [l]. *)

Lemma heap_empty_invalid (l : nat) :
  sl_sat heap_empty (SLInvalid l).
Proof.
  simpl. unfold heap_empty. reflexivity.
Qed.

(* ================================================================= *)
(** ** Error Reachability                                             *)
(* ================================================================= *)

(** The error state [Er heap_empty] is a member of the outcome set. *)

Lemma double_free_error_reachable (l v : nat) :
  In _ (mgcl_denote (double_free l) (Ok (heap_singleton l v)))
       (Er heap_empty).
Proof.
  rewrite double_free_denote.
  constructor.
Qed.

(* ================================================================= *)
(** ** Under-Approximate OL Triple                                    *)
(* ================================================================= *)

(** ⊨↓ ⟨ok: l ↦ v⟩ free(l); free(l) ⟨er: l ↛⟩

    Starting from any set of ok-states where location [l] holds
    value [v], executing [double_free l] produces an error state
    where [l] is not allocated — witnessing the double-free bug.

    The under-approximate form means: the error outcome with the
    invalid-pointer condition is reachable.  Since [double_free]
    is deterministic, this is in fact the *only* outcome. *)

Theorem double_free_uaf (l v : nat) :
  mgcl_valid_under
    (BiAtom (AOk (SLPointsTo l v)))
    (BiAtom (AEr (SLInvalid l)))
    (double_free l).
Proof.
  intros m Hpre.
  (* The precondition forces m = {Ok (heap_singleton l v)} *)
  rewrite (ok_pts_is_singleton l v m Hpre).
  unfold collect. rewrite pset_bind_ret_l.
  rewrite double_free_denote.
  (* Need: {Er heap_empty} ⊨ (er: l ↛) ⊕ ⊤ *)
  simpl.
  exists (pset_ret (Er heap_empty)), pset_empty.
  split.
  - (* pset_union {Er heap_empty} ∅ = {Er heap_empty} *)
    apply pset_union_empty_r.
  - split.
    + (* er: l ↛ *)
      unfold mgcl_atom_sat, nd_atom_sat. split.
      * exists (Er heap_empty). constructor.
      * intros s Hin. inversion Hin; subst.
        simpl. apply heap_empty_invalid.
    + (* ⊤ *)
      exact I.
Qed.

(* ================================================================= *)
(** ** Exact OL Triple                                                *)
(* ================================================================= *)

(** ⊨ ⟨ok: l ↦ v⟩ free(l); free(l) ⟨er: l ↛⟩

    Since [double_free] is deterministic and always errors, the
    exact triple matches the under-approximate one. *)

Theorem double_free_exact (l v : nat) :
  mgcl_valid
    (BiAtom (AOk (SLPointsTo l v)))
    (BiAtom (AEr (SLInvalid l)))
    (double_free l).
Proof.
  intros m Hpre.
  rewrite (ok_pts_is_singleton l v m Hpre).
  unfold collect. rewrite pset_bind_ret_l.
  rewrite double_free_denote.
  (* {Er heap_empty} satisfies (AEr (SLInvalid l)) *)
  simpl. unfold mgcl_atom_sat, nd_atom_sat. split.
  - exists (Er heap_empty). constructor.
  - intros s Hin. inversion Hin; subst.
    simpl. apply heap_empty_invalid.
Qed.

(* ================================================================= *)
(** ** Corollary: Manifest Error                                      *)
(* ================================================================= *)

(** The double-free is a manifest error: freeing twice always
    errors, regardless of the initial value stored at [l]. *)

Corollary double_free_manifest (l : nat) :
  manifest_error (double_free l) (SLInvalid l).
Proof.
  intros sigma.
  destruct (sigma l) eqn:Hl.
  - (* sigma l = Some n: free succeeds, then second free errors on empty *)
    exists (Er (heap_remove sigma l)).
    split.
    + unfold double_free.
      rewrite mgcl_denote_seq, mgcl_denote_atom.
      rewrite (mgcl_den_free_ok _ l n Hl).
      rewrite pset_bind_ret_l, mgcl_denote_atom.
      assert (Hnone : heap_remove sigma l l = None).
      { apply heap_remove_eq. }
      rewrite (mgcl_den_free_er _ l Hnone).
      constructor.
    + exists (heap_remove sigma l).
      split; [reflexivity |].
      simpl. apply heap_remove_eq.
  - (* sigma l = None: first free errors immediately *)
    exists (Er sigma).
    split.
    + unfold double_free.
      rewrite mgcl_denote_seq, mgcl_denote_atom.
      rewrite (mgcl_den_free_er _ l Hl).
      rewrite pset_bind_ret_l, mgcl_denote_atom.
      rewrite mgcl_den_er_propagate.
      constructor.
    + exists sigma.
      split; [reflexivity |].
      simpl. exact Hl.
Qed.

Close Scope mgcl_scope.
