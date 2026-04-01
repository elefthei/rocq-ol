(** * OL/Heap/test_lang.v — Tests for mGCL Syntax and Denotation *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Heap Require Import Assertion Error Lang.

(* ================================================================= *)
(** ** Test 1: Basic Atom Denotations                                 *)
(* ================================================================= *)

(** Alloc on empty heap produces the expected singleton heap. *)
Example test_alloc_empty :
  In _ (mgcl_den (MAlloc 1 42) (Ok heap_empty))
       (Ok (heap_update heap_empty 1 42)).
Proof.
  simpl. constructor.
Qed.

(** Free on allocated location succeeds. *)
Example test_free_ok :
  let h := heap_singleton 1 42 in
  In _ (mgcl_den (MFree 1) (Ok h))
       (Ok (heap_remove h 1)).
Proof.
  simpl. unfold heap_singleton. simpl.
  constructor.
Qed.

(** Free on unallocated location errors. *)
Example test_free_er :
  In _ (mgcl_den (MFree 1) (Ok heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(** Store on allocated location succeeds. *)
Example test_store_ok :
  let h := heap_singleton 1 42 in
  In _ (mgcl_den (MStore 1 99) (Ok h))
       (Ok (heap_update h 1 99)).
Proof.
  simpl. unfold heap_singleton. simpl. constructor.
Qed.

(** Store on unallocated location errors. *)
Example test_store_er :
  In _ (mgcl_den (MStore 1 99) (Ok heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(** Load on allocated location succeeds. *)
Example test_load_ok :
  let h := heap_singleton 1 42 in
  In _ (mgcl_den (MLoad 1) (Ok h))
       (Ok h).
Proof.
  simpl. unfold heap_singleton. simpl. constructor.
Qed.

(** Load on unallocated location errors. *)
Example test_load_er :
  In _ (mgcl_den (MLoad 1) (Ok heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(** Error always faults. *)
Example test_error :
  In _ (mgcl_den MError (Ok heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(* ================================================================= *)
(** ** Test 2: Error Propagation                                      *)
(* ================================================================= *)

(** Alloc on an error state propagates the error. *)
Example test_er_propagate_alloc :
  In _ (mgcl_den (MAlloc 1 42) (Er heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(** Free on an error state propagates the error. *)
Example test_er_propagate_free :
  In _ (mgcl_den (MFree 1) (Er heap_empty))
       (Er heap_empty).
Proof.
  simpl. constructor.
Qed.

(* ================================================================= *)
(** ** Test 3: Program Composition                                    *)
(* ================================================================= *)

(** Alloc then store: allocation at loc 1, then store 99. *)
Example test_alloc_then_store :
  let prog := OLSeq (OLAtom (MAlloc 1 0)) (OLAtom (MStore 1 99)) in
  In _ (mgcl_denote prog (Ok heap_empty))
       (Ok (heap_update (heap_update heap_empty 1 0) 1 99)).
Proof.
  simpl. unfold pset_bind, In.
  exists (Ok (heap_update heap_empty 1 0)).
  split.
  - constructor.
  - simpl. unfold heap_update at 1. simpl. constructor.
Qed.

(** Alloc then free: allocation at loc 1, then free loc 1. *)
Example test_alloc_then_free :
  let prog := OLSeq (OLAtom (MAlloc 1 42)) (OLAtom (MFree 1)) in
  In _ (mgcl_denote prog (Ok heap_empty))
       (Ok (heap_remove (heap_update heap_empty 1 42) 1)).
Proof.
  simpl. unfold pset_bind, In.
  exists (Ok (heap_update heap_empty 1 42)).
  split.
  - constructor.
  - simpl. unfold heap_update at 1. simpl. constructor.
Qed.

(* ================================================================= *)
(** ** Test 4: Nondeterministic Choice (malloc)                       *)
(* ================================================================= *)

(** malloc produces both ok and error outcomes. *)
Example test_malloc_ok :
  In _ (mgcl_denote (mgcl_malloc 1 0) (Ok heap_empty))
       (Ok (heap_update heap_empty 1 0)).
Proof.
  simpl. apply Union_introl. constructor.
Qed.

Example test_malloc_er :
  In _ (mgcl_denote (mgcl_malloc 1 0) (Ok heap_empty))
       (Er heap_empty).
Proof.
  simpl. apply Union_intror. constructor.
Qed.

(* ================================================================= *)
(** ** Test 5: Double Free (Use-After-Free Error)                     *)
(* ================================================================= *)

(** Double free produces an error on the second free. *)
Example test_double_free :
  let h := heap_singleton 1 42 in
  let prog := OLSeq (OLAtom (MFree 1)) (OLAtom (MFree 1)) in
  In _ (mgcl_denote prog (Ok h))
       (Er (heap_remove h 1)).
Proof.
  simpl. unfold pset_bind, In.
  unfold heap_singleton. simpl.
  exists (Ok (heap_remove (fun a => if (a =? 1)%nat then Some 42 else None) 1)).
  split.
  - constructor.
  - simpl. unfold heap_remove at 1. simpl. constructor.
Qed.

(* ================================================================= *)
(** ** Test 6: Kleene Star — Skip (zero iterations)                   *)
(* ================================================================= *)

(** Star of any program includes the starting state (zero iterations). *)
Example test_star_refl :
  In _ (mgcl_denote (OLStar (OLAtom (MAlloc 1 42))) (Ok heap_empty))
       (Ok heap_empty).
Proof.
  simpl. apply star_refl.
Qed.

(* ================================================================= *)
(** ** Test 7: Collecting Semantics                                   *)
(* ================================================================= *)

(** Collecting skip over a singleton is the singleton. *)
Example test_collect_skip :
  mgcl_collect OLOne (pset_ret (Ok heap_empty)) =
    pset_ret (Ok heap_empty).
Proof.
  unfold mgcl_collect. apply collect_ret.
Qed.

(** Collecting abort over any set is empty. *)
Example test_collect_abort :
  mgcl_collect OLZero (pset_ret (Ok heap_empty)) = pset_empty.
Proof.
  unfold mgcl_collect, collect, pset_bind.
  apply ensemble_ext. intro s. split.
  - intros [t [Ht Hd]]. simpl in Hd. inversion Hd.
  - intro H. inversion H.
Qed.

(* ================================================================= *)
(** ** Test 8: Atom Satisfaction                                      *)
(* ================================================================= *)

(** A singleton ok set satisfies an AOk assertion. *)
Example test_atom_sat_ok :
  let h := heap_singleton 1 42 in
  mgcl_atom_sat (pset_ret (Ok h)) (AOk (SLPointsTo 1 42)).
Proof.
  unfold mgcl_atom_sat, nd_atom_sat. split.
  - exists (Ok (heap_singleton 1 42)). constructor.
  - intros s Hin. inversion Hin; subst.
    simpl. reflexivity.
Qed.

(** A singleton er set satisfies an AEr assertion. *)
Example test_atom_sat_er :
  mgcl_atom_sat (pset_ret (Er heap_empty)) (AEr SLEmp).
Proof.
  unfold mgcl_atom_sat, nd_atom_sat. split.
  - exists (Er heap_empty). constructor.
  - intros s Hin. inversion Hin; subst.
    simpl. reflexivity.
Qed.

(* ================================================================= *)
(** ** Test 9: Heap Operation Properties                              *)
(* ================================================================= *)

(** heap_update followed by heap_remove at the same location
    is the same as heap_remove on the original. *)
Example test_update_remove :
  forall h loc val,
    heap_remove (heap_update h loc val) loc = heap_remove h loc.
Proof.
  intros h loc val. apply heap_ext. intro a.
  unfold heap_remove, heap_update.
  destruct (Nat.eqb a loc); reflexivity.
Qed.
