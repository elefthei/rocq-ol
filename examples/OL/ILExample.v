(** * examples/OL/ILExample.v — Incorrectness Logic Triples

    Demonstrates Incorrectness Logic (IL) triples for the malloc;store
    example and connects them to OL under-approximate triples.

    Main results:
    - [malloc_store_il]: ⊨ [Ok(∅)] malloc;store [Er(∅)]
        Every error state is reachable from the empty heap.
    - [malloc_store_il_success]: ⊨ [Ok(∅)] malloc;store [Ok(l↦1)]
        The success state is also IL-reachable.
    - [malloc_store_il_to_ol_under]: IL triple → OL under-approx triple
        via [il_singleton_implies_ol_under].

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 4 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple Hoare Incorrectness.
From OL.Heap Require Import Assertion Error Lang Rules.

Open Scope mgcl_scope.

(* ================================================================= *)
(** ** Program & Denotation (reused from Malloc.v)                    *)
(* ================================================================= *)

Definition malloc_store (l : nat) : mgcl_prog :=
  (MALLOC l 0) ;; (STORE l 1).

Lemma heap_update_empty (l v : nat) :
  heap_update heap_empty l v = heap_singleton l v.
Proof.
  apply heap_ext. intro a.
  unfold heap_update, heap_empty, heap_singleton.
  destruct (Nat.eqb a l); reflexivity.
Qed.

Lemma malloc_store_denote (l : nat) :
  mgcl_denote (malloc_store l) (Ok heap_empty) =
    pset_union (pset_ret (Ok (heap_singleton l 1)))
               (pset_ret (Er heap_empty)).
Proof.
  unfold malloc_store.
  rewrite mgcl_denote_seq, mgcl_malloc_denote.
  rewrite pset_bind_union, !pset_bind_ret_l, !mgcl_denote_atom.
  rewrite (mgcl_den_store_ok _ l 1 0 (heap_update_eq heap_empty l 0)).
  rewrite heap_update_overwrite.
  unfold mgcl_den. unfold heap_empty at 2.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** IL Triple: Error Reachability                                   *)
(* ================================================================= *)

(** The error state [Er heap_empty] is IL-reachable from [Ok heap_empty]:

        ⊨ [Ok(∅)] malloc(l);[l]←1 [Er(∅)]

    Proof: given τ = Er(∅) (the only Q-state), we exhibit
    σ = Ok(∅) such that Er(∅) ∈ ⟦malloc;store⟧(Ok(∅)). *)

Theorem malloc_store_il (l : nat) :
  il_valid
    (eq (Ok heap_empty))
    (mgcl_denote (malloc_store l))
    (eq (Er heap_empty)).
Proof.
  intros tau Htau. subst tau.
  exists (Ok heap_empty). split.
  - reflexivity.
  - rewrite malloc_store_denote.
    apply Union_intror. constructor.
Qed.

(* ================================================================= *)
(** ** IL Triple: Success Reachability                                 *)
(* ================================================================= *)

(** The success state [Ok(l↦1)] is also IL-reachable:

        ⊨ [Ok(∅)] malloc(l);[l]←1 [Ok(l↦1)]

    IL works for both correctness and incorrectness witnesses. *)

Theorem malloc_store_il_success (l : nat) :
  il_valid
    (eq (Ok heap_empty))
    (mgcl_denote (malloc_store l))
    (eq (Ok (heap_singleton l 1))).
Proof.
  intros tau Htau. subst tau.
  exists (Ok heap_empty). split.
  - reflexivity.
  - rewrite malloc_store_denote.
    apply Union_introl. constructor.
Qed.

(* ================================================================= *)
(** ** IL → OL Under-Approximate Triple                                *)
(* ================================================================= *)

(** By [il_singleton_implies_ol_under], the IL triple lifts to an
    OL under-approximate triple with [nd_atom_sat]:

        ⊨↓ ⟨{Ok(∅)}⟩ malloc;store ⟨{Er(∅)}⟩

    This shows OL subsumes IL for singleton preconditions. *)

Theorem malloc_store_il_to_ol_under (l : nat) :
  ol_valid_under nd_atom_sat
    (mgcl_denote (malloc_store l))
    (BiAtom (eq (Ok heap_empty)))
    (BiAtom (eq (Er heap_empty))).
Proof.
  apply il_singleton_implies_ol_under.
  - intros tau Htau. subst tau.
    rewrite malloc_store_denote.
    apply Union_intror. constructor.
  - exists (Er heap_empty). reflexivity.
Qed.

(* ================================================================= *)
(** ** IL Consequence: Weakened Postcondition                          *)
(* ================================================================= *)

(** IL allows post-STRENGTHENING (not weakening!). Here we show
    that the error-only IL triple follows from a broader one that
    includes all outcomes.

    If [Ok(∅)] C [τ = Er(∅) ∨ τ = Ok(l↦1)], then
    by strengthening (restricting) Q to just errors:
    [Ok(∅)] C [τ = Er(∅)]. *)

Theorem malloc_store_il_both (l : nat) :
  il_valid
    (eq (Ok heap_empty))
    (mgcl_denote (malloc_store l))
    (fun tau => tau = Er heap_empty \/ tau = Ok (heap_singleton l 1)).
Proof.
  intros tau [Htau | Htau]; subst tau.
  - exists (Ok heap_empty). split; [reflexivity |].
    rewrite malloc_store_denote.
    apply Union_intror. constructor.
  - exists (Ok heap_empty). split; [reflexivity |].
    rewrite malloc_store_denote.
    apply Union_introl. constructor.
Qed.

Theorem malloc_store_il_from_consequence (l : nat) :
  il_valid
    (eq (Ok heap_empty))
    (mgcl_denote (malloc_store l))
    (eq (Er heap_empty)).
Proof.
  eapply il_consequence.
  - (* Pre-weakening: eq ⊆ eq (trivial) *)
    intros sigma H. exact H.
  - exact (malloc_store_il_both l).
  - (* Post-strengthening: eq (Er ∅) ⊆ disjunction *)
    intros sigma Heq. subst sigma. left. reflexivity.
Qed.
