(** * examples/OL/IfExample.v — Null-Check with If-Then-Else

    Demonstrates the [if_ol_triple] rule with a null-check pattern:
    a location [l] might be allocated ([l ↦ v]) or unallocated ([l ↛]).
    The program checks whether [l] is allocated and, if so, writes 42;
    otherwise it does nothing.

        if (l allocated)
          then [l] ← 42
          else skip

    OL triple (exact):

        ⊨ ⟨ (ok: l↦v) ⊕ (ok: l↛) ⟩
            if (l alloc?) then store(l,42) else skip
          ⟨ (ok: l↦42) ⊕ (ok: l↛) ⟩

    Both outcomes are fully characterized:
    - If [l] was allocated, the value is updated to 42.
    - If [l] was unallocated, the heap is unchanged. *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Rules Require Import Generic.
From OL.Heap Require Import Assertion Error Lang Rules.

Open Scope mgcl_scope.

(* ================================================================= *)
(** ** The Guard and Program                                          *)
(* ================================================================= *)

(** The guard checks whether location [l] is allocated. *)
Definition is_allocated (l : nat) : Heap -> Prop :=
  fun h => h l <> None.

(** The program: if [l] is allocated, store 42; otherwise skip. *)
Definition null_check (l : nat) : mgcl_prog :=
  ITE (is_allocated l) THEN (STORE l 42) ELSE SKIP.

(* ================================================================= *)
(** ** OL Triple: Exact Specification                                 *)
(* ================================================================= *)

Section NullCheckSpec.
  Variable l : nat.
  Variable v : nat.

  (** [l ↦ v] entails [is_allocated l]. *)
  Lemma pointsto_is_allocated (h : Heap) :
    sl_sat h (SLPointsTo l v) -> is_allocated l h.
  Proof.
    intro Hsat. apply sl_sat_pointsto in Hsat.
    unfold is_allocated. rewrite Hsat.
    unfold heap_singleton.
    rewrite Nat.eqb_refl. discriminate.
  Qed.

  (** [l ↛] entails [¬ is_allocated l]. *)
  Lemma invalid_not_allocated (h : Heap) :
    sl_sat h (SLInvalid l) -> ~ is_allocated l h.
  Proof.
    intro Hsat. apply sl_sat_invalid in Hsat.
    unfold is_allocated. intro Halloc. exact (Halloc Hsat).
  Qed.

  (** The skip branch preserves [l ↛]. *)
  Lemma skip_preserves_invalid :
    mgcl_valid (BiAtom (AOk (SLInvalid l))) (BiAtom (AOk (SLInvalid l))) SKIP.
  Proof.
    apply (@ol_one _ _ _ mgcl_atom_sat mgcl_den).
  Qed.

  (** Main theorem: the null-check program has an exact OL triple. *)
  Theorem null_check_triple :
    mgcl_valid
      (BiOPlus (BiAtom (AOk (SLPointsTo l v))) (BiAtom (AOk (SLInvalid l))))
      (BiOPlus (BiAtom (AOk (SLPointsTo l 42))) (BiAtom (AOk (SLInvalid l))))
      (null_check l).
  Proof.
    unfold null_check.
    apply if_ol_triple.
    - exact pointsto_is_allocated.
    - exact invalid_not_allocated.
    - exact (store_ol_triple l v 42).
    - exact skip_preserves_invalid.
  Qed.

End NullCheckSpec.
