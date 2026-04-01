(** * examples/OL/PushBack.v — Use-After-Free Proof (Figure 8)

    Verifies the push_back use-after-free example from Figure 8 of the
    Outcome Logic paper.  A vector with a single-cell buffer is modeled
    with three heap locations:

    - [v_addr] = 0 : the vector header, stores a pointer to the buffer
    - [a_addr] = 1 : the original buffer
    - [b_addr] = 2 : the new buffer (after reallocation)

    The [push_back] operation nondeterministically either reallocates
    the buffer (free old + alloc new + update pointer) or does nothing.
    A subsequent write to the old buffer address [a_addr] causes a
    use-after-free error in the reallocation case.

    **Theorem [push_back_uaf]** (under-approximate triple):

        ⊨↓ ⟨ok: v↦a ∗ a↦−⟩ main ⟨er: a↛ ∗ true⟩

    This witnesses that an error outcome with an invalid pointer is
    reachable, demonstrating the use-after-free bug.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5.5, Figure 8 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Heap Require Import Assertion Error Lang Rules.

(* ================================================================= *)
(** ** Concrete Addresses                                             *)
(* ================================================================= *)

Definition v_addr : nat := 0.
Definition a_addr : nat := 1.
Definition b_addr : nat := 2.
Definition new_val : nat := 42.

(* ================================================================= *)
(** ** Program Definition (Figure 8)                                  *)
(* ================================================================= *)

(** The program from the paper, using concrete addresses:

    push_back(v):
      ( free(a); alloc(b, val); store(v, b) ) + skip

    main():
      push_back(v);
      store(a, 1)     ← use-after-free if realloc happened *)

Open Scope mgcl_scope.

(** Reallocation branch: free old buffer, alloc new, update pointer. *)
Definition push_back_realloc : mgcl_prog :=
  FREE a_addr ;; ALLOC b_addr new_val ;; STORE v_addr b_addr.

(** push_back: nondeterministically reallocates or does nothing. *)
Definition push_back_prog : mgcl_prog :=
  push_back_realloc ⊕ₘ SKIP.

(** main: call push_back then write to the (possibly stale) pointer. *)
Definition main_prog : mgcl_prog :=
  push_back_prog ;; STORE a_addr 1.

Close Scope mgcl_scope.

(* ================================================================= *)
(** ** Helper: Singleton Absorption into a Superset                   *)
(* ================================================================= *)

Lemma pset_union_singleton_absorb {A : Type} (x : A) (S : PSet A) :
  In _ S x -> pset_union (pset_ret x) S = S.
Proof.
  intro Hin. apply ensemble_ext. intro y. split.
  - intro HU. inversion HU; subst.
    + inversion H; subst. exact Hin.
    + exact H.
  - intro HS. apply Union_intror. exact HS.
Qed.

(* ================================================================= *)
(** ** Denotation Computation                                        *)
(* ================================================================= *)

(** For any heap of the form [v↦a ∗ a↦val0], the full program
    produces exactly two outcomes: an error (from realloc + stale
    write) and a success (from skip + valid write). *)

Lemma main_denote (val0 : nat) :
  let h := heap_union (heap_singleton v_addr a_addr)
                       (heap_singleton a_addr val0) in
  let h_realloc := heap_update
                     (heap_update (heap_remove h a_addr) b_addr new_val)
                     v_addr b_addr in
  let h_ok := heap_update h a_addr 1 in
  mgcl_denote main_prog (Ok h) =
    pset_union (pset_ret (Er h_realloc)) (pset_ret (Ok h_ok)).
Proof.
  intros h h_realloc h_ok.

  assert (Ha : h a_addr = Some val0).
  { subst h. unfold heap_union, heap_singleton, v_addr, a_addr. reflexivity. }

  assert (Hva : (heap_update (heap_remove h a_addr) b_addr new_val) v_addr
                = Some a_addr).
  { unfold v_addr, b_addr.
    rewrite heap_update_neq; [| discriminate].
    unfold a_addr. rewrite heap_remove_neq; [| discriminate].
    subst h. unfold heap_union, heap_singleton, v_addr. reflexivity. }

  assert (Hna : h_realloc a_addr = None).
  { subst h_realloc. unfold v_addr, a_addr.
    rewrite heap_update_neq; [| discriminate].
    unfold b_addr. rewrite heap_update_neq; [| discriminate].
    apply heap_remove_eq. }

  unfold main_prog, push_back_prog, push_back_realloc.
  unfold mgcl_denote, ol_denote. fold (ol_denote mgcl_den).

  (* Compute MFree a_addr on Ok h *)
  change (mgcl_den (MFree a_addr) (Ok h)) with
    (match h a_addr with
     | Some _ => pset_ret (Ok (heap_remove h a_addr))
     | None   => pset_ret (Er h) end).
  rewrite Ha.
  repeat rewrite pset_bind_ret_l.

  (* Compute MAlloc b_addr new_val *)
  change (mgcl_den (MAlloc b_addr new_val) (Ok (heap_remove h a_addr))) with
    (pset_ret (Ok (heap_update (heap_remove h a_addr) b_addr new_val))).
  repeat rewrite pset_bind_ret_l.

  (* Compute MStore v_addr b_addr *)
  change (mgcl_den (MStore v_addr b_addr)
          (Ok (heap_update (heap_remove h a_addr) b_addr new_val))) with
    (match (heap_update (heap_remove h a_addr) b_addr new_val) v_addr with
     | Some _ => pset_ret (Ok (heap_update (heap_update (heap_remove h a_addr) b_addr new_val) v_addr b_addr))
     | None   => pset_ret (Er (heap_update (heap_remove h a_addr) b_addr new_val)) end).
  rewrite Hva.
  repeat rewrite pset_bind_ret_l.
  fold h_realloc.

  (* Distribute bind over union *)
  rewrite pset_bind_union.
  repeat rewrite pset_bind_ret_l.

  (* Compute MStore a_addr 1 on the realloc heap (error) *)
  change (mgcl_den (MStore a_addr 1) (Ok h_realloc)) with
    (match h_realloc a_addr with
     | Some _ => pset_ret (Ok (heap_update h_realloc a_addr 1))
     | None   => pset_ret (Er h_realloc) end).
  rewrite Hna.

  (* Compute MStore a_addr 1 on the original heap (success) *)
  change (mgcl_den (MStore a_addr 1) (Ok h)) with
    (match h a_addr with
     | Some _ => pset_ret (Ok (heap_update h a_addr 1))
     | None   => pset_ret (Er h) end).
  rewrite Ha.
  fold h_ok.
  reflexivity.
Qed.

(** Extract the error-reachability fact and the invalid-pointer property. *)

Lemma main_reaches_error (val0 : nat) :
  let h := heap_union (heap_singleton v_addr a_addr)
                       (heap_singleton a_addr val0) in
  let h_err := heap_update
                 (heap_update (heap_remove h a_addr) b_addr new_val)
                 v_addr b_addr in
  In _ (mgcl_denote main_prog (Ok h)) (Er h_err) /\
  h_err a_addr = None.
Proof.
  cbv zeta.
  rewrite (main_denote val0).
  split.
  - apply Union_introl. constructor.
  - unfold v_addr, a_addr.
    rewrite heap_update_neq; [| discriminate].
    unfold b_addr. rewrite heap_update_neq; [| discriminate].
    apply heap_remove_eq.
Qed.

(* ================================================================= *)
(** ** SL Satisfaction: Error Heap Has Invalid Pointer                *)
(* ================================================================= *)

(** Any heap where [a_addr] is unallocated satisfies [a↛ ∗ true]. *)

Lemma invalid_star_true (h : Heap) :
  h a_addr = None ->
  sl_sat h (SLStar (SLInvalid a_addr) SLTrue).
Proof.
  intro Hnone. simpl.
  exists heap_empty, h.
  split; [apply heap_disjoint_empty_l |].
  split; [apply heap_union_empty_l |].
  split; [simpl; reflexivity | exact I].
Qed.

(* ================================================================= *)
(** ** Main Theorem: Use-After-Free (Under-Approximate Triple)       *)
(* ================================================================= *)

(** ⊨↓ ⟨ok: v↦a ∗ a↦−⟩ main ⟨er: a↛ ∗ true⟩

    Starting from any set of ok-states where the vector [v] points to
    buffer [a] (which holds some value), executing [main_prog] can
    produce an error state where [a] is freed — witnessing the
    use-after-free bug.

    The under-approximate form means: some outcomes are errors with
    the dangling-pointer condition.  Other outcomes (from the skip
    branch) may succeed, but we don't constrain them. *)

Theorem push_back_uaf :
  mgcl_valid_under
    (BiAtom (AOk (SLStar (SLPointsTo v_addr a_addr) (SLPointsAny a_addr))))
    (BiAtom (AEr (SLStar (SLInvalid a_addr) SLTrue)))
    main_prog.
Proof.
  unfold mgcl_valid_under, ol_valid_under, ol_valid.
  intros m Hpre.

  (* Extract precondition: m is non-empty, all states are Ok h
     where h = heap_union (heap_singleton v a) (heap_singleton a val0) *)
  simpl in Hpre. destruct Hpre as [[s0 Hs0] Hforall].
  specialize (Hforall s0 Hs0) as Hs0_sat.
  destruct s0 as [h0 | h0]; [| simpl in Hs0_sat; contradiction].
  simpl in Hs0_sat.
  destruct Hs0_sat as [h1 [h2 [Hdisj [Hunion [Hpt Hany]]]]].
  simpl in Hpt. subst h1.
  destruct Hany as [val0 Hh2]. subst h2.

  (* h0 = heap_union (heap_singleton v_addr a_addr) (heap_singleton a_addr val0) *)
  symmetry in Hunion. subst h0.
  set (h := heap_union (heap_singleton v_addr a_addr)
                        (heap_singleton a_addr val0)).

  (* Get error outcome from the denotation *)
  destruct (main_reaches_error val0) as [Herr_in Herr_none].
  fold h in Herr_in, Herr_none.

  set (h_err := heap_update
                  (heap_update (heap_remove h a_addr) b_addr new_val)
                  v_addr b_addr) in *.

  (* Er h_err is in the collecting extension (because Ok h ∈ m) *)
  assert (Herr_coll : In _ (collect (mgcl_denote main_prog) m) (Er h_err)).
  { unfold collect, pset_bind, In.
    exists (Ok h). split; [exact Hs0 | exact Herr_in]. }

  (* Build the postcondition: (er: a↛ ∗ true) ⊕ ⊤ *)
  simpl.
  exists (pset_ret (Er h_err)), (collect (mgcl_denote main_prog) m).
  split.

  - (* pset_union {Er h_err} result = result *)
    apply pset_union_singleton_absorb. exact Herr_coll.

  - split.
    + (* {Er h_err} satisfies BiAtom (AEr (SLStar (SLInvalid a_addr) SLTrue)) *)
      simpl. split.
      * exists (Er h_err). constructor.
      * intros s Hs. inversion Hs; subst.
        simpl. apply invalid_star_true. exact Herr_none.
    + (* result satisfies BiTop *)
      exact I.
Qed.

(* ================================================================= *)
(** ** Corollary: Error Reachability (Individual State)               *)
(* ================================================================= *)

Corollary uaf_error_reachable (val0 : nat) :
  let h := heap_union (heap_singleton v_addr a_addr)
                       (heap_singleton a_addr val0) in
  exists s, In _ (mgcl_denote main_prog (Ok h)) s /\
            err_is_er s.
Proof.
  simpl.
  destruct (main_reaches_error val0) as [Hin _].
  eexists. split; [exact Hin | exact I].
Qed.

(** The success state is also reachable (skip path). *)

Lemma uaf_success_reachable (val0 : nat) :
  let h := heap_union (heap_singleton v_addr a_addr)
                       (heap_singleton a_addr val0) in
  exists s, In _ (mgcl_denote main_prog (Ok h)) s /\
            err_is_ok s.
Proof.
  cbv zeta.
  set (h := heap_union (heap_singleton v_addr a_addr)
                        (heap_singleton a_addr val0)).
  exists (Ok (heap_update h a_addr 1)).
  unfold h. rewrite (main_denote val0). fold h.
  split; [apply Union_intror; constructor | exact I].
Qed.
