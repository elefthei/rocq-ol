(** * OL/Heap/Lang.v — mGCL Syntax and Error-Aware Powerset Denotation

    Defines the Guarded Command Language with Memory (mGCL) as the
    atomic command type for OL's generic language [ol_prog].  The mGCL
    atoms are heap-manipulating commands (alloc, free, store, load, error)
    with deterministic, error-aware semantics.

    The denotation [mgcl_den] maps each mGCL atom to an error-aware
    powerset function [err_state Heap → PSet (err_state Heap)]:
    - On [Ok h]: performs the heap operation, returning [Ok h'] on
      success or [Er h] when the operation faults (e.g., free of an
      unallocated location, store/load to an unallocated location).
    - On [Er h]: propagates the error unchanged (error propagation).

    The full program denotation [mgcl_denote] is obtained by plugging
    [mgcl_den] into [ol_denote] from [OL/Lang.v].

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5, Appendix B.3 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Heap Require Import Assertion Error.

(* ================================================================= *)
(** ** Heap Operations                                                *)
(* ================================================================= *)

(** Update a heap at address [loc] to hold value [val]. *)
Definition heap_update (h : Heap) (loc val : nat) : Heap :=
  fun a => if Nat.eqb a loc then Some val else h a.

(** Remove (deallocate) address [loc] from the heap. *)
Definition heap_remove (h : Heap) (loc : nat) : Heap :=
  fun a => if Nat.eqb a loc then None else h a.

(* ================================================================= *)
(** ** Heap Operation Lemmas                                          *)
(* ================================================================= *)

Section HeapOpLemmas.

  (** [heap_update] sets the target address. *)
  Lemma heap_update_eq (h : Heap) (loc val : nat) :
    heap_update h loc val loc = Some val.
  Proof.
    unfold heap_update. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (** [heap_update] preserves other addresses. *)
  Lemma heap_update_neq (h : Heap) (loc val a : nat) :
    a <> loc -> heap_update h loc val a = h a.
  Proof.
    intro Hneq. unfold heap_update.
    destruct (Nat.eqb a loc) eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - reflexivity.
  Qed.

  (** [heap_remove] clears the target address. *)
  Lemma heap_remove_eq (h : Heap) (loc : nat) :
    heap_remove h loc loc = None.
  Proof.
    unfold heap_remove. rewrite Nat.eqb_refl. reflexivity.
  Qed.

  (** [heap_remove] preserves other addresses. *)
  Lemma heap_remove_neq (h : Heap) (loc a : nat) :
    a <> loc -> heap_remove h loc a = h a.
  Proof.
    intro Hneq. unfold heap_remove.
    destruct (Nat.eqb a loc) eqn:E.
    - apply Nat.eqb_eq in E. contradiction.
    - reflexivity.
  Qed.

  (** Updating with the existing value is the identity. *)
  Lemma heap_update_same (h : Heap) (loc val : nat) :
    h loc = Some val -> heap_update h loc val = h.
  Proof.
    intro Heq. apply heap_ext. intro a.
    unfold heap_update.
    destruct (Nat.eqb a loc) eqn:E.
    - apply Nat.eqb_eq in E. subst. symmetry. exact Heq.
    - reflexivity.
  Qed.

  (** Removing from an unallocated address is the identity. *)
  Lemma heap_remove_none (h : Heap) (loc : nat) :
    h loc = None -> heap_remove h loc = h.
  Proof.
    intro Heq. apply heap_ext. intro a.
    unfold heap_remove.
    destruct (Nat.eqb a loc) eqn:E.
    - apply Nat.eqb_eq in E. subst. symmetry. exact Heq.
    - reflexivity.
  Qed.

  (** [heap_update] is idempotent at the same address. *)
  Lemma heap_update_overwrite (h : Heap) (loc v1 v2 : nat) :
    heap_update (heap_update h loc v1) loc v2 = heap_update h loc v2.
  Proof.
    apply heap_ext. intro a.
    unfold heap_update.
    destruct (Nat.eqb a loc); reflexivity.
  Qed.

  (** [heap_update] at different addresses commutes. *)
  Lemma heap_update_comm (h : Heap) (l1 l2 v1 v2 : nat) :
    l1 <> l2 ->
    heap_update (heap_update h l1 v1) l2 v2 =
    heap_update (heap_update h l2 v2) l1 v1.
  Proof.
    intro Hneq. apply heap_ext. intro a.
    unfold heap_update.
    destruct (Nat.eqb a l2) eqn:E2, (Nat.eqb a l1) eqn:E1; try reflexivity.
    apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2.
    subst. contradiction.
  Qed.

End HeapOpLemmas.

(* ================================================================= *)
(** ** mGCL Atomic Command Syntax                                     *)
(* ================================================================= *)

(** The atomic commands of the Guarded Command Language with Memory,
    adapted for the simplified heap-only model (expressions are literal
    [nat] values).

    Syntax from the paper (Section 5):
    [c ∈ mGCL ::= alloc(loc,val) | free(loc) | store(loc,val)
                 | load(loc) | error]

    Note: [assume e] and [x := e] from the paper's full mGCL are
    part of the GCL base language and would be modeled as separate
    atom types or program combinators.  Here we focus on the heap-
    and error-specific commands. *)

Inductive mgcl_atom : Type :=
  | MAlloc (loc val : nat)          (** allocate [loc] with value [val] *)
  | MFree  (loc : nat)              (** free location [loc] *)
  | MStore (loc val : nat)          (** [[loc] ← val] — store to heap *)
  | MLoad  (loc : nat)              (** [x ← [loc]] — load from heap *)
  | MError                          (** [error()] — immediate fault *)
  .

(** mGCL programs are OL programs with mGCL atoms. *)
Definition mgcl_prog : Type := ol_prog mgcl_atom.

(* ================================================================= *)
(** ** Error-Aware Powerset Denotation for Atoms                      *)
(* ================================================================= *)

(** [mgcl_den c s] gives the set of error-tagged states reachable
    from [s] by executing the atomic mGCL command [c].

    Error propagation: if [s = Er h], the error is forwarded
    unchanged — no atomic command can recover from an error.

    On [s = Ok h]:
    - [MAlloc loc val]: always succeeds, sets [h(loc) := val]
    - [MFree loc]:  Ok if [h(loc) = Some _] (sets to None);
                    Er if [h(loc) = None] (double-free / use-after-free)
    - [MStore loc val]: Ok if [h(loc) = Some _] (updates value);
                        Er if [h(loc) = None] (store to freed location)
    - [MLoad loc]: Ok if [h(loc) = Some _] (heap unchanged);
                   Er if [h(loc) = None] (load from freed location)
    - [MError]:    always produces [Er h]

    Each atom is deterministic: it produces exactly one outcome.
    This matches the paper's observation that mGCL atoms are
    deterministic and can be embedded in any outer monad. *)

Definition mgcl_den (c : mgcl_atom)
    (s : err_state Heap) : PSet (err_state Heap) :=
  match s with
  | Er h => pset_ret (Er h)
  | Ok h =>
    match c with
    | MAlloc loc val => pset_ret (Ok (heap_update h loc val))
    | MFree loc =>
        match h loc with
        | Some _ => pset_ret (Ok (heap_remove h loc))
        | None   => pset_ret (Er h)
        end
    | MStore loc val =>
        match h loc with
        | Some _ => pset_ret (Ok (heap_update h loc val))
        | None   => pset_ret (Er h)
        end
    | MLoad loc =>
        match h loc with
        | Some _ => pset_ret (Ok h)
        | None   => pset_ret (Er h)
        end
    | MError => pset_ret (Er h)
    end
  end.

(* ================================================================= *)
(** ** Full Program Denotation                                        *)
(* ================================================================= *)

(** [mgcl_denote C s] gives the set of error-tagged states reachable
    from [s] by executing program [C], using [ol_denote] with
    [mgcl_den] as the atomic denotation.

    This is the composition of the outer OL language semantics
    (abort, skip, seq, choice, star) with the inner mGCL error-
    aware heap semantics.  It matches the paper's two-monad
    composition: outer monad [M] (here: powerset) composed with
    the error monad [E + −]. *)

Definition mgcl_denote (C : mgcl_prog)
    : err_state Heap -> PSet (err_state Heap) :=
  ol_denote mgcl_den C.

(* ================================================================= *)
(** ** Atomic Satisfaction for the Error-Heap Model                   *)
(* ================================================================= *)

(** [mgcl_atom_sat S a] lifts SL satisfaction through the error monad
    and the nondeterministic powerset to define when a set of error-
    tagged heap states satisfies an error-tagged SL assertion.

    This is the composition:
    [nd_atom_sat ∘ err_atom_sat ∘ sl_sat]

    Used to instantiate the BI assertion logic ([bi_sat]) for heap
    programs with errors.  An [AOk p] assertion requires all states
    in [S] to be [Ok] and satisfy [p]; an [AEr q] assertion requires
    all states to be [Er] and satisfy [q]. *)

Definition mgcl_atom_sat
    : PSet (err_state Heap) -> err_assert sl_assert -> Prop :=
  fun S a => nd_atom_sat S (fun s => err_atom_sat sl_sat s a).

(* ================================================================= *)
(** ** Error Propagation                                              *)
(* ================================================================= *)

Section ErrorPropagation.

  (** Every mGCL atom propagates errors unchanged. *)
  Lemma mgcl_den_er_propagate : forall (c : mgcl_atom) (h : Heap),
    mgcl_den c (Er h) = pset_ret (Er h).
  Proof. intros c h. destruct c; reflexivity. Qed.

  (** Atoms are deterministic: they always produce a singleton set. *)
  Lemma mgcl_den_singleton : forall (c : mgcl_atom) (s : err_state Heap),
    exists s', mgcl_den c s = pset_ret s'.
  Proof.
    intros c s. destruct s as [h | h].
    - (* Ok h *)
      destruct c as [loc val | loc | loc val | loc | ].
      + exists (Ok (heap_update h loc val)). reflexivity.
      + simpl. destruct (h loc) eqn:E.
        * exists (Ok (heap_remove h loc)). reflexivity.
        * exists (Er h). reflexivity.
      + simpl. destruct (h loc) eqn:E.
        * exists (Ok (heap_update h loc val)). reflexivity.
        * exists (Er h). reflexivity.
      + simpl. destruct (h loc) eqn:E.
        * exists (Ok h). reflexivity.
        * exists (Er h). reflexivity.
      + exists (Er h). reflexivity.
    - (* Er h *)
      exists (Er h). reflexivity.
  Qed.

End ErrorPropagation.

(* ================================================================= *)
(** ** Denotation Unfolding Lemmas                                    *)
(* ================================================================= *)

Section DenotationLemmas.

  (** [MAlloc] always succeeds. *)
  Lemma mgcl_den_alloc (h : Heap) (loc val : nat) :
    mgcl_den (MAlloc loc val) (Ok h) =
      pset_ret (Ok (heap_update h loc val)).
  Proof. reflexivity. Qed.

  (** [MFree] on an allocated location succeeds. *)
  Lemma mgcl_den_free_ok (h : Heap) (loc : nat) (v : nat) :
    h loc = Some v ->
    mgcl_den (MFree loc) (Ok h) = pset_ret (Ok (heap_remove h loc)).
  Proof.
    intro Hsome. simpl. rewrite Hsome. reflexivity.
  Qed.

  (** [MFree] on an unallocated location errors. *)
  Lemma mgcl_den_free_er (h : Heap) (loc : nat) :
    h loc = None ->
    mgcl_den (MFree loc) (Ok h) = pset_ret (Er h).
  Proof.
    intro Hnone. simpl. rewrite Hnone. reflexivity.
  Qed.

  (** [MStore] on an allocated location succeeds. *)
  Lemma mgcl_den_store_ok (h : Heap) (loc val : nat) (v : nat) :
    h loc = Some v ->
    mgcl_den (MStore loc val) (Ok h) =
      pset_ret (Ok (heap_update h loc val)).
  Proof.
    intro Hsome. simpl. rewrite Hsome. reflexivity.
  Qed.

  (** [MStore] on an unallocated location errors. *)
  Lemma mgcl_den_store_er (h : Heap) (loc : nat) (val : nat) :
    h loc = None ->
    mgcl_den (MStore loc val) (Ok h) = pset_ret (Er h).
  Proof.
    intro Hnone. simpl. rewrite Hnone. reflexivity.
  Qed.

  (** [MLoad] on an allocated location succeeds (heap unchanged). *)
  Lemma mgcl_den_load_ok (h : Heap) (loc : nat) (v : nat) :
    h loc = Some v ->
    mgcl_den (MLoad loc) (Ok h) = pset_ret (Ok h).
  Proof.
    intro Hsome. simpl. rewrite Hsome. reflexivity.
  Qed.

  (** [MLoad] on an unallocated location errors. *)
  Lemma mgcl_den_load_er (h : Heap) (loc : nat) :
    h loc = None ->
    mgcl_den (MLoad loc) (Ok h) = pset_ret (Er h).
  Proof.
    intro Hnone. simpl. rewrite Hnone. reflexivity.
  Qed.

  (** [MError] always produces an error. *)
  Lemma mgcl_den_error (h : Heap) :
    mgcl_den MError (Ok h) = pset_ret (Er h).
  Proof. reflexivity. Qed.

End DenotationLemmas.

(* ================================================================= *)
(** ** Full Program Denotation Lemmas                                 *)
(* ================================================================= *)

Section ProgramLemmas.

  (** [⟦𝟎⟧(s) = ∅] — abort produces no outcomes. *)
  Lemma mgcl_denote_zero (s : err_state Heap) :
    mgcl_denote OLZero s = pset_empty.
  Proof. reflexivity. Qed.

  (** [⟦𝟏⟧(s) = {s}] — skip returns the input unchanged. *)
  Lemma mgcl_denote_one (s : err_state Heap) :
    mgcl_denote OLOne s = pset_ret s.
  Proof. reflexivity. Qed.

  (** Sequential composition unfolds to bind. *)
  Lemma mgcl_denote_seq (C1 C2 : mgcl_prog) (s : err_state Heap) :
    mgcl_denote (OLSeq C1 C2) s =
      pset_bind (mgcl_denote C1 s) (mgcl_denote C2).
  Proof. reflexivity. Qed.

  (** Nondeterministic choice unfolds to union. *)
  Lemma mgcl_denote_plus (C1 C2 : mgcl_prog) (s : err_state Heap) :
    mgcl_denote (OLPlus C1 C2) s =
      pset_union (mgcl_denote C1 s) (mgcl_denote C2 s).
  Proof. reflexivity. Qed.

  (** Kleene star unfolds to the reflexive-transitive closure. *)
  Lemma mgcl_denote_star (C : mgcl_prog) (s : err_state Heap) :
    mgcl_denote (OLStar C) s = star_set (mgcl_denote C) s.
  Proof. reflexivity. Qed.

  (** Atomic command unfolds to [mgcl_den]. *)
  Lemma mgcl_denote_atom (c : mgcl_atom) (s : err_state Heap) :
    mgcl_denote (OLAtom c) s = mgcl_den c s.
  Proof. reflexivity. Qed.

End ProgramLemmas.

(* ================================================================= *)
(** ** Error Propagation for Sequences                                *)
(* ================================================================= *)

Section SeqErrorPropagation.

  (** If an atom produces an error, sequencing with any program
      preserves that error. *)
  Lemma mgcl_seq_atom_er (c : mgcl_atom) (C : mgcl_prog)
      (h : Heap) (s' : err_state Heap) :
    mgcl_den c (Ok h) = pset_ret (Er h) ->
    In _ (mgcl_denote (OLSeq (OLAtom c) C) (Ok h)) s' ->
    In _ (mgcl_denote C (Er h)) s'.
  Proof.
    intros Hden Hin.
    unfold mgcl_denote, ol_denote in Hin. fold (ol_denote mgcl_den C) in Hin.
    unfold pset_bind, In in Hin.
    destruct Hin as [t [Hc Ht]].
    rewrite Hden in Hc.
    unfold pset_ret in Hc. inversion Hc; subst.
    fold (mgcl_denote C) in Ht.
    exact Ht.
  Qed.

  (** An error state in a sequence propagates through all subsequent
      atoms via error propagation.  For a single atom: *)
  Lemma mgcl_atom_seq_er_propagate (c : mgcl_atom) (h : Heap) :
    mgcl_denote (OLAtom c) (Er h) = pset_ret (Er h).
  Proof.
    unfold mgcl_denote, ol_denote.
    apply mgcl_den_er_propagate.
  Qed.

End SeqErrorPropagation.

(* ================================================================= *)
(** ** Collecting Semantics for mGCL                                  *)
(* ================================================================= *)

(** The collecting extension lifts [mgcl_denote C] from
    [err_state Heap → PSet (err_state Heap)] to
    [PSet (err_state Heap) → PSet (err_state Heap)].

    This is used in the OL triple definition. *)

Definition mgcl_collect (C : mgcl_prog)
    : PSet (err_state Heap) -> PSet (err_state Heap) :=
  collect (mgcl_denote C).

(** Collecting over the empty set yields the empty set. *)
Lemma mgcl_collect_empty (C : mgcl_prog) :
  mgcl_collect C pset_empty = pset_empty.
Proof. unfold mgcl_collect. apply collect_empty. Qed.

(** Collecting distributes over union. *)
Lemma mgcl_collect_union (C : mgcl_prog)
    (S1 S2 : PSet (err_state Heap)) :
  mgcl_collect C (pset_union S1 S2) =
    pset_union (mgcl_collect C S1) (mgcl_collect C S2).
Proof. unfold mgcl_collect. apply collect_union. Qed.

(** Collecting a singleton is just the denotation. *)
Lemma mgcl_collect_ret (C : mgcl_prog) (s : err_state Heap) :
  mgcl_collect C (pset_ret s) = mgcl_denote C s.
Proof. unfold mgcl_collect. apply collect_ret. Qed.

(* ================================================================= *)
(** ** OL Triple Validity for mGCL Programs                          *)
(* ================================================================= *)

(** [mgcl_valid φ C ψ] asserts that for every set [m] of error-tagged
    heap states satisfying [φ], the collected outcomes of executing [C]
    satisfy [ψ].

    This is the concrete instantiation of [ol_valid] for the error-
    heap model. *)

Definition mgcl_valid
    (phi psi : bi_formula (err_assert sl_assert))
    (C : mgcl_prog) : Prop :=
  ol_valid mgcl_atom_sat (mgcl_denote C) phi psi.

(** Under-approximate validity for mGCL. *)
Definition mgcl_valid_under
    (phi psi : bi_formula (err_assert sl_assert))
    (C : mgcl_prog) : Prop :=
  ol_valid_under mgcl_atom_sat (mgcl_denote C) phi psi.

(** Partial correctness validity for mGCL. *)
Definition mgcl_valid_pc
    (phi psi : bi_formula (err_assert sl_assert))
    (C : mgcl_prog) : Prop :=
  ol_valid_pc mgcl_atom_sat (mgcl_denote C) phi psi.

(* ================================================================= *)
(** ** Syntactic Sugar                                                *)
(* ================================================================= *)

(** [mgcl_malloc loc val] models [x := malloc()] from the paper:
    nondeterministically allocate ([MAlloc]) or produce null (modeled
    as [MError] since null dereference is an immediate fault).

    In the paper: [x := malloc() ≜ (x := alloc()) + (x := null)]
    Here: [malloc loc val ≜ alloc(loc,val) + error()] *)

Definition mgcl_malloc (loc val : nat) : mgcl_prog :=
  OLPlus (OLAtom (MAlloc loc val)) (OLAtom MError).

(** [mgcl_malloc] produces both ok and error outcomes. *)
Lemma mgcl_malloc_denote (h : Heap) (loc val : nat) :
  mgcl_denote (mgcl_malloc loc val) (Ok h) =
    pset_union (pset_ret (Ok (heap_update h loc val)))
               (pset_ret (Er h)).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Notation                                                       *)
(* ================================================================= *)

Declare Scope mgcl_scope.
Delimit Scope mgcl_scope with mgcl.

Notation "'ALLOC' loc val" := (OLAtom (MAlloc loc val))
  (at level 0, loc at level 0, val at level 0) : mgcl_scope.
Notation "'FREE' loc" := (OLAtom (MFree loc))
  (at level 0, loc at level 0) : mgcl_scope.
Notation "'STORE' loc val" := (OLAtom (MStore loc val))
  (at level 0, loc at level 0, val at level 0) : mgcl_scope.
Notation "'LOAD' loc" := (OLAtom (MLoad loc))
  (at level 0, loc at level 0) : mgcl_scope.
Notation "'ERROR'" := (OLAtom MError) : mgcl_scope.
Notation "'SKIP'" := OLOne : mgcl_scope.
Notation "'ABORT'" := OLZero : mgcl_scope.
Notation "C1 ';;' C2" := (OLSeq C1 C2)
  (at level 60, right associativity) : mgcl_scope.
Notation "C1 '⊕ₘ' C2" := (OLPlus C1 C2)
  (at level 50, left associativity) : mgcl_scope.
Notation "'MALLOC' loc val" := (mgcl_malloc loc val)
  (at level 0, loc at level 0, val at level 0) : mgcl_scope.
