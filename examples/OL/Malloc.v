(** * examples/OL/Malloc.v — Malloc/Store Verification (Equations 4–5)

    Verifies the running example from Section 2 of the Outcome Logic
    paper: the program [x := malloc(); [x] ← 1] produces both a
    successful outcome ([x ↦ 1]) and an error outcome (null / crash).

    In our simplified model (no variable store, addresses are literal
    nats), the program is:

        [malloc(l, 0) ;; store(l, 1)]

    which is [(alloc(l, 0) + skip) ;; store(l, 1)].

    The null branch (skip) leaves the heap unchanged; the subsequent
    store on an unallocated location triggers the error.

    **Equation 4** (exact OL triple):

        ⊨ ⟨ok:emp⟩ malloc(l); [l]←1 ⟨(ok: l↦1) ⊕ (er: emp)⟩

    Both outcomes are fully characterized: the successful branch
    stores 1 at [l]; the error branch preserves the empty heap.

    **Equation 5** (under-approximate OL triple):

        ⊨↓ ⟨ok:emp⟩ malloc(l); [l]←1 ⟨er: emp⟩

    The error outcome is reachable — witnessing the bug.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 2, Equations 4–5 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL Require Import Error.
From OL.Heap Require Import Assertion Lang Rules.

Open Scope mgcl_scope.

(* ================================================================= *)
(** ** The Program                                                    *)
(* ================================================================= *)

(** [malloc_store l] models [x := malloc(); [x] ← 1] for a fixed
    address [l].  [malloc] nondeterministically allocates or returns
    null (skip); [store] writes 1 to [l], erroring on the null branch. *)

Definition malloc_store (l : nat) : mgcl_prog :=
  (MALLOC l 0) ;; (STORE l 1).

(* ================================================================= *)
(** ** Helper: heap_update on empty heap yields singleton             *)
(* ================================================================= *)

Lemma heap_update_empty (l v : nat) :
  heap_update heap_empty l v = heap_singleton l v.
Proof.
  apply heap_ext. intro a.
  unfold heap_update, heap_empty, heap_singleton.
  destruct (Nat.eqb a l); reflexivity.
Qed.

(* ================================================================= *)
(** ** Denotation of malloc_store                                     *)
(* ================================================================= *)

(** On [Ok heap_empty], [malloc_store l] produces exactly two
    outcomes: [Ok (heap_singleton l 1)] and [Er heap_empty].
    The error comes from the null branch: skip leaves the heap empty,
    then store(l,1) fails because l is unallocated. *)

Lemma malloc_store_denote (l : nat) :
  mgcl_denote (malloc_store l) (Ok heap_empty) =
    pset_union (pset_ret (Ok (heap_singleton l 1)))
               (pset_ret (Er heap_empty)).
Proof.
  unfold malloc_store.
  (* Step 1: Decompose sequential composition *)
  rewrite mgcl_denote_seq.
  (* Step 2: Expand malloc to its two branches *)
  rewrite mgcl_malloc_denote.
  (* Step 3: Distribute bind over union, simplify singletons *)
  rewrite pset_bind_union, !pset_bind_ret_l.
  (* Step 4: Unfold mgcl_denote to mgcl_den on atoms *)
  rewrite !mgcl_denote_atom.
  (* Step 5: Ok branch: store succeeds (loc is allocated after alloc) *)
  rewrite (mgcl_den_store_ok _ l 1 0 (heap_update_eq heap_empty l 0)).
  (* Step 6: Double update at same address simplifies *)
  rewrite heap_update_overwrite.
  (* Step 7: Null branch: store on heap_empty fails (l unallocated) *)
  unfold mgcl_den. unfold heap_empty at 2.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Precondition characterization                                  *)
(* ================================================================= *)

(** Any set satisfying [BiAtom (AOk SLEmp)] is exactly [{Ok heap_empty}]. *)

Lemma ok_emp_is_singleton (m : PSet (err_state Heap)) :
  bi_sat mgcl_atom_sat m (BiAtom (AOk SLEmp)) ->
  m = pset_ret (Ok heap_empty).
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

(** The outcome set [{Ok(l↦1), Er(∅)}] satisfies
    [(ok: l↦1) ⊕ (er: emp)]. *)

Lemma post_sat_oplus (l : nat) :
  bi_sat mgcl_atom_sat
    (pset_union (pset_ret (Ok (heap_singleton l 1)))
                (pset_ret (Er heap_empty)))
    (BiOPlus (BiAtom (AOk (SLPointsTo l 1)))
             (BiAtom (AEr SLEmp))).
Proof.
  simpl.
  exists (pset_ret (Ok (heap_singleton l 1))),
         (pset_ret (Er heap_empty)).
  split.
  - (* union decomposition *)
    reflexivity.
  - split.
    + (* ok: l ↦ 1 *)
      unfold mgcl_atom_sat, nd_atom_sat. split.
      * exists (Ok (heap_singleton l 1)). constructor.
      * intros s Hin. inversion Hin; subst. simpl. reflexivity.
    + (* er: emp *)
      unfold mgcl_atom_sat, nd_atom_sat. split.
      * exists (Er heap_empty). constructor.
      * intros s Hin. inversion Hin; subst. simpl. reflexivity.
Qed.

(* ================================================================= *)
(** ** Equation 4 — Exact OL Triple                                   *)
(* ================================================================= *)

(** ⊨ ⟨ok:emp⟩ malloc(l);[l]←1 ⟨(ok: l↦1) ⊕ (er: emp)⟩

    For any set of states satisfying [ok:emp] (i.e., the singleton
    set [{Ok heap_empty}]), running [malloc_store l] produces the
    outcome set [{Ok(l↦1), Er(∅)}], which decomposes into
    [ok: l↦1] and [er: emp] via the outcome conjunction [⊕]. *)

Theorem malloc_store_eq4 (l : nat) :
  mgcl_valid
    (BiAtom (AOk SLEmp))
    (BiOPlus (BiAtom (AOk (SLPointsTo l 1)))
             (BiAtom (AEr SLEmp)))
    (malloc_store l).
Proof.
  intros m Hpre.
  (* The precondition forces m = {Ok heap_empty} *)
  rewrite (ok_emp_is_singleton m Hpre).
  (* Collecting over a singleton is just the denotation *)
  unfold collect. rewrite pset_bind_ret_l.
  (* Compute the denotation *)
  rewrite malloc_store_denote.
  (* Verify the postcondition *)
  exact (post_sat_oplus l).
Qed.

(* ================================================================= *)
(** ** Equation 5 — Under-Approximate OL Triple                       *)
(* ================================================================= *)

(** ⊨↓ ⟨ok:emp⟩ malloc(l);[l]←1 ⟨er: emp⟩

    The error outcome is reachable: malloc may return null (error),
    and this error propagates through the store.  This witnesses the
    bug without constraining the successful outcomes.

    Recall: ⊨↓ ⟨φ⟩ C ⟨ψ⟩ ≡ ⊨ ⟨φ⟩ C ⟨ψ ⊕ ⊤⟩ *)

Theorem malloc_store_eq5 (l : nat) :
  mgcl_valid_under
    (BiAtom (AOk SLEmp))
    (BiAtom (AEr SLEmp))
    (malloc_store l).
Proof.
  intros m Hpre.
  (* The precondition forces m = {Ok heap_empty} *)
  rewrite (ok_emp_is_singleton m Hpre).
  unfold collect. rewrite pset_bind_ret_l.
  rewrite malloc_store_denote.
  (* Need: {Ok(l↦1), Er(∅)} ⊨ (er:emp) ⊕ ⊤ *)
  simpl.
  exists (pset_ret (Er heap_empty)),
         (pset_ret (Ok (heap_singleton l 1))).
  split.
  - (* union decomposition — note the swap *)
    apply pset_union_comm.
  - split.
    + (* er: emp *)
      unfold mgcl_atom_sat, nd_atom_sat. split.
      * exists (Er heap_empty). constructor.
      * intros s Hin. inversion Hin; subst. simpl. reflexivity.
    + (* ⊤ *)
      exact I.
Qed.

(* ================================================================= *)
(** ** Corollary: Manifest Error                                      *)
(* ================================================================= *)

(** The error in [malloc_store] is manifest: it occurs regardless of
    the heap context.  This follows from the under-approximate triple
    (Equation 5) and matches the manifest error example in Section 5.2
    of the paper (line 1568 in the tex).

    Concretely:
    ⊨ ⟨ok:emp⟩ malloc(l);[l]←1 ⟨(er: emp) ⊕ ⊤⟩

    This is just the definition-unfolded form of Equation 5. *)

Corollary malloc_store_manifest (l : nat) :
  mgcl_valid
    (BiAtom (AOk SLEmp))
    (BiOPlus (BiAtom (AEr SLEmp)) BiTop)
    (malloc_store l).
Proof.
  exact (malloc_store_eq5 l).
Qed.

(* ================================================================= *)
(** ** Derived: Error Reachability (Individual State)                  *)
(* ================================================================= *)

(** The error state [Er heap_empty] is a member of the outcome set. *)

Lemma malloc_store_error_reachable (l : nat) :
  In _ (mgcl_denote (malloc_store l) (Ok heap_empty))
       (Er heap_empty).
Proof.
  rewrite malloc_store_denote.
  apply Union_intror. constructor.
Qed.

(** The success state [Ok (heap_singleton l 1)] is also reachable. *)

Lemma malloc_store_success_reachable (l : nat) :
  In _ (mgcl_denote (malloc_store l) (Ok heap_empty))
       (Ok (heap_singleton l 1)).
Proof.
  rewrite malloc_store_denote.
  apply Union_introl. constructor.
Qed.

(* ================================================================= *)
(** ** Derived: Equation 4 implies Equation 5                         *)
(* ================================================================= *)

(** Every exact triple implies the corresponding under-approximate
    triple.  This is a sanity check showing the relationship. *)

Lemma eq4_implies_eq5 (l : nat) :
  mgcl_valid
    (BiAtom (AOk SLEmp))
    (BiOPlus (BiAtom (AOk (SLPointsTo l 1)))
             (BiAtom (AEr SLEmp)))
    (malloc_store l) ->
  mgcl_valid_under
    (BiAtom (AOk SLEmp))
    (BiAtom (AEr SLEmp))
    (malloc_store l).
Proof.
  intro Heq4.
  intros m Hpre.
  specialize (Heq4 m Hpre).
  (* Post of Eq4: (ok:l↦1) ⊕ (er:emp) *)
  (* Need:        (er:emp) ⊕ ⊤ *)
  simpl in Heq4 |- *.
  destruct Heq4 as [m1 [m2 [Heq [Hok Her]]]].
  exists m2, m1.
  rewrite pset_union_comm.
  split; [exact Heq |].
  split; [exact Her | exact I].
Qed.
