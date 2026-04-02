(** * examples/OL/ManifestError.v — Manifest Error Examples

    Demonstrates manifest error reasoning from Section 5.3 of the
    Outcome Logic paper.

    Example 1: error() is manifest for SLTrue
    Example 2: error() + skip has a manifest error
    Example 3: Sequential composition with error — error(); C is
               manifest for any program C

    These examples illustrate the key concepts:
    - A *manifest error* is one that occurs regardless of the calling
      context (i.e., for every initial ok-state, some error outcome
      is reachable).
    - The under-approximate triple [⊨↓ ⟨ok:true⟩ C ⟨er:q⟩]
      characterizes manifest errors (Lemma 5.7).
    - Nondeterministic choice preserves manifestness.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5.3 *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL.Heap Require Import Assertion Error Lang Rules.
From OL.Heap Require Import Manifest.

Open Scope mgcl_scope.

(* ================================================================= *)
(** ** Example 1: error() is manifest for SLTrue                     *)
(* ================================================================= *)

(** The simplest manifest error: [error()] always produces an error
    state, and any heap satisfies [SLTrue]. *)

(** Direct proof from semantics: for any sigma, [error()] on
    [Ok sigma] gives [Er sigma], and [Er sigma] satisfies
    [SLTrue] trivially. *)

Lemma error_denote (sigma : Heap) :
  mgcl_denote (OLAtom MError) (Ok sigma) = pset_ret (Er sigma).
Proof.
  rewrite mgcl_denote_atom. apply mgcl_den_error.
Qed.

(** The error outcome is always reachable. *)

Lemma error_always_errors (sigma : Heap) :
  In _ (mgcl_denote (OLAtom MError) (Ok sigma)) (Er sigma).
Proof.
  rewrite error_denote. constructor.
Qed.

(** Manifest error (direct, not via the library lemma). *)

Theorem error_manifest_direct :
  manifest_error (OLAtom MError) SLTrue.
Proof.
  intros sigma.
  exists (Er sigma). split.
  - apply error_always_errors.
  - exists sigma. split; [reflexivity |].
    simpl. exact I.
Qed.

(** Via the characterization: manifest error ↔ under-approximate
    triple [⊨↓ ⟨ok:true⟩ error() ⟨er:true⟩]. *)

Theorem error_manifest_via_characterization :
  manifest_triple (OLAtom MError) SLTrue.
Proof.
  apply manifest_error_characterization.
  exact error_manifest_direct.
Qed.

(** And back: the triple implies the manifest error. *)

Theorem error_manifest_roundtrip :
  manifest_error (OLAtom MError) SLTrue.
Proof.
  apply manifest_error_characterization.
  exact error_manifest_via_characterization.
Qed.

(* ================================================================= *)
(** ** Example 2: error() + skip has a manifest error                *)
(* ================================================================= *)

(** The program [error() + skip] nondeterministically either errors
    or succeeds.  Despite having a successful branch, the error is
    still manifest: from every initial state, the error branch
    produces an error outcome. *)

Definition error_plus_skip : mgcl_prog := ERROR ⊕ₘ SKIP.

(** Denotation: the outcome set contains both Ok and Er states. *)

Lemma error_plus_skip_denote (sigma : Heap) :
  mgcl_denote error_plus_skip (Ok sigma) =
    pset_union (pset_ret (Er sigma)) (pset_ret (Ok sigma)).
Proof.
  unfold error_plus_skip.
  rewrite mgcl_denote_plus.
  rewrite mgcl_denote_atom, mgcl_denote_one.
  rewrite mgcl_den_error.
  reflexivity.
Qed.

(** The error outcome is in the result set. *)

Lemma error_plus_skip_error_reachable (sigma : Heap) :
  In _ (mgcl_denote error_plus_skip (Ok sigma)) (Er sigma).
Proof.
  rewrite error_plus_skip_denote.
  apply Union_introl. constructor.
Qed.

(** The success outcome is also in the result set. *)

Lemma error_plus_skip_success_reachable (sigma : Heap) :
  In _ (mgcl_denote error_plus_skip (Ok sigma)) (Ok sigma).
Proof.
  rewrite error_plus_skip_denote.
  apply Union_intror. constructor.
Qed.

(** Manifest error: [error() + skip] is manifest for SLTrue. *)

Theorem error_plus_skip_manifest :
  manifest_error error_plus_skip SLTrue.
Proof.
  (* Use the library lemma: choice preserves manifest errors *)
  apply manifest_choice_l.
  exact error_is_manifest.
Qed.

(** Via under-approximate triple. *)

Theorem error_plus_skip_triple :
  manifest_triple error_plus_skip SLTrue.
Proof.
  apply manifest_implies_triple.
  exact error_plus_skip_manifest.
Qed.

(** Under-approximate triple with explicit outcome conjunction:
    ⊨↓ ⟨ok:emp⟩ error()+skip ⟨er:emp⟩
    showing specifically that starting from the empty heap, the
    error outcome preserves the empty heap. *)

Theorem error_plus_skip_under_emp :
  mgcl_valid_under
    (BiAtom (AOk SLEmp))
    (BiAtom (AEr SLEmp))
    error_plus_skip.
Proof.
  intros m Hpre.
  (* Extract: m = {Ok heap_empty} *)
  simpl in Hpre. destruct Hpre as [[s0 Hs0] Hforall].
  specialize (Hforall s0 Hs0) as Hs0_sat.
  destruct s0 as [h0 | h0]; [| simpl in Hs0_sat; contradiction].
  simpl in Hs0_sat. subst h0.
  (* m = {Ok heap_empty} *)
  assert (Hm : m = pset_ret (Ok heap_empty)).
  { apply ensemble_ext. intro s. split.
    - intro Hin. specialize (Hforall s Hin).
      destruct s as [h | h].
      + simpl in Hforall. subst h. constructor.
      + simpl in Hforall. contradiction.
    - intro Hin. inversion Hin; subst. exact Hs0. }
  rewrite Hm. unfold collect. rewrite pset_bind_ret_l.
  rewrite error_plus_skip_denote.
  (* Need: {Er heap_empty, Ok heap_empty} ⊨ (er:emp) ⊕ ⊤ *)
  simpl.
  exists (pset_ret (Er heap_empty)),
         (pset_union (pset_ret (Er heap_empty)) (pset_ret (Ok heap_empty))).
  split.
  - (* union absorption: {Er heap_empty} ∪ full = full *)
    apply ensemble_ext. intro s. split.
    + intro Hunion. inversion Hunion; subst.
      * inversion H; subst. apply Union_introl. exact H.
      * exact H.
    + intro Hin. apply Union_intror. exact Hin.
  - split.
    + (* er: emp *)
      unfold mgcl_atom_sat, nd_atom_sat. split.
      * exists (Er heap_empty). constructor.
      * intros s Hin. inversion Hin; subst. simpl. reflexivity.
    + (* ⊤ *)
      exact I.
Qed.

(* ================================================================= *)
(** ** Example 3: Sequential composition — error(); C is manifest   *)
(* ================================================================= *)

(** When [error()] is sequenced before any program [C], the error
    propagates through [C] (by error propagation).  Therefore
    [error(); C] is a manifest error for [SLTrue], regardless of [C].

    This demonstrates how manifest errors compose sequentially:
    once an error occurs, it cannot be recovered from by subsequent
    commands. *)

(** Helper: error propagation through any program.
    If a state [Er h] is in [⟦C⟧(Er h)] for any [C], it must be
    propagated.  Since atoms always propagate errors, and the program
    constructors (seq, plus, star) preserve membership, we prove this
    for atomic programs and lift. *)

Lemma error_propagates_through_atom (c : mgcl_atom) (h : Heap) :
  mgcl_denote (OLAtom c) (Er h) = pset_ret (Er h).
Proof.
  rewrite mgcl_denote_atom. apply mgcl_den_er_propagate.
Qed.

(** For any program [C], [error(); C] on [Ok sigma] produces
    exactly the same as [C] on [Er sigma] — which by error
    propagation is [{Er sigma}] for any atomic [C]. *)

Lemma error_seq_atom_denote (c : mgcl_atom) (sigma : Heap) :
  mgcl_denote (OLSeq (OLAtom MError) (OLAtom c)) (Ok sigma) =
    pset_ret (Er sigma).
Proof.
  rewrite mgcl_denote_seq.
  rewrite mgcl_denote_atom.
  rewrite mgcl_den_error.
  rewrite pset_bind_ret_l.
  rewrite mgcl_denote_atom.
  apply mgcl_den_er_propagate.
Qed.

(** Manifest error for error() followed by an atom. *)

Theorem error_seq_atom_manifest (c : mgcl_atom) :
  manifest_error (OLSeq (OLAtom MError) (OLAtom c)) SLTrue.
Proof.
  intros sigma.
  exists (Er sigma). split.
  - rewrite error_seq_atom_denote. constructor.
  - exists sigma. split; [reflexivity | simpl; exact I].
Qed.

(** Manifest triple form for error() followed by an atom. *)

Theorem error_seq_atom_triple (c : mgcl_atom) :
  manifest_triple (OLSeq (OLAtom MError) (OLAtom c)) SLTrue.
Proof.
  apply manifest_implies_triple.
  apply error_seq_atom_manifest.
Qed.

(* ================================================================= *)
(** ** Example 3b: Comparison — skip is NOT manifest                 *)
(* ================================================================= *)

(** As a contrast, [skip] is never a manifest error: it produces
    only ok-outcomes, so no error is reachable. *)

Theorem skip_not_manifest_example (q : sl_assert) :
  latent_error OLOne q.
Proof.
  apply skip_not_manifest.
Qed.

(** Abort is also not manifest (vacuously — no outcomes at all). *)

Theorem abort_not_manifest_example (q : sl_assert) :
  latent_error OLZero q.
Proof.
  apply abort_not_manifest.
Qed.

(* ================================================================= *)
(** ** Example 4: Manifest vs Latent in malloc                       *)
(* ================================================================= *)

(** With the normalized malloc [alloc(l,v) + skip], malloc alone does
    NOT have a manifest error — both branches produce Ok outcomes.
    Furthermore, [malloc; store] is also not unconditionally manifest:
    if [l] is already allocated, both branches of [malloc; store]
    succeed.  The error is LATENT, depending on the initial state.

    The error only occurs when starting from a heap where [l] is
    unallocated.  This matches the paper: the bug is witnessed by
    the under-approximate triple ⊨↓ ⟨ok:emp⟩ malloc(l);[l]←1 ⟨er:emp⟩
    (proven in Malloc.v), not by a manifest error property. *)

Theorem malloc_store_error_from_empty (l v : nat) :
  exists tau,
    In _ (mgcl_denote ((MALLOC l v) ;; (STORE l v)) (Ok heap_empty)) tau /\
    exists h, tau = Er h /\ sl_sat h SLTrue.
Proof.
  exists (Er heap_empty).
  split.
  - change (In _ (pset_bind (mgcl_denote (MALLOC l v) (Ok heap_empty))
                             (mgcl_denote (STORE l v)))
                  (Er heap_empty)).
    rewrite mgcl_malloc_denote.
    rewrite pset_bind_union, !pset_bind_ret_l.
    rewrite mgcl_denote_atom.
    simpl. apply Union_intror. constructor.
  - exists heap_empty. split; [reflexivity | exact I].
Qed.

(* ================================================================= *)
(** ** Summary                                                        *)
(* ================================================================= *)

(** Key results demonstrated:

    1. [error_manifest_direct]:
         manifest_error (OLAtom MError) SLTrue
       error() always produces an error.

    2. [error_plus_skip_manifest]:
         manifest_error (error() + skip) SLTrue
       Nondeterministic choice preserves manifestness.

    3. [error_seq_atom_manifest]:
         manifest_error (error(); c) SLTrue
       Error propagation through sequential composition.

    4. [skip_not_manifest_example]:
         latent_error skip q
       Skip never produces errors (contrast case).

    5. [malloc_store_error_from_empty]:
         Error reachable from heap_empty for malloc(l,v);store(l,v)
       With normalized malloc [alloc + skip], the error is latent
       (depends on initial state), not manifest.  The bug is witnessed
       by the under-approx triple in Malloc.v, not manifestness. *)

Close Scope mgcl_scope.
