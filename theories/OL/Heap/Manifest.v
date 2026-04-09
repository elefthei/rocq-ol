(** * OL/Heap/Manifest.v — Manifest Error Characterization (Lemma 5.7)

    Defines [manifest errors] and proves the bidirectional
    characterization from Lemma 5.7 of the paper:

      An under-approximate triple [⊨↓ ⟨p⟩ C ⟨er:q⟩] is a manifest
      error iff [⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩].

    A manifest error is one that occurs regardless of the calling
    context — i.e., for every ok-state σ, some error outcome
    satisfying q is reachable.  This contrasts with *latent* errors,
    which only manifest in certain calling contexts.

    The key insight from the paper (Section 5.3) is that OL's
    outcome conjunction [⊕] and under-approximate triples provide a
    clean, compositional characterization of manifest errors that is
    difficult to express in Incorrectness Logic alone.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5.3, Lemma 5.7 *)

From Stdlib Require Import Ensembles Classical_Prop PeanoNat.
From OL Require Import Monad Assertion Lang Triple.
From OL Require Import Error.
From OL.Heap Require Import Assertion Lang Rules.

(* ================================================================= *)
(** ** Manifest Error Definition                                      *)
(* ================================================================= *)

(** A manifest error for a program [C] with error postcondition [q]
    asserts: for every initial ok-state σ, there exists at least one
    outcome in [⟦C⟧(Ok σ)] that is an error satisfying [q ⊕ ⊤].

    Informally, no matter what heap the caller provides, the program
    will (among its possible outcomes) produce an error satisfying q.

    This matches the paper's definition:
    [∀σ. ∃τ ∈ ⟦C⟧(σ). τ ⊨ (er:q ⊕ ⊤)] *)

Definition manifest_error
    (C : mgcl_prog) (q : sl_assert) : Prop :=
  forall (sigma : Heap),
    exists (tau : err_state Heap),
      In _ (mgcl_denote C (Ok sigma)) tau /\
      exists h, tau = Er h /\ sl_sat h q.

(** Alternative characterization using [bi_sat_under]:
    the error outcome satisfies [er:q] under the under-approximate
    interpretation (i.e., [er:q ⊕ ⊤]). *)

Definition manifest_error_bi
    (C : mgcl_prog) (q : sl_assert) : Prop :=
  forall (sigma : Heap),
    bi_sat_under heap_nd_atom_sat
      (mgcl_denote C (Ok sigma))
      (BiAtom (AEr q)).

(* ================================================================= *)
(** ** Under-Approximate Triple Form                                  *)
(* ================================================================= *)

(** The OL under-approximate triple characterization:
    [⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩]

    This says: for every set of ok-states [S] satisfying [ok:true]
    (i.e., any non-empty set of ok-states), the collected outcomes
    [C†(S)] satisfy [er:q ⊕ ⊤] — meaning they contain at least some
    errors satisfying q (with possibly more outcomes). *)

Definition manifest_triple
    (C : mgcl_prog) (q : sl_assert) : Prop :=
  heap_ol_valid_under (mgcl_denote C)
    (BiAtom (AOk SLTrue))
    (BiAtom (AEr q)).

(* ================================================================= *)
(** ** Helper Lemmas                                                  *)
(* ================================================================= *)

Section Helpers.

  (** Any heap satisfies [SLTrue]. *)
  Lemma sl_sat_true (h : Heap) : sl_sat h SLTrue.
  Proof. simpl. exact I. Qed.

  (** A singleton ok-state satisfies [ok:true]. *)
  Lemma ok_true_singleton (sigma : Heap) :
    bi_sat heap_nd_atom_sat (pset_ret (Ok sigma)) (BiAtom (AOk SLTrue)).
  Proof.
    simpl. split.
    - exists (Ok sigma). constructor.
    - intros s Hin. inversion Hin; subst. simpl. exact I.
  Qed.

  (** Collecting a singleton set is just the denotation. *)
  Lemma collect_singleton_mgcl (C : mgcl_prog) (s : err_state Heap) :
    collect (mgcl_denote C) (pset_ret s) = mgcl_denote C s.
  Proof.
    unfold collect. apply pset_bind_ret_l.
  Qed.

  (** If [tau] is in [⟦C⟧(Ok sigma)] and [Ok sigma] is in [S],
      then [tau] is in [C†(S)]. *)
  Lemma collect_member (C : mgcl_prog) (S : PSet (err_state Heap))
      (sigma : Heap) (tau : err_state Heap) :
    In _ S (Ok sigma) ->
    In _ (mgcl_denote C (Ok sigma)) tau ->
    In _ (collect (mgcl_denote C) S) tau.
  Proof.
    intros HS Htau.
    unfold collect, pset_bind.
    exists (Ok sigma). split; assumption.
  Qed.

  (** Under-approximate satisfaction for singletons:
      if there exists an error outcome tau in [f s] satisfying q,
      then [f s] satisfies [er:q ⊕ ⊤]. *)
  Lemma under_approx_er_witness
      (f_result : PSet (err_state Heap))
      (h : Heap) (q : sl_assert) :
    In _ f_result (Er h) ->
    sl_sat h q ->
    bi_sat heap_nd_atom_sat f_result (BiOPlus (BiAtom (AEr q)) BiTop).
  Proof.
    intros Hin Hsat.
    simpl.
    exists (pset_ret (Er h)), f_result.
    split.
    - (* pset_union {Er h} f_result = f_result since Er h ∈ f_result *)
      apply ensemble_ext. intro tau.
      unfold pset_union. split.
      + intro Hunion. inversion Hunion; subst.
        * unfold pset_ret in H. inversion H; subst. exact Hin.
        * exact H.
      + intro Hf. apply Union_intror. exact Hf.
    - split.
      + (* pset_ret (Er h) satisfies AEr q *)
        simpl. split.
        * exists (Er h). constructor.
        * intros s Hs. inversion Hs; subst. simpl. exact Hsat.
      + (* f_result satisfies ⊤ *)
        exact I.
  Qed.

  (** From a set satisfying [ok:true], we can extract an ok-state. *)
  Lemma ok_true_extract (S : PSet (err_state Heap)) :
    bi_sat heap_nd_atom_sat S (BiAtom (AOk SLTrue)) ->
    exists sigma, In _ S (Ok sigma).
  Proof.
    simpl. intros [Hne Hforall].
    destruct Hne as [s Hs].
    specialize (Hforall s Hs).
    destruct s as [sigma | sigma].
    - exists sigma. exact Hs.
    - simpl in Hforall. contradiction.
  Qed.

  (** From an under-approximate error in collected semantics
      (with ok:true precondition), extract a witness. *)
  Lemma collect_ok_true_under_er_extract
      (C : mgcl_prog) (S : PSet (err_state Heap))
      (q : sl_assert) :
    bi_sat heap_nd_atom_sat S (BiAtom (AOk SLTrue)) ->
    bi_sat heap_nd_atom_sat (collect (mgcl_denote C) S) (BiOPlus (BiAtom (AEr q)) BiTop) ->
    exists (sigma : Heap) (h : Heap),
      In _ S (Ok sigma) /\
      In _ (mgcl_denote C (Ok sigma)) (Er h) /\
      sl_sat h q.
  Proof.
    intros Hpre Hpost.
    simpl in Hpost.
    destruct Hpost as [m1 [m2 [Heq [[Hne1 Hforall1] _]]]].
    destruct Hne1 as [tau Htau].
    specialize (Hforall1 tau Htau) as Hsat_tau.
    destruct tau as [h | h].
    - simpl in Hsat_tau. contradiction.
    - assert (Hin_col : In _ (collect (mgcl_denote C) S) (Er h)).
      { rewrite <- Heq. apply Union_introl. exact Htau. }
      unfold collect, pset_bind in Hin_col.
      destruct Hin_col as [s [HS Hden]].
      destruct Hpre as [_ Hok].
      specialize (Hok s HS).
      destruct s as [sigma | sigma].
      + exists sigma, h.
        split; [exact HS |].
        split; [exact Hden |].
        simpl in Hsat_tau. exact Hsat_tau.
      + simpl in Hok. contradiction.
  Qed.

End Helpers.

(* ================================================================= *)
(** ** Lemma 5.7 — Forward Direction                                  *)
(* ================================================================= *)

(** If the error is manifest (occurs from every ok-state), then the
    under-approximate triple [⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩] holds.

    Proof sketch: Given [S ⊨ ok:true], extract some [Ok σ ∈ S].
    By manifest error, [∃ τ ∈ ⟦C⟧(Ok σ)], [τ = Er h] with [h ⊨ q].
    Since [Ok σ ∈ S], we have [τ ∈ C†(S)].  Decompose [C†(S)] as
    the singleton [{Er h}] (satisfying [er:q]) union the rest
    (satisfying [⊤]). *)

Section ForwardDirection.

  Theorem manifest_implies_triple (C : mgcl_prog) (q : sl_assert) :
    manifest_error C q -> manifest_triple C q.
  Proof.
    intros Hmanifest.
    unfold manifest_triple, heap_ol_valid_under, heap_ol_valid, ol_valid_under, ol_valid.
    intros S Hpre.
    (* Extract an ok-state from S *)
    destruct (ok_true_extract S Hpre) as [sigma Hsigma].
    (* Use manifest error to get an error witness *)
    destruct (Hmanifest sigma) as [tau [Htau_in [h [Htau_eq Hsat_q]]]].
    subst tau.
    (* Er h is in C†(S) *)
    assert (Hin_col : In _ (collect (mgcl_denote C) S) (Er h)).
    { apply (collect_member C S sigma (Er h) Hsigma Htau_in). }
    (* Now show C†(S) ⊨ (er:q ⊕ ⊤) *)
    apply (under_approx_er_witness (collect (mgcl_denote C) S) h q Hin_col Hsat_q).
  Qed.

End ForwardDirection.

(* ================================================================= *)
(** ** Lemma 5.7 — Backward Direction                                 *)
(* ================================================================= *)

(** If [⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩], then the error is manifest.

    Proof sketch: Let σ be an arbitrary ok-state.  Instantiate the
    triple with [S = {Ok σ}], which satisfies [ok:true].
    Then [C†({Ok σ}) = ⟦C⟧(Ok σ)] satisfies [(er:q) ⊕ ⊤],
    meaning there exists [Er h ∈ ⟦C⟧(Ok σ)] with [h ⊨ q]. *)

Section BackwardDirection.

  Theorem triple_implies_manifest (C : mgcl_prog) (q : sl_assert) :
    manifest_triple C q -> manifest_error C q.
  Proof.
    intros Htriple sigma.
    unfold manifest_triple, heap_ol_valid_under, heap_ol_valid, ol_valid_under, ol_valid in Htriple.
    (* Instantiate with the singleton set {Ok sigma} *)
    assert (Hpre : bi_sat heap_nd_atom_sat
                     (pset_ret (Ok sigma)) (BiAtom (AOk SLTrue))).
    { apply ok_true_singleton. }
    specialize (Htriple (pset_ret (Ok sigma)) Hpre).
    (* C†({Ok sigma}) = ⟦C⟧(Ok sigma) *)
    rewrite collect_singleton_mgcl in Htriple.
    (* Htriple : mgcl_denote C (Ok sigma) ⊨ (er:q ⊕ ⊤) *)
    simpl in Htriple.
    destruct Htriple as [m1 [m2 [Heq [[Hne1 Hforall1] _]]]].
    destruct Hne1 as [tau Htau].
    specialize (Hforall1 tau Htau) as Hsat_tau.
    destruct tau as [h | h].
    - simpl in Hsat_tau. contradiction.
    - (* tau = Er h, and it satisfies q *)
      exists (Er h).
      split.
      + (* Er h is in mgcl_denote C (Ok sigma) *)
        rewrite <- Heq. apply Union_introl. exact Htau.
      + exists h. split; [reflexivity |].
        simpl in Hsat_tau. exact Hsat_tau.
  Qed.

End BackwardDirection.

(* ================================================================= *)
(** ** Lemma 5.7 — Full Characterization                              *)
(* ================================================================= *)

(** The complete biconditional: manifest errors are precisely
    characterized by the under-approximate OL triple. *)

Theorem manifest_error_characterization (C : mgcl_prog) (q : sl_assert) :
  manifest_error C q <-> manifest_triple C q.
Proof.
  split.
  - apply manifest_implies_triple.
  - apply triple_implies_manifest.
Qed.

(* ================================================================= *)
(** ** Manifest vs Latent Errors                                      *)
(* ================================================================= *)

(** A latent error is one that is *not* manifest: there exists some
    calling context (initial ok-state) from which no error outcome
    satisfying q is reachable. *)

Definition latent_error (C : mgcl_prog) (q : sl_assert) : Prop :=
  ~ manifest_error C q.

(** Equivalently, a latent error means the manifest triple fails. *)
Lemma latent_iff_not_triple (C : mgcl_prog) (q : sl_assert) :
  latent_error C q <-> ~ manifest_triple C q.
Proof.
  unfold latent_error.
  split; intro H; intro Habs; apply H;
    apply manifest_error_characterization; exact Habs.
Qed.

(* ================================================================= *)
(** ** Corollaries                                                    *)
(* ================================================================= *)

Section Corollaries.

  (** The [error()] command produces a manifest error with postcondition
      [SLTrue] — any heap satisfies [true]. *)
  Lemma error_is_manifest :
    manifest_error (OLAtom MError) SLTrue.
  Proof.
    intros sigma.
    exists (Er sigma).
    split.
    - simpl. constructor.
    - exists sigma. split; [reflexivity |].
      simpl. exact I.
  Qed.

  (** [error()] manifest error via the triple characterization. *)
  Lemma error_manifest_triple :
    manifest_triple (OLAtom MError) SLTrue.
  Proof.
    apply manifest_implies_triple.
    apply error_is_manifest.
  Qed.

  (** Skip is never a manifest error (it produces only ok-outcomes). *)
  Lemma skip_not_manifest (q : sl_assert) :
    latent_error OLOne q.
  Proof.
    intros Hmanifest.
    destruct (Hmanifest heap_empty) as [tau [Hin [h [Htau_eq _]]]].
    subst tau.
    simpl in Hin. inversion Hin.
  Qed.

  (** Abort is vacuously never manifest (no outcomes at all). *)
  Lemma abort_not_manifest (q : sl_assert) :
    latent_error OLZero q.
  Proof.
    intros Hmanifest.
    destruct (Hmanifest heap_empty) as [tau [Hin _]].
    simpl in Hin. inversion Hin.
  Qed.

  (** A manifest error is witnessed by every ok-state,
      so instantiating with any specific state gives a witness. *)
  Lemma manifest_witness (C : mgcl_prog) (q : sl_assert) (sigma : Heap) :
    manifest_error C q ->
    exists h,
      In _ (mgcl_denote C (Ok sigma)) (Er h) /\ sl_sat h q.
  Proof.
    intro Hm.
    destruct (Hm sigma) as [tau [Hin [h [Heq Hsat]]]].
    exists h. subst tau. split; assumption.
  Qed.

  (** Manifest errors are monotone in postcondition weakening:
      if [q] entails [q'], then manifest for [q] implies manifest for [q']. *)
  Lemma manifest_weaken (C : mgcl_prog) (q q' : sl_assert) :
    manifest_error C q ->
    (forall h, sl_sat h q -> sl_sat h q') ->
    manifest_error C q'.
  Proof.
    intros Hm Hweak sigma.
    destruct (Hm sigma) as [tau [Hin [h [Heq Hsat]]]].
    exists tau. split; [exact Hin |].
    exists h. split; [exact Heq |].
    apply Hweak. exact Hsat.
  Qed.

  (** Choice preserves manifest errors: if [C1] is manifest,
      then [C1 + C2] is also manifest (C1's error outcomes
      are a subset of the choice's outcomes). *)
  Lemma manifest_choice_l (C1 C2 : mgcl_prog) (q : sl_assert) :
    manifest_error C1 q ->
    manifest_error (OLPlus C1 C2) q.
  Proof.
    intros Hm sigma.
    destruct (Hm sigma) as [tau [Hin [h [Heq Hsat]]]].
    exists tau. split.
    - simpl. apply Union_introl. exact Hin.
    - exists h. split; [exact Heq | exact Hsat].
  Qed.

  Lemma manifest_choice_r (C1 C2 : mgcl_prog) (q : sl_assert) :
    manifest_error C2 q ->
    manifest_error (OLPlus C1 C2) q.
  Proof.
    intros Hm sigma.
    destruct (Hm sigma) as [tau [Hin [h [Heq Hsat]]]].
    exists tau. split.
    - simpl. apply Union_intror. exact Hin.
    - exists h. split; [exact Heq | exact Hsat].
  Qed.

End Corollaries.

(* ================================================================= *)
(** ** Summary                                                        *)
(* ================================================================= *)

(** Key results proved in this file:

    *** Lemma 5.7 (Manifest Error Characterization) ***
    - [manifest_implies_triple]:
        manifest_error C q → ⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩
    - [triple_implies_manifest]:
        ⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩ → manifest_error C q
    - [manifest_error_characterization]:
        manifest_error C q ↔ ⊨↓ ⟨ok:true⟩ C ⟨er:q ⊕ ⊤⟩

    *** Manifest vs Latent ***
    - [latent_error]:           ¬ manifest_error C q
    - [latent_iff_not_triple]:  latent ↔ ¬ manifest_triple

    *** Corollaries ***
    - [error_is_manifest]:      error() is manifest for SLTrue
    - [skip_not_manifest]:      skip is never manifest
    - [abort_not_manifest]:     abort is never manifest
    - [manifest_witness]:       manifest → specific witness
    - [manifest_weaken]:        postcondition weakening
    - [manifest_choice_l/r]:    choice preserves manifestness
*)
