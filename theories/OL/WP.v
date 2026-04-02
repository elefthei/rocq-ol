(** * OL/WP.v — Weakest Precondition Transformers

    Defines angelic WP and demonic WLP predicate transformers from the
    WHP paper (arXiv:2404.05097) and the non-unrolling while-loop rules
    from the TOPLAS paper (arXiv:2401.04594).

    Main definitions:
    - [wp denote Q σ]    — ∃τ ∈ denote(σ). Q(τ)   (angelic / Lisbon)
    - [wlp denote Q σ]   — ∀τ ∈ denote(σ). Q(τ)   (demonic / Hoare)

    While-loop rules (CENTRAL — from TOPLAS paper):
    - [wlp_while_invariant]  — Hoare invariant rule (no unrolling)
    - [wp_while_variant]     — Lisbon variant rule (witnesses termination)

    Reference:
    - arXiv:2404.05097, Tables 1–2 (WP/WLP/SP)
    - arXiv:2401.04594, §5.3 (While, Invariant, Variant rules) *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Lang SP.
From OL.Rules Require Import Expression.

(* ================================================================= *)
(** ** WP and WLP Definitions                                        *)
(* ================================================================= *)

Section WPDefs.

Context {Sigma : Type}.

(** Angelic weakest precondition: some execution reaches [Q].
    Corresponds to Lisbon Logic / [◇] modality. *)
Definition wp (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) : Prop :=
  exists tau, In _ (denote sigma) tau /\ Q tau.

(** Demonic weakest liberal precondition: all executions satisfy [Q].
    Corresponds to Hoare Logic / [□] modality. *)
Definition wlp (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) : Prop :=
  forall tau, In _ (denote sigma) tau -> Q tau.

End WPDefs.

(* ================================================================= *)
(** ** Connection to Existing Definitions                             *)
(* ================================================================= *)

Section Connection.

Context {Sigma : Type}.

(** WLP is exactly [hoare_valid] from [Hoare.v], stated pointwise. *)
Lemma wlp_iff_hoare_pointwise (denote : Sigma -> PSet Sigma)
    (P : Sigma -> Prop) (Q : Sigma -> Prop) :
  (forall sigma, P sigma -> wlp denote Q sigma) <->
  (forall sigma, P sigma -> forall tau, In _ (denote sigma) tau -> Q tau).
Proof.
  split; intros H sigma HP; exact (H sigma HP).
Qed.

End Connection.

(* ================================================================= *)
(** ** Inductive WP/WLP Rules                                        *)
(* ================================================================= *)

Section WPRules.

Context {Atom Sigma : Type}.
Variable atom_den : Atom -> Sigma -> PSet Sigma.

Let den := ol_denote atom_den.

(** *** WP Rules *)

Lemma wp_one (Q : Sigma -> Prop) (sigma : Sigma) :
  wp (den OLOne) Q sigma <-> Q sigma.
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hret HQ]]. inversion Hret. subst. exact HQ.
  - intro HQ. exists sigma. split; [constructor | exact HQ].
Qed.

Lemma wp_zero (Q : Sigma -> Prop) (sigma : Sigma) :
  ~ wp (den OLZero) Q sigma.
Proof.
  unfold wp. simpl. intros [tau [Habs _]]. destruct Habs.
Qed.

Lemma wp_plus (C1 C2 : ol_prog Atom) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wp (den (OLPlus C1 C2)) Q sigma <->
  wp (den C1) Q sigma \/ wp (den C2) Q sigma.
Proof.
  unfold wp. simpl. split.
  - intros [tau [HU HQ]]. inversion HU; subst.
    + left. exists tau. auto.
    + right. exists tau. auto.
  - intros [[tau [H1 HQ]] | [tau [H2 HQ]]].
    + exists tau. split; [left; exact H1 | exact HQ].
    + exists tau. split; [right; exact H2 | exact HQ].
Qed.

Lemma wp_seq (C1 C2 : ol_prog Atom) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wp (den (OLSeq C1 C2)) Q sigma <->
  wp (den C1) (wp (den C2) Q) sigma.
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hseq HQ]].
    destruct Hseq as [mid [HC1 HC2]].
    exists mid. split; [exact HC1|].
    exists tau. auto.
  - intros [mid [HC1 [tau [HC2 HQ]]]].
    exists tau. split; [|exact HQ].
    exists mid. auto.
Qed.

Lemma wp_atom (a : Atom) (Q : Sigma -> Prop) (sigma : Sigma) :
  wp (den (OLAtom a)) Q sigma <-> wp (atom_den a) Q sigma.
Proof.
  reflexivity.
Qed.

(** *** WLP Rules *)

Lemma wlp_one (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp (den OLOne) Q sigma <-> Q sigma.
Proof.
  unfold wlp. simpl. split.
  - intro H. apply H. constructor.
  - intros HQ tau Hret. inversion Hret. subst. exact HQ.
Qed.

Lemma wlp_zero (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp (den OLZero) Q sigma.
Proof.
  unfold wlp. simpl. intros tau Habs. destruct Habs.
Qed.

Lemma wlp_plus (C1 C2 : ol_prog Atom) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wlp (den (OLPlus C1 C2)) Q sigma <->
  wlp (den C1) Q sigma /\ wlp (den C2) Q sigma.
Proof.
  unfold wlp. simpl. split.
  - intro H. split.
    + intros tau H1. apply H. left. exact H1.
    + intros tau H2. apply H. right. exact H2.
  - intros [H1 H2] tau HU.
    inversion HU; subst; auto.
Qed.

Lemma wlp_seq (C1 C2 : ol_prog Atom) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wlp (den (OLSeq C1 C2)) Q sigma <->
  wlp (den C1) (wlp (den C2) Q) sigma.
Proof.
  unfold wlp. simpl. split.
  - intros H mid HC1 tau HC2.
    apply H. exists mid. auto.
  - intros H tau [mid [HC1 HC2]].
    exact (H mid HC1 tau HC2).
Qed.

Lemma wlp_atom (a : Atom) (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp (den (OLAtom a)) Q sigma <-> wlp (atom_den a) Q sigma.
Proof.
  reflexivity.
Qed.

End WPRules.

(* ================================================================= *)
(** ** WP/WLP for Assume                                             *)
(* ================================================================= *)

Section WPAssume.

Context {Sigma : Type}.

Lemma wp_assume (b : Sigma -> Prop) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wp (assume_den b) Q sigma <-> b sigma /\ Q sigma.
Proof.
  unfold wp, assume_den. split.
  - intros [tau [[Heq Hb] HQ]]. subst. auto.
  - intros [Hb HQ]. exists sigma. split; [split; auto | auto].
Qed.

Lemma wlp_assume (b : Sigma -> Prop) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wlp (assume_den b) Q sigma <-> (b sigma -> Q sigma).
Proof.
  unfold wlp, assume_den. split.
  - intros H Hb. apply H. split; [reflexivity | exact Hb].
  - intros H tau [Heq Hb]. subst. exact (H Hb).
Qed.

End WPAssume.

(* ================================================================= *)
(** ** SP–WP Duality                                                 *)
(* ================================================================= *)

(** The key theorem connecting forward (SP) and backward (WP)
    reasoning: something in the strongest post satisfies Q iff
    some precondition state has WP Q.  (Thm 4.5, Boolean case.) *)

Section Duality.

Context {Sigma : Type}.

Theorem sp_wp_duality (denote : Sigma -> PSet Sigma)
    (P Q : Sigma -> Prop) :
  (exists tau, In _ (sp denote P) tau /\ Q tau) <->
  (exists sigma, In _ P sigma /\ wp denote Q sigma).
Proof.
  unfold sp, collect, pset_bind, wp. split.
  - intros [tau [[sigma [HP Hden]] HQ]].
    exists sigma. split; [exact HP|].
    exists tau. auto.
  - intros [sigma [HP [tau [Hden HQ]]]].
    exists tau. split; [|exact HQ].
    exists sigma. auto.
Qed.

(** WP–WLP duality (De Morgan, requires classical logic). *)
Theorem wp_wlp_duality (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wp denote Q sigma <-> ~ wlp denote (fun tau => ~ Q tau) sigma.
Proof.
  unfold wp, wlp. split.
  - intros [tau [Hden HQ]] Hall.
    exact (Hall tau Hden HQ).
  - intro Hnn. apply NNPP.
    intro Hn. apply Hnn.
    intros tau Hden HQ.
    apply Hn. exists tau. auto.
Qed.

End Duality.

(* ================================================================= *)
(** ** WP Monotonicity                                               *)
(* ================================================================= *)

Section Monotonicity.

Context {Sigma : Type}.

Lemma wp_monotone (denote : Sigma -> PSet Sigma)
    (Q R : Sigma -> Prop) :
  (forall tau, Q tau -> R tau) ->
  forall sigma, wp denote Q sigma -> wp denote R sigma.
Proof.
  intros Hsub sigma [tau [Hden HQ]].
  exists tau. split; [exact Hden | apply Hsub; exact HQ].
Qed.

Lemma wlp_monotone (denote : Sigma -> PSet Sigma)
    (Q R : Sigma -> Prop) :
  (forall tau, Q tau -> R tau) ->
  forall sigma, wlp denote Q sigma -> wlp denote R sigma.
Proof.
  intros Hsub sigma Hwlp tau Hden.
  apply Hsub. exact (Hwlp tau Hden).
Qed.

End Monotonicity.

(* ================================================================= *)
(** ** While-Loop Rules (CENTRAL — from TOPLAS paper)                *)
(* ================================================================= *)

(** These non-unrolling rules are the main contribution.  They come
    from the TOPLAS paper (arXiv:2401.04594, §5.3):

    A. [wlp_while_invariant] — Hoare/demonic invariant rule
    B. [wp_while_variant]    — Lisbon/angelic variant rule

    Both work directly on [while_den] from [Expression.v] without
    needing to unfold the [star] inductive or reason about
    bounded iteration. *)

Section WhileRules.

Context {Sigma : Type}.

(** *** A. WLP While — Invariant Rule (Hoare)

    If invariant [I] is preserved by the loop body on ALL paths
    (demonic), and [I ∧ ¬b → Q], then [I → wlp[while b C]{Q}].

    This is the standard Hoare while rule as a predicate transformer.
    Derived from TOPLAS Invariant rule (§5.3.4, lines 1339–1346):

    <<
      triple(sure(P ∧ b), C, always(P))
      ─────────────────────────────────
      triple(sure(P), while b C, always(P ∧ ¬b))
    >>
*)
Theorem wlp_while_invariant (I : Sigma -> Prop) (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  (forall sigma, I sigma -> b sigma ->
    wlp body I sigma) ->
  (forall sigma, I sigma -> ~ b sigma -> Q sigma) ->
  forall sigma, I sigma -> wlp (while_den b body) Q sigma.
Proof.
  intros Hbody Hexit sigma HI.
  unfold wlp, while_den, pset_bind.
  intros tau [rho [Hstar Hassume]].
  destruct Hassume as [Heq Hnb]. subst tau.
  apply Hexit; [|exact Hnb].
  (* Show: I rho — by induction on star *)
  clear Hnb Q Hexit.
  induction Hstar as [| s mid rho Hstep Hstar IH].
  - exact HI.
  - apply IH.
    (* mid is reached from s via guarded body *)
    unfold while_body_den, pset_bind in Hstep.
    destruct Hstep as [s' [Hassume Hmid]].
    destruct Hassume as [Heq Hb]. subst s'.
    (* I s and b s, so wlp body I s, so I mid *)
    assert (HIs : I s).
    { (* Need I s — but we're doing induction on star from sigma.
         Actually, we need to strengthen the induction hypothesis.
         Let's redo this with a stronger statement. *)
      admit. }
    exact (Hbody s HIs Hb mid Hmid).
Abort.

(** We need a strengthened induction: every state reachable via
    [star (while_body_den b body)] from a state satisfying [I]
    also satisfies [I]. *)

Lemma star_preserves_invariant (I : Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma) :
  (forall sigma, I sigma -> b sigma -> wlp body I sigma) ->
  forall sigma rho,
    I sigma ->
    star (while_body_den b body) sigma rho ->
    I rho.
Proof.
  intros Hbody sigma rho HI Hstar.
  induction Hstar as [| s mid rho Hstep Hstar IH].
  - exact HI.
  - apply IH.
    unfold while_body_den, pset_bind in Hstep.
    destruct Hstep as [s' [Hassume Hmid]].
    destruct Hassume as [Heq Hb]. subst s'.
    exact (Hbody s HI Hb mid Hmid).
Abort.

(** The issue is that the IH for [star] gives us induction from [s]
    (the current node), but we need [I s] at each step.  We must carry
    the invariant through the whole induction. *)

Lemma star_preserves_invariant (I : Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma) :
  (forall sigma, I sigma -> b sigma -> wlp body I sigma) ->
  forall sigma rho,
    star (while_body_den b body) sigma rho ->
    I sigma ->
    I rho.
Proof.
  intros Hbody sigma rho Hstar.
  induction Hstar as [| s mid rho Hstep Hstar IH].
  - intro HI. exact HI.
  - intro HIs.
    apply IH.
    unfold while_body_den, pset_bind in Hstep.
    destruct Hstep as [s' [Hassume Hmid]].
    destruct Hassume as [Heq Hb]. subst s'.
    exact (Hbody s HIs Hb mid Hmid).
Qed.

(** Now the main theorem. *)
Theorem wlp_while_invariant (I : Sigma -> Prop) (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  (forall sigma, I sigma -> b sigma ->
    wlp body I sigma) ->
  (forall sigma, I sigma -> ~ b sigma -> Q sigma) ->
  forall sigma, I sigma -> wlp (while_den b body) Q sigma.
Proof.
  intros Hbody Hexit sigma HI.
  unfold wlp, while_den, pset_bind.
  intros tau [rho [Hstar Hassume]].
  destruct Hassume as [Heq Hnb]. subst tau.
  apply Hexit.
  - exact (star_preserves_invariant I b body Hbody sigma rho Hstar HI).
  - exact Hnb.
Qed.

(** *** B. WP While — Variant Rule (Lisbon)

    If there is a decreasing variant [V : nat -> Sigma -> Prop] where:
    - [V 0] implies [¬b] (loop exits)
    - [V (S n)] implies [b] (loop continues)
    - the body maps [V (S n)] to [V n] on SOME path

    Then some execution of the loop terminates in [Q].

    Derived from TOPLAS Lisbon Variant rule (§5.3.4, lines 1363–1375):

    <<
      ∀n. sure(P₀) ⊨ ¬b    sure(P_{n+1}) ⊨ b
           triple(sure(P_{n+1}), C, sometimes(P_n))
      ─────────────────────────────────────────────
      triple(∃n. sure(P_n), while b C, sometimes(P₀))
    >>
*)

(** Helper: build a while-loop execution trace from a variant. *)
Lemma variant_gives_star (V : nat -> Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma) :
  (forall sigma, V 0 sigma -> ~ b sigma) ->
  (forall n sigma, V (S n) sigma -> b sigma) ->
  (forall n sigma, V (S n) sigma -> wp body (V n) sigma) ->
  forall n sigma,
    V n sigma ->
    exists rho, star (while_body_den b body) sigma rho /\ V 0 rho.
Proof.
  intros HV0 HVS Hbody.
  induction n as [| n IH].
  - intros sigma HV. exists sigma. split.
    + apply star_refl.
    + exact HV.
  - intros sigma HVSn.
    destruct (Hbody n sigma HVSn) as [mid [Hmid HVn]].
    destruct (IH mid HVn) as [rho [Hstar HV0rho]].
    exists rho. split.
    + eapply star_step.
      * unfold while_body_den, pset_bind.
        exists sigma. split.
        -- unfold assume_den. split; [reflexivity | apply HVS with n; exact HVSn].
        -- exact Hmid.
      * exact Hstar.
    + exact HV0rho.
Qed.

Theorem wp_while_variant (V : nat -> Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) :
  (forall sigma, V 0 sigma -> ~ b sigma) ->
  (forall n sigma, V (S n) sigma -> b sigma) ->
  (forall n sigma, V (S n) sigma -> wp body (V n) sigma) ->
  (forall sigma, V 0 sigma -> Q sigma) ->
  forall n sigma, V n sigma -> wp (while_den b body) Q sigma.
Proof.
  intros HV0 HVS Hbody HQ n sigma HVn.
  destruct (variant_gives_star V b body HV0 HVS Hbody n sigma HVn)
    as [rho [Hstar HV0rho]].
  unfold wp, while_den, pset_bind.
  exists rho. split.
  - exists rho. split.
    + exact Hstar.
    + unfold assume_den. split; [reflexivity | apply HV0; exact HV0rho].
  - apply HQ. exact HV0rho.
Qed.

(** *** WP–WLP While Duality

    [wp[while b C]{Q}(σ) ↔ ¬ wlp[while b C]{¬Q}(σ)]

    This follows from the general WP–WLP duality specialized to
    [while_den]. *)

Theorem wp_wlp_while_duality (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wp (while_den b body) Q sigma <->
  ~ wlp (while_den b body) (fun tau => ~ Q tau) sigma.
Proof.
  exact (wp_wlp_duality (while_den b body) Q sigma).
Qed.

(** *** Denotational Characterization via Star

    These connect the WP/WLP transformers to the [star] inductive
    from [Lang.v] — the semantic anchor. *)

(** WP while: some execution through the starred body reaches ¬b ∧ Q. *)
Lemma wp_while_star (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wp (while_den b body) Q sigma <->
  exists rho, star (while_body_den b body) sigma rho /\
    ~ b rho /\ Q rho.
Proof.
  unfold wp, while_den, pset_bind. split.
  - intros [tau [[rho [Hstar Hassume]] HQ]].
    destruct Hassume as [Heq Hnb]. subst tau.
    exists rho. auto.
  - intros [rho [Hstar [Hnb HQ]]].
    exists rho. split.
    + exists rho. split.
      * exact Hstar.
      * unfold assume_den. split; [reflexivity | exact Hnb].
    + exact HQ.
Qed.

(** WLP while: all executions through the starred body satisfy ¬b → Q. *)
Lemma wlp_while_star (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp (while_den b body) Q sigma <->
  forall rho, star (while_body_den b body) sigma rho ->
    ~ b rho -> Q rho.
Proof.
  unfold wlp, while_den, pset_bind. split.
  - intros H rho Hstar Hnb.
    apply H. exists rho. split.
    + exact Hstar.
    + unfold assume_den. split; [reflexivity | exact Hnb].
  - intros H tau [rho [Hstar Hassume]].
    destruct Hassume as [Heq Hnb]. subst tau.
    exact (H rho Hstar Hnb).
Qed.

End WhileRules.
