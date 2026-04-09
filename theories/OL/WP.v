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
From OL Require Import Monad Assertion Lang SP Triple.
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
(** ** Falsification via WP/WLP Duality                              *)
(* ================================================================= *)

(** The four falsification equivalences from WP-HLL-OL Thm 5.1.
    These connect falsifying a correctness/incorrectness statement
    to the dual transformer. *)

Section Falsification.

Context {Sigma : Type}.

(** Partial correctness falsification: the Hoare triple fails iff
    there is a witness state in P that reaches a ¬Q state. *)
Theorem hoare_falsification_wp (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  ~ (forall sigma, P sigma -> wlp denote Q sigma) <->
  exists sigma, P sigma /\ wp denote (fun tau => ~ Q tau) sigma.
Proof.
  split.
  - intro Hfail. apply NNPP. intro Hno.
    apply Hfail. intros sigma HP.
    unfold wlp. intros tau Hden.
    apply NNPP. intro HnQ.
    apply Hno. exists sigma. split; [exact HP|].
    exists tau. auto.
  - intros [sigma [HP [tau [Hden HnQ]]]] Hall.
    exact (HnQ (Hall sigma HP tau Hden)).
Qed.

(** Lisbon falsification: the reachability triple fails iff
    there is a witness state in P where all paths avoid Q. *)
Theorem lisbon_falsification_wlp (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  ~ (forall sigma, P sigma -> wp denote Q sigma) <->
  exists sigma, P sigma /\ wlp denote (fun tau => ~ Q tau) sigma.
Proof.
  split.
  - intro Hfail. apply NNPP. intro Hno.
    apply Hfail. intros sigma HP.
    apply NNPP. intro Hnwp.
    apply Hno. exists sigma. split; [exact HP|].
    unfold wlp. intros tau Hden HQ.
    apply Hnwp. exists tau. auto.
  - intros [sigma [HP Hwlp]] Hall.
    destruct (Hall sigma HP) as [tau [Hden HQ]].
    exact (Hwlp tau Hden HQ).
Qed.

(** Pointwise WP–WLP falsification duality: failing to have all paths
    satisfy Q is the same as having some path satisfy ¬Q. *)
Theorem wlp_falsification_pointwise (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  ~ wlp denote Q sigma <-> wp denote (fun tau => ~ Q tau) sigma.
Proof.
  split.
  - intro Hn. apply NNPP. intro Hno.
    apply Hn. unfold wlp. intros tau Hden.
    apply NNPP. intro HnQ.
    apply Hno. exists tau. auto.
  - intros [tau [Hden HnQ]] Hwlp.
    exact (HnQ (Hwlp tau Hden)).
Qed.

(** Pointwise WP falsification: failing to have some path
    satisfy Q means all paths satisfy ¬Q. *)
Theorem wp_falsification_pointwise (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  ~ wp denote Q sigma <-> wlp denote (fun tau => ~ Q tau) sigma.
Proof.
  split.
  - intro Hn. unfold wlp. intros tau Hden HQ.
    apply Hn. exists tau. auto.
  - intros Hwlp [tau [Hden HQ]].
    exact (Hwlp tau Hden HQ).
Qed.

End Falsification.

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

(** Every state reachable via [star (while_body_den b body)] from
    a state satisfying [I] also satisfies [I]. *)
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

(** *** C. General WLP While Rule (TOPLAS §4.1, lines 1093–1106)

    Two families of assertions φ_n (guard true) and ψ_n (guard false):
    - φ_n ⊨ b  and  ψ_n ⊨ ¬b
    - body maps each φ_n to φ_{n+1} ∨ ψ_{n+1} on ALL paths

    Then: (φ₀ ∨ ψ₀) → wlp[while b C]{∃n. ψ_n}

    This generalizes [wlp_while_invariant] (set φ_n = I∧b, ψ_n = I∧¬b)
    and is the WLP specialization of the TOPLAS While rule. *)

(** Convergence condition for assertion families (TOPLAS §3.2).
    [Converges psi psi_inf] holds when [psi_inf] is the pointwise
    union of the family [psi]:  σ ∈ ψ_∞  ↔  ∃n. σ ∈ ψ_n.

    For the Boolean (nondeterministic) semiring, convergence is trivially
    satisfiable by taking ψ_∞(σ) := ∃n. ψ_n(σ). *)
Definition Converges {Sigma : Type}
    (psi : nat -> Sigma -> Prop) (psi_inf : Sigma -> Prop) : Prop :=
  forall sigma, psi_inf sigma <-> exists n, psi n sigma.

(** Helper: if ¬b σ, no while-body step from σ is possible. *)
Lemma while_body_no_step (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (sigma tau : Sigma) :
  ~ b sigma ->
  ~ In _ (while_body_den b body sigma) tau.
Proof.
  intros Hnb [s [[Heq Hb] _]]. subst. exact (Hnb Hb).
Qed.

(** Helper: if ¬b σ, star from σ is trivial (rho = sigma). *)
Lemma star_exit_trivial (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (sigma rho : Sigma) :
  ~ b sigma ->
  star (while_body_den b body) sigma rho ->
  rho = sigma.
Proof.
  intros Hnb Hstar.
  inversion Hstar; subst.
  - reflexivity.
  - exfalso. exact (while_body_no_step b body sigma _ Hnb H).
Qed.

(** Helper: from a φ_k state, every star-exit state satisfies some ψ_n. *)
Lemma general_while_exit
    (phi psi : nat -> Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma) :
  (forall n sigma, phi n sigma -> b sigma) ->
  (forall n sigma, psi n sigma -> ~ b sigma) ->
  (forall n sigma, phi n sigma ->
    wlp body (fun tau => phi (S n) tau \/ psi (S n) tau) sigma) ->
  forall sigma rho,
    star (while_body_den b body) sigma rho ->
    forall k, phi k sigma ->
    ~ b rho ->
    exists n, psi n rho.
Proof.
  intros Hphi_b Hpsi_nb Hbody.
  intros sigma rho Hstar.
  induction Hstar as [| s mid rho' Hstep Hstar' IH].
  - intros k Hphi Hnb.
    exfalso. exact (Hnb (Hphi_b k sigma Hphi)).
  - intros k Hphi Hnb.
    unfold while_body_den, pset_bind in Hstep.
    destruct Hstep as [s' [[Heq Hb] Hmid]]. subst s'.
    destruct (Hbody k s Hphi mid Hmid) as [Hphi' | Hpsi'].
    + exact (IH (S k) Hphi' Hnb).
    + assert (rho' = mid).
      { exact (star_exit_trivial b body mid rho'
                 (Hpsi_nb (S k) mid Hpsi') Hstar'). }
      subst rho'. exists (S k). exact Hpsi'.
Qed.

(** The general WLP while rule with two assertion families. *)
Theorem wlp_while_general
    (phi psi : nat -> Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) :
  (forall n sigma, phi n sigma -> b sigma) ->
  (forall n sigma, psi n sigma -> ~ b sigma) ->
  (forall n sigma, phi n sigma ->
    wlp body (fun tau => phi (S n) tau \/ psi (S n) tau) sigma) ->
  (forall sigma, (exists n, psi n sigma) -> Q sigma) ->
  forall sigma, (phi 0 sigma \/ psi 0 sigma) ->
    wlp (while_den b body) Q sigma.
Proof.
  intros Hphi_b Hpsi_nb Hbody HQ sigma Hinit.
  apply wlp_while_star.
  intros rho Hstar Hnb.
  destruct Hinit as [Hphi0 | Hpsi0].
  - apply HQ.
    exact (general_while_exit phi psi b body
             Hphi_b Hpsi_nb Hbody sigma rho Hstar 0 Hphi0 Hnb).
  - assert (rho = sigma).
    { exact (star_exit_trivial b body sigma rho
               (Hpsi_nb 0 sigma Hpsi0) Hstar). }
    subst rho. apply HQ. exists 0. exact Hpsi0.
Qed.

(** Corollary: the invariant rule is a special case with constant families.
    Set φ_n = I∧b and ψ_n = I∧¬b. *)
Corollary wlp_while_invariant_from_general (I : Sigma -> Prop)
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) :
  (forall sigma, I sigma -> b sigma -> wlp body I sigma) ->
  (forall sigma, I sigma -> ~ b sigma -> Q sigma) ->
  forall sigma, I sigma -> wlp (while_den b body) Q sigma.
Proof.
  intros Hbody Hexit sigma HI.
  apply (wlp_while_general
    (fun _ sigma => I sigma /\ b sigma)
    (fun _ sigma => I sigma /\ ~ b sigma)
    b body Q).
  - intros _ s [_ Hb]. exact Hb.
  - intros _ s [_ Hnb]. exact Hnb.
  - intros n s [HIs Hbs]. unfold wlp. intros tau Hden.
    destruct (classic (b tau)) as [Hbt | Hnbt].
    + left. split; [exact (Hbody s HIs Hbs tau Hden) | exact Hbt].
    + right. split; [exact (Hbody s HIs Hbs tau Hden) | exact Hnbt].
  - intros s [n [HIs Hnbs]]. exact (Hexit s HIs Hnbs).
  - destruct (classic (b sigma)) as [Hb | Hnb].
    + left. split; auto.
    + right. split; auto.
Qed.

End WhileRules.

(* ================================================================= *)
(** ** WP/WLP for If-Then-Else                                       *)
(* ================================================================= *)

(** The GCL conditional [if b then C₁ else C₂] is encoded as
    [(assume b; C₁) + (assume ¬b; C₂)].  WP and WLP decompose
    according to the guard. *)

Section WPIf.

Context {Sigma : Type}.

Lemma wp_if (b : Sigma -> Prop) (d1 d2 : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wp (if_den b d1 d2) Q sigma <->
  (b sigma /\ wp d1 Q sigma) \/ (~ b sigma /\ wp d2 Q sigma).
Proof.
  unfold wp, if_den. split.
  - intros [tau [HU HQ]].
    inversion HU; subst.
    + destruct H as [s [[Heq Hb] Hd1]]. subst s.
      left. split; [exact Hb | exists tau; auto].
    + destruct H as [s [[Heq Hnb] Hd2]]. subst s.
      right. split; [exact Hnb | exists tau; auto].
  - intros [[Hb [tau [Hd1 HQ]]] | [Hnb [tau [Hd2 HQ]]]].
    + exists tau. split; [| exact HQ].
      apply Union_introl. exists sigma.
      split; [split; [reflexivity | exact Hb] | exact Hd1].
    + exists tau. split; [| exact HQ].
      apply Union_intror. exists sigma.
      split; [split; [reflexivity | exact Hnb] | exact Hd2].
Qed.

Lemma wlp_if (b : Sigma -> Prop) (d1 d2 : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp (if_den b d1 d2) Q sigma <->
  (b sigma -> wlp d1 Q sigma) /\ (~ b sigma -> wlp d2 Q sigma).
Proof.
  unfold wlp, if_den. split.
  - intros H. split.
    + intros Hb tau Hd1. apply H.
      apply Union_introl. exists sigma.
      split; [split; [reflexivity | exact Hb] | exact Hd1].
    + intros Hnb tau Hd2. apply H.
      apply Union_intror. exists sigma.
      split; [split; [reflexivity | exact Hnb] | exact Hd2].
  - intros [H1 H2] tau HU.
    inversion HU; subst.
    + destruct H as [s [[Heq Hb] Hd1]]. subst s.
      exact (H1 Hb tau Hd1).
    + destruct H as [s [[Heq Hnb] Hd2]]. subst s.
      exact (H2 Hnb tau Hd2).
Qed.

End WPIf.

(* ================================================================= *)
(** ** WP/WLP for Assignment                                         *)
(* ================================================================= *)

(** Assignment [assign f] maps σ to {f(σ)}.  WP/WLP reduce
    to backward substitution: [Q(f(σ))]. *)

Section WPAssign.

Context {Sigma : Type}.

Lemma wp_assign (f : Sigma -> Sigma) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wp (assign_den f) Q sigma <-> Q (f sigma).
Proof.
  unfold wp, assign_den. split.
  - intros [tau [Hret HQ]]. inversion Hret. subst. exact HQ.
  - intro HQ. exists (f sigma). split; [constructor | exact HQ].
Qed.

Lemma wlp_assign (f : Sigma -> Sigma) (Q : Sigma -> Prop)
    (sigma : Sigma) :
  wlp (assign_den f) Q sigma <-> Q (f sigma).
Proof.
  unfold wlp, assign_den. split.
  - intro H. apply H. constructor.
  - intros HQ tau Hret. inversion Hret. subst. exact HQ.
Qed.

End WPAssign.

(* ================================================================= *)
(** ** Compositional Hoare/Lisbon Rules (TOPLAS §4.1)                *)
(* ================================================================= *)

(** These derived rules express the standard Hoare Logic and
    Lisbon Logic sequencing and conditional rules using WLP and WP.

    - Hoare {P}C{Q} ↔ ∀σ. P(σ) → wlp(C)(Q)(σ)
    - Lisbon {P}C{Q} ↔ ∀σ. P(σ) → wp(C)(Q)(σ) *)

Section HoareLisbonSeq.

Context {Atom Sigma : Type}.
Variable atom_den : Atom -> Sigma -> PSet Sigma.

Let den := ol_denote atom_den.

(** Hoare (WLP) sequential composition. *)
Lemma hoare_seq_wlp (P Q R : Sigma -> Prop)
    (C1 C2 : ol_prog Atom) :
  (forall sigma, P sigma -> wlp (den C1) Q sigma) ->
  (forall sigma, Q sigma -> wlp (den C2) R sigma) ->
  forall sigma, P sigma -> wlp (den (OLSeq C1 C2)) R sigma.
Proof.
  intros H1 H2 sigma HP.
  apply (wlp_seq atom_den).
  apply (wlp_monotone (den C1) Q (wlp (den C2) R)).
  - exact H2.
  - exact (H1 sigma HP).
Qed.

(** Lisbon (WP) sequential composition. *)
Lemma lisbon_seq_wp (P Q R : Sigma -> Prop)
    (C1 C2 : ol_prog Atom) :
  (forall sigma, P sigma -> wp (den C1) Q sigma) ->
  (forall sigma, Q sigma -> wp (den C2) R sigma) ->
  forall sigma, P sigma -> wp (den (OLSeq C1 C2)) R sigma.
Proof.
  intros H1 H2 sigma HP.
  apply (wp_seq atom_den).
  apply (wp_monotone (den C1) Q (wp (den C2) R)).
  - exact H2.
  - exact (H1 sigma HP).
Qed.

End HoareLisbonSeq.

Section HoareLisbonIf.

Context {Sigma : Type}.

(** Hoare (WLP) conditional rule. *)
Lemma hoare_if_wlp (P Q : Sigma -> Prop)
    (b : Sigma -> Prop) (d1 d2 : Sigma -> PSet Sigma) :
  (forall sigma, P sigma -> b sigma -> wlp d1 Q sigma) ->
  (forall sigma, P sigma -> ~ b sigma -> wlp d2 Q sigma) ->
  forall sigma, P sigma -> wlp (if_den b d1 d2) Q sigma.
Proof.
  intros H1 H2 sigma HP.
  apply wlp_if. split.
  - intro Hb. exact (H1 sigma HP Hb).
  - intro Hnb. exact (H2 sigma HP Hnb).
Qed.

(** Lisbon (WP) conditional rule. *)
Lemma lisbon_if_wp (P Q : Sigma -> Prop)
    (b : Sigma -> Prop) (d1 d2 : Sigma -> PSet Sigma) :
  (forall sigma, P sigma -> b sigma -> wp d1 Q sigma) ->
  (forall sigma, P sigma -> ~ b sigma -> wp d2 Q sigma) ->
  forall sigma, P sigma -> wp (if_den b d1 d2) Q sigma.
Proof.
  intros H1 H2 sigma HP.
  destruct (classic (b sigma)) as [Hb | Hnb].
  - apply wp_if. left. split; [exact Hb | exact (H1 sigma HP Hb)].
  - apply wp_if. right. split; [exact Hnb | exact (H2 sigma HP Hnb)].
Qed.

(** Hoare (WLP) consequence / weakening rule. *)
Lemma hoare_consequence_wlp (P P' Q Q' : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) :
  (forall sigma, P sigma -> P' sigma) ->
  (forall sigma, Q' sigma -> Q sigma) ->
  (forall sigma, P' sigma -> wlp denote Q' sigma) ->
  forall sigma, P sigma -> wlp denote Q sigma.
Proof.
  intros HP HQ Hwlp sigma HPsig.
  apply (wlp_monotone denote Q' Q HQ).
  exact (Hwlp sigma (HP sigma HPsig)).
Qed.

(** Lisbon (WP) consequence / weakening rule. *)
Lemma lisbon_consequence_wp (P P' Q Q' : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) :
  (forall sigma, P sigma -> P' sigma) ->
  (forall sigma, Q' sigma -> Q sigma) ->
  (forall sigma, P' sigma -> wp denote Q' sigma) ->
  forall sigma, P sigma -> wp denote Q sigma.
Proof.
  intros HP HQ Hwp sigma HPsig.
  apply (wp_monotone denote Q' Q HQ).
  exact (Hwp sigma (HP sigma HPsig)).
Qed.

End HoareLisbonIf.

(* ================================================================= *)
(** ** TOPLAS While-OL Rule — Partial Correctness (Theorem 5.9)       *)
(* ================================================================= *)

(** Two assertion families φ_n (guard-true) and ψ_n (guard-false) with
    convergence to ψ_∞.  This lifts [wlp_while_general] from pointwise
    predicate-transformer style to OL partial-correctness triples under
    [nd_atom_sat].

    Precondition: all states satisfy [φ_0 ∨ ψ_0].
    Postcondition: all terminating outcomes satisfy [ψ_∞], OR no outcomes.

    The partial-correctness form [ol_valid_pc] is needed because the WLP
    (demonic) while rule cannot guarantee non-empty outcomes — it only
    says that IF an outcome exists, it satisfies [ψ_∞]. *)

Section TOPLASWhileOL.

  Context {Sigma : Type}.

  Theorem ol_while_general_toplas_pc
      (phi psi : nat -> Sigma -> Prop)
      (psi_inf : Sigma -> Prop)
      (b : Sigma -> Prop) (body : Sigma -> PSet Sigma) :
    Converges psi psi_inf ->
    (forall n sigma, phi n sigma -> b sigma) ->
    (forall n sigma, psi n sigma -> ~ b sigma) ->
    (forall n sigma, phi n sigma ->
      wlp body (fun tau => phi (S n) tau \/ psi (S n) tau) sigma) ->
    ol_valid_pc nd_atom_sat (while_den b body)
      (BiAtom (fun sigma => phi 0 sigma \/ psi 0 sigma))
      (BiAtom psi_inf).
  Proof.
    intros Hconv Hphi_b Hpsi_nb Hbody m Hpre.
    simpl.
    destruct Hpre as [[s0 Hs0] HforallP].
    destruct (classic (exists tau, In _ (collect (while_den b body) m) tau))
      as [[tau0 Htau0] | Hempty].
    - (* Non-empty: all outcomes satisfy psi_inf *)
      left. split.
      + exists tau0. exact Htau0.
      + intros tau Htau.
        unfold collect, pset_bind, In in Htau.
        destruct Htau as [sigma [Hinm Htau_in_while]].
        specialize (HforallP sigma Hinm).
        assert (Hwlp : wlp (while_den b body) psi_inf sigma).
        { apply (wlp_while_general phi psi b body).
          - exact Hphi_b.
          - exact Hpsi_nb.
          - exact Hbody.
          - intros s [n Hpsi_n]. apply Hconv. exists n. exact Hpsi_n.
          - exact HforallP. }
        exact (Hwlp tau Htau_in_while).
    - (* Empty: right disjunct (BiEmpty) *)
      right.
      apply ensemble_ext. intro tau. split.
      + intro Hin. exfalso. apply Hempty. exists tau. exact Hin.
      + intro Hempty'. inversion Hempty'.
  Qed.

End TOPLASWhileOL.
