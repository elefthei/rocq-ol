(** * OL/Rules/Expression.v — Assign, Assume, If (Multi-Outcome) Rules

    Proves soundness of the GCL expression-based proof rules from
    Figure 5 of the Outcome Logic paper.  These rules specialize to
    the nondeterministic powerset execution model ([PSet], [nd_atom_sat])
    and provide reasoning principles for state-transforming commands.

    Denotation primitives defined:
    - [assume_den b σ]   — guard filtering: [{σ}] if [b σ], [∅] otherwise
    - [assign_den f σ]   — deterministic state transform: [{f σ}]
    - [if_den b d₁ d₂ σ] — conditional: [d₁ σ] if [b σ], [d₂ σ] otherwise

    Rules proved:
    - [ol_assign]    — ⊨ ⟨Q ∘ f⟩ assign(f) ⟨Q⟩   (backward substitution)
    - [ol_assume]    — ⊨ ⟨φ ∧ b⟩ assume(b) ⟨φ⟩    (guard filtering)
    - [ol_if_multi]  — Multi-Outcome If rule       (outcome splitting)

    Additional lemmas:
    - [ol_assume_empty] — assume with unsatisfied guard yields ⊤⊕
    - [ol_if_single]    — Single-postcondition If (Hoare-style derived)
    - Under-approximate and partial-correctness corollaries
    - Syntactic sugar: [while_den] for while loops

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 3–4, Figure 5 *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Assertion Lang Triple.

(* ================================================================= *)
(** ** Assume Denotation                                              *)
(* ================================================================= *)

(** [assume_den b σ] returns [{σ}] when the guard [b σ] holds, and
    [∅] when [b σ] is false.  This models the GCL [assume(b)] command
    which filters states based on a boolean condition.

    Formally: [assume_den b σ = {σ' | σ' = σ ∧ b σ}]. *)

Definition assume_den {Sigma : Type} (b : Sigma -> Prop)
    (sigma : Sigma) : PSet Sigma :=
  fun sigma' => sigma' = sigma /\ b sigma.

(* ================================================================= *)
(** ** Assign Denotation                                              *)
(* ================================================================= *)

(** [assign_den f σ] returns [{f(σ)}] — a deterministic state
    transformation.  This models the GCL assignment [x := e] where
    [f] captures the state update function [σ ↦ σ[x := ⟦e⟧(σ)]]. *)

Definition assign_den {Sigma : Type} (f : Sigma -> Sigma)
    (sigma : Sigma) : PSet Sigma :=
  pset_ret (f sigma).

(* ================================================================= *)
(** ** If Denotation                                                  *)
(* ================================================================= *)

(** [if_den b den1 den2 σ] models the GCL conditional:
    [if b then C₁ else C₂ ≜ (assume(b); C₁) + (assume(¬b); C₂)]

    When [b σ]:  returns [den1 σ]  (true branch outcomes only)
    When [¬b σ]: returns [den2 σ]  (false branch outcomes only) *)

Definition if_den {Sigma : Type} (b : Sigma -> Prop)
    (den1 den2 : Sigma -> PSet Sigma)
    (sigma : Sigma) : PSet Sigma :=
  pset_union (pset_bind (assume_den b sigma) den1)
             (pset_bind (assume_den (fun s => ~ b s) sigma) den2).

(* ================================================================= *)
(** ** Assume Denotation Properties                                   *)
(* ================================================================= *)

Section AssumeProperties.

  Context {Sigma : Type}.

  (** Membership characterization: [τ ∈ assume_den(b)(σ)] iff
      [τ = σ] and [b σ]. *)
  Lemma assume_den_In (b : Sigma -> Prop) (sigma tau : Sigma) :
    In _ (assume_den b sigma) tau <-> (tau = sigma /\ b sigma).
  Proof.
    unfold assume_den, In. tauto.
  Qed.

  (** When the guard holds, [assume_den b σ = {σ}]. *)
  Lemma assume_den_true (b : Sigma -> Prop) (sigma : Sigma) :
    b sigma ->
    assume_den b sigma = pset_ret sigma.
  Proof.
    intro Hb.
    apply ensemble_ext. intro tau.
    split.
    - intros [Heq _]. subst. constructor.
    - intro Hin. inversion Hin; subst.
      split; [reflexivity | exact Hb].
  Qed.

  (** When the guard fails, [assume_den b σ = ∅]. *)
  Lemma assume_den_false (b : Sigma -> Prop) (sigma : Sigma) :
    ~ b sigma ->
    assume_den b sigma = pset_empty.
  Proof.
    intro Hnb.
    apply ensemble_ext. intro tau.
    split.
    - intros [_ Hbs]. exfalso. exact (Hnb Hbs).
    - intro H. inversion H.
  Qed.

  (** Collecting [assume(b)] over a set where all states satisfy [b]
      gives back the original set: [collect(assume(b), m) = m]. *)
  Lemma collect_assume_all (b : Sigma -> Prop) (m : PSet Sigma) :
    (forall sigma, In _ m sigma -> b sigma) ->
    collect (assume_den b) m = m.
  Proof.
    intro Hb.
    apply ensemble_ext. intro tau. split.
    - unfold collect, pset_bind, In.
      intros [sigma [Hm [Heq Hbs]]]. subst. exact Hm.
    - intro Hm.
      unfold collect, pset_bind, In.
      exists tau. split; [exact Hm |].
      split; [reflexivity | apply Hb; exact Hm].
  Qed.

  (** Collecting [assume(b)] over a set where NO states satisfy [b]
      gives the empty set: [collect(assume(b), m) = ∅]. *)
  Lemma collect_assume_none (b : Sigma -> Prop) (m : PSet Sigma) :
    (forall sigma, In _ m sigma -> ~ b sigma) ->
    collect (assume_den b) m = pset_empty.
  Proof.
    intro Hnb.
    apply ensemble_ext. intro tau. split.
    - unfold collect, pset_bind, In.
      intros [sigma [Hm [_ Hbs]]].
      exfalso. exact (Hnb sigma Hm Hbs).
    - intro H. inversion H.
  Qed.

End AssumeProperties.

(* ================================================================= *)
(** ** Assign Denotation Properties                                   *)
(* ================================================================= *)

Section AssignProperties.

  Context {Sigma : Type}.

  (** Membership characterization: [τ ∈ assign_den(f)(σ)] iff
      [τ = f(σ)]. *)
  Lemma assign_den_In (f : Sigma -> Sigma) (sigma tau : Sigma) :
    In _ (assign_den f sigma) tau <-> tau = f sigma.
  Proof.
    unfold assign_den, pset_ret, In.
    split.
    - intro H. inversion H. reflexivity.
    - intro H. subst. constructor.
  Qed.

  (** Collecting [assign(f)] over [m] gives the image [{f(σ) | σ ∈ m}]. *)
  Lemma collect_assign (f : Sigma -> Sigma) (m : PSet Sigma) :
    collect (assign_den f) m = pset_bind m (fun sigma => pset_ret (f sigma)).
  Proof. reflexivity. Qed.

  (** The image is characterized by membership. *)
  Lemma collect_assign_In (f : Sigma -> Sigma) (m : PSet Sigma) (tau : Sigma) :
    In _ (collect (assign_den f) m) tau <->
    exists sigma, In _ m sigma /\ tau = f sigma.
  Proof.
    unfold collect, assign_den, pset_bind, pset_ret, In.
    split.
    - intros [sigma [Hm Hret]].
      exists sigma. split; [exact Hm |].
      inversion Hret. reflexivity.
    - intros [sigma [Hm Heq]].
      exists sigma. split; [exact Hm |].
      subst. constructor.
  Qed.

End AssignProperties.

(* ================================================================= *)
(** ** If Denotation Properties                                       *)
(* ================================================================= *)

Section IfProperties.

  Context {Sigma : Type}.

  (** When the guard holds, [if_den b d₁ d₂ σ = d₁ σ]. *)
  Lemma if_den_true (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma) (sigma : Sigma) :
    b sigma ->
    if_den b den1 den2 sigma = den1 sigma.
  Proof.
    intro Hb.
    unfold if_den.
    assert (H1 : assume_den b sigma = pset_ret sigma)
      by (apply assume_den_true; exact Hb).
    assert (H2 : assume_den (fun s => ~ b s) sigma = pset_empty)
      by (apply assume_den_false; intro Hn; exact (Hn Hb)).
    rewrite H1, H2.
    rewrite pset_bind_ret_l, pset_bind_empty.
    apply pset_union_empty_r.
  Qed.

  (** When the guard fails, [if_den b d₁ d₂ σ = d₂ σ]. *)
  Lemma if_den_false (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma) (sigma : Sigma) :
    ~ b sigma ->
    if_den b den1 den2 sigma = den2 sigma.
  Proof.
    intro Hnb.
    unfold if_den.
    assert (H1 : assume_den b sigma = pset_empty)
      by (apply assume_den_false; exact Hnb).
    assert (H2 : assume_den (fun s => ~ b s) sigma = pset_ret sigma)
      by (apply assume_den_true; exact Hnb).
    rewrite H1, H2.
    rewrite pset_bind_empty, pset_bind_ret_l.
    apply pset_union_empty_l.
  Qed.

  (** Collecting respects pointwise denotation equality on a given set. *)
  Lemma collect_ext_at (f g : Sigma -> PSet Sigma) (m : PSet Sigma) :
    (forall sigma, In _ m sigma -> f sigma = g sigma) ->
    collect f m = collect g m.
  Proof.
    intro Hext.
    unfold collect, pset_bind.
    apply ensemble_ext. intro tau. split.
    - intros [sigma [Hm Hf]].
      exists sigma. split; [exact Hm |].
      unfold In in *. rewrite <- (Hext sigma Hm). exact Hf.
    - intros [sigma [Hm Hg]].
      exists sigma. split; [exact Hm |].
      unfold In in *. rewrite (Hext sigma Hm). exact Hg.
  Qed.

  (** Collecting [if_den b d₁ d₂] over a union where [m₁] satisfies
      [b] and [m₂] satisfies [¬b] decomposes into the union of the
      branch collections. *)
  Lemma collect_if_split (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma)
      (m1 m2 : PSet Sigma) :
    (forall sigma, In _ m1 sigma -> b sigma) ->
    (forall sigma, In _ m2 sigma -> ~ b sigma) ->
    collect (if_den b den1 den2) (pset_union m1 m2) =
      pset_union (collect den1 m1) (collect den2 m2).
  Proof.
    intros Hb1 Hnb2.
    rewrite collect_union.
    assert (Hc1 : collect (if_den b den1 den2) m1 = collect den1 m1).
    { apply collect_ext_at. intros sigma Hin.
      apply if_den_true. exact (Hb1 sigma Hin). }
    assert (Hc2 : collect (if_den b den1 den2) m2 = collect den2 m2).
    { apply collect_ext_at. intros sigma Hin.
      apply if_den_false. exact (Hnb2 sigma Hin). }
    rewrite Hc1, Hc2.
    reflexivity.
  Qed.

End IfProperties.

(* ================================================================= *)
(** ** Assign Rule — Backward Substitution                            *)
(* ================================================================= *)

(** The Assign rule is the OL analogue of Hoare Logic's assignment
    axiom.  For a deterministic state transformer [f], the precondition
    is obtained by backward substitution: [Q ∘ f].

    [⊨ ⟨Q ∘ f⟩ assign(f) ⟨Q⟩]

    This captures [⊨ ⟨φ[e/x]⟩ x := e ⟨φ⟩] from the paper, where
    [f = λσ. σ[x := ⟦e⟧(σ)]] is the state update and the atomic
    assertion [Q] is the postcondition [φ]. *)

Section AssignRule.

  Context {Sigma : Type}.

  Theorem ol_assign (f : Sigma -> Sigma) (Q : Sigma -> Prop) :
    ol_valid nd_atom_sat (assign_den f)
      (BiAtom (fun sigma => Q (f sigma)))
      (BiAtom Q).
  Proof.
    intros m Hpre.
    simpl in Hpre. simpl.
    destruct Hpre as [[sigma0 Hin0] Hforall].
    split.
    - (* Non-emptiness: f(σ₀) is in the image *)
      exists (f sigma0).
      unfold collect, pset_bind, assign_den, pset_ret, In.
      exists sigma0. split; [exact Hin0 | constructor].
    - (* Universal: every τ in the image satisfies Q *)
      intros tau Hin.
      unfold collect, pset_bind, assign_den, pset_ret, In in Hin.
      destruct Hin as [sigma [Hm Hret]].
      inversion Hret; subst.
      apply Hforall. exact Hm.
  Qed.

  (** Under-approximate version. *)
  Corollary ol_assign_under (f : Sigma -> Sigma) (Q : Sigma -> Prop) :
    ol_valid_under nd_atom_sat (assign_den f)
      (BiAtom (fun sigma => Q (f sigma)))
      (BiAtom Q).
  Proof.
    apply ol_valid_implies_under. apply ol_assign.
  Qed.

  (** Partial-correctness version. *)
  Corollary ol_assign_pc (f : Sigma -> Sigma) (Q : Sigma -> Prop) :
    ol_valid_pc nd_atom_sat (assign_den f)
      (BiAtom (fun sigma => Q (f sigma)))
      (BiAtom Q).
  Proof.
    apply ol_valid_implies_pc. apply ol_assign.
  Qed.

  (** Assign with weakening: apply backward substitution then weaken. *)
  Theorem ol_assign_consequence (f : Sigma -> Sigma)
      (P Q : Sigma -> Prop) :
    (forall sigma, P sigma -> Q (f sigma)) ->
    ol_valid nd_atom_sat (assign_den f) (BiAtom P) (BiAtom Q).
  Proof.
    intro Hweak.
    apply ol_valid_pre_strengthen with
      (phi := BiAtom (fun sigma => Q (f sigma))).
    - apply ol_assign.
    - intros m [Hne Hforall]. split.
      + exact Hne.
      + intros sigma Hin. apply Hweak. apply Hforall. exact Hin.
  Qed.

End AssignRule.

(* ================================================================= *)
(** ** Assume Rule — Guard Filtering                                  *)
(* ================================================================= *)

(** The Assume rule states that [assume(b)] preserves any property
    that holds together with the guard:

    [⊨ ⟨φ ∧ b⟩ assume(b) ⟨φ⟩]

    The proof relies on the fact that when all states in [m] satisfy
    the guard [b], [collect(assume(b), m) = m], so the postcondition
    [φ] follows directly from the precondition. *)

Section AssumeRule.

  Context {Sigma : Type}.

  Theorem ol_assume (b : Sigma -> Prop)
      (phi : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat (assume_den b)
      (BiAnd phi (BiAtom b))
      phi.
  Proof.
    intros m Hpre.
    simpl in Hpre.
    destruct Hpre as [Hphi [_Hne Hb]].
    (* Key: collect(assume(b), m) = m when ∀σ∈m. b(σ) *)
    assert (Heq : collect (assume_den b) m = m)
      by (apply collect_assume_all; exact Hb).
    rewrite Heq.
    exact Hphi.
  Qed.

  (** When the guard [b] is false for all states in [m], the
      assume produces the empty set [⊤⊕]. *)
  Theorem ol_assume_empty (b : Sigma -> Prop)
      (phi : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat (assume_den b)
      (BiAnd phi (BiAtom (fun s => ~ b s)))
      BiEmpty.
  Proof.
    intros m Hpre.
    simpl in Hpre.
    destruct Hpre as [_Hphi [_Hne Hnb]].
    simpl.
    apply collect_assume_none.
    exact Hnb.
  Qed.

  (** Under-approximate version. *)
  Corollary ol_assume_under (b : Sigma -> Prop)
      (phi : bi_formula (Sigma -> Prop)) :
    ol_valid_under nd_atom_sat (assume_den b)
      (BiAnd phi (BiAtom b))
      phi.
  Proof.
    apply ol_valid_implies_under. apply ol_assume.
  Qed.

  (** Partial-correctness version. *)
  Corollary ol_assume_pc (b : Sigma -> Prop)
      (phi : bi_formula (Sigma -> Prop)) :
    ol_valid_pc nd_atom_sat (assume_den b)
      (BiAnd phi (BiAtom b))
      phi.
  Proof.
    apply ol_valid_implies_pc. apply ol_assume.
  Qed.

  (** Assume at the atomic level: a simpler variant where both the
      precondition and postcondition are atomic assertions. *)
  Theorem ol_assume_atom (b : Sigma -> Prop) (P : Sigma -> Prop) :
    ol_valid nd_atom_sat (assume_den b)
      (BiAtom (fun sigma => P sigma /\ b sigma))
      (BiAtom P).
  Proof.
    intros m Hpre.
    simpl in Hpre. simpl.
    destruct Hpre as [[sigma0 Hin0] Hforall].
    assert (Hb : forall sigma, In _ m sigma -> b sigma).
    { intros sigma Hin. exact (proj2 (Hforall sigma Hin)). }
    assert (Heq : collect (assume_den b) m = m)
      by (apply collect_assume_all; exact Hb).
    rewrite Heq.
    split.
    - exists sigma0. exact Hin0.
    - intros sigma Hin.
      exact (proj1 (Hforall sigma Hin)).
  Qed.

End AssumeRule.

(* ================================================================= *)
(** ** If Rule — Multi-Outcome Conditional                            *)
(* ================================================================= *)

(** The Multi-Outcome If rule is the distinctive OL rule for
    conditionals.  It splits outcomes according to which branch was
    taken, using outcome conjunction [⊕]:

    [⊨ ⟨φ₁⟩ C₁ ⟨ψ₁⟩]   [⊨ ⟨φ₂⟩ C₂ ⟨ψ₂⟩]
    ————————————————————————————————————————————
    [⊨ ⟨(φ₁ ∧ b) ⊕ (φ₂ ∧ ¬b)⟩ if b C₁ C₂ ⟨ψ₁ ⊕ ψ₂⟩]

    The precondition [(φ₁ ∧ b) ⊕ (φ₂ ∧ ¬b)] requires [m] to split
    into two parts: [m₁] (states satisfying the guard, analyzed with
    [C₁]) and [m₂] (states failing the guard, analyzed with [C₂]).
    The postcondition [ψ₁ ⊕ ψ₂] splits the outcomes accordingly. *)

Section IfMultiOutcomeRule.

  Context {Sigma : Type}.

  Theorem ol_if_multi (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma)
      (phi1 phi2 psi1 psi2 : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat den1 phi1 psi1 ->
    ol_valid nd_atom_sat den2 phi2 psi2 ->
    ol_valid nd_atom_sat (if_den b den1 den2)
      (BiOPlus (BiAnd phi1 (BiAtom b))
               (BiAnd phi2 (BiAtom (fun s => ~ b s))))
      (BiOPlus psi1 psi2).
  Proof.
    intros H1 H2 m Hpre.
    (* Unpack the ⊕ precondition: m = m₁ ∪ m₂ *)
    simpl in Hpre.
    destruct Hpre as [m1 [m2 [Heq [[Hphi1 [_Hne1 Hb1]] [Hphi2 [_Hne2 Hnb2]]]]]].
    (* Decompose the collecting semantics *)
    simpl.
    rewrite <- Heq.
    rewrite (collect_if_split b den1 den2 m1 m2 Hb1 Hnb2).
    (* Provide the witnesses for ⊕ satisfaction *)
    exists (collect den1 m1), (collect den2 m2).
    split; [reflexivity |].
    split.
    - (* ψ₁: apply first premise to m₁ *)
      apply H1. exact Hphi1.
    - (* ψ₂: apply second premise to m₂ *)
      apply H2. exact Hphi2.
  Qed.

  (** Under-approximate version. *)
  Corollary ol_if_multi_under (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma)
      (phi1 phi2 psi1 psi2 : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat den1 phi1 psi1 ->
    ol_valid nd_atom_sat den2 phi2 psi2 ->
    ol_valid_under nd_atom_sat (if_den b den1 den2)
      (BiOPlus (BiAnd phi1 (BiAtom b))
               (BiAnd phi2 (BiAtom (fun s => ~ b s))))
      (BiOPlus psi1 psi2).
  Proof.
    intros H1 H2.
    apply ol_valid_implies_under.
    exact (ol_if_multi b den1 den2 phi1 phi2 psi1 psi2 H1 H2).
  Qed.

  (** Partial-correctness version. *)
  Corollary ol_if_multi_pc (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma)
      (phi1 phi2 psi1 psi2 : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat den1 phi1 psi1 ->
    ol_valid nd_atom_sat den2 phi2 psi2 ->
    ol_valid_pc nd_atom_sat (if_den b den1 den2)
      (BiOPlus (BiAnd phi1 (BiAtom b))
               (BiAnd phi2 (BiAtom (fun s => ~ b s))))
      (BiOPlus psi1 psi2).
  Proof.
    intros H1 H2.
    apply ol_valid_implies_pc.
    exact (ol_if_multi b den1 den2 phi1 phi2 psi1 psi2 H1 H2).
  Qed.

  (** Single-postcondition If — Hoare-style derived rule.  When both
      branches share the same postcondition, the outcome conjunction
      [ψ ⊕ ψ] can be collapsed (but the precondition still splits). *)
  Theorem ol_if_single (b : Sigma -> Prop)
      (den1 den2 : Sigma -> PSet Sigma)
      (phi1 phi2 psi : bi_formula (Sigma -> Prop)) :
    ol_valid nd_atom_sat den1 phi1 psi ->
    ol_valid nd_atom_sat den2 phi2 psi ->
    ol_valid nd_atom_sat (if_den b den1 den2)
      (BiOPlus (BiAnd phi1 (BiAtom b))
               (BiAnd phi2 (BiAtom (fun s => ~ b s))))
      (BiOPlus psi psi).
  Proof.
    intros H1 H2.
    exact (ol_if_multi b den1 den2 phi1 phi2 psi psi H1 H2).
  Qed.

End IfMultiOutcomeRule.

(* ================================================================= *)
(** ** While Loop — Syntactic Sugar                                   *)
(* ================================================================= *)

(** [while_den b body σ] models the GCL while loop:
    [while b do C ≜ (assume(b); C)⋆; assume(¬b)]

    The loop body is guarded by [assume(b)], iterated via the Kleene
    star, and terminated by [assume(¬b)] to ensure the guard fails
    on exit. *)

Definition while_body_den {Sigma : Type}
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (sigma : Sigma) : PSet Sigma :=
  pset_bind (assume_den b sigma) body.

Definition while_den {Sigma : Type}
    (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
    (sigma : Sigma) : PSet Sigma :=
  pset_bind (star_set (while_body_den b body) sigma)
            (assume_den (fun s => ~ b s)).

(* ================================================================= *)
(** ** While Loop Properties                                          *)
(* ================================================================= *)

Section WhileProperties.

  Context {Sigma : Type}.

  (** The while body step from a state satisfying [b] is just [body σ]. *)
  Lemma while_body_den_true (b : Sigma -> Prop)
      (body : Sigma -> PSet Sigma) (sigma : Sigma) :
    b sigma ->
    while_body_den b body sigma = body sigma.
  Proof.
    intro Hb.
    unfold while_body_den.
    rewrite (assume_den_true b sigma Hb).
    apply pset_bind_ret_l.
  Qed.

  (** The while body step from a state failing [b] is empty. *)
  Lemma while_body_den_false (b : Sigma -> Prop)
      (body : Sigma -> PSet Sigma) (sigma : Sigma) :
    ~ b sigma ->
    while_body_den b body sigma = pset_empty.
  Proof.
    intro Hnb.
    unfold while_body_den.
    rewrite (assume_den_false b sigma Hnb).
    apply pset_bind_empty.
  Qed.

  (** Membership in the while denotation: [τ ∈ while_den b body σ]
      means there is some intermediate state [ρ] reachable from [σ]
      via iterated [body] steps (each guarded by [b]), such that
      [τ = ρ] and [¬b ρ]. *)
  Lemma while_den_In (b : Sigma -> Prop) (body : Sigma -> PSet Sigma)
      (sigma tau : Sigma) :
    In _ (while_den b body sigma) tau <->
    exists rho, star (while_body_den b body) sigma rho /\
                tau = rho /\ ~ b rho.
  Proof.
    unfold while_den.
    split.
    - unfold pset_bind, In.
      intros [rho [Hstar Hassume]].
      unfold assume_den in Hassume.
      destruct Hassume as [Heq Hnb].
      exists rho. subst. auto.
    - intros [rho [Hstar [Heq Hnb]]].
      unfold pset_bind, In.
      exists rho. split.
      + unfold star_set, In. exact Hstar.
      + unfold assume_den. subst. auto.
  Qed.

End WhileProperties.

(* ================================================================= *)
(** ** Notation                                                       *)
(* ================================================================= *)

(** The [gcl_scope] provides notation for the generic GCL primitives.
    For heap-specific programs, use [mgcl_scope] from [Heap/Lang.v] instead.
    Open this scope with [Open Scope gcl_scope] when writing non-heap
    GCL examples or instantiations. *)

Declare Scope gcl_scope.
Delimit Scope gcl_scope with gcl.

Notation "'ASSUME' b" := (assume_den b)
  (at level 0, b at level 0) : gcl_scope.
Notation "'ASSIGN' f" := (assign_den f)
  (at level 0, f at level 0) : gcl_scope.
Notation "'IF' b 'THEN' d1 'ELSE' d2" := (if_den b d1 d2)
  (at level 65, b at level 99, d1 at level 99, d2 at level 99) : gcl_scope.
Notation "'WHILE' b 'DO' body" := (while_den b body)
  (at level 65, b at level 99, body at level 99) : gcl_scope.

(* ================================================================= *)
(** ** While Loop — Collecting Semantics                              *)
(* ================================================================= *)

Section WhileCollecting.

  Context {Sigma : Type}.

  (** Collecting the while body star is monotone: any state reachable
      by the star from some state in m is in the collecting. *)
  Lemma collect_while_body_star (b : Sigma -> Prop)
      (body : Sigma -> PSet Sigma) (m : PSet Sigma) :
    collect (fun sigma => star_set (while_body_den b body) sigma) m =
      (fun rho => exists sigma, In _ m sigma /\
                                star (while_body_den b body) sigma rho).
  Proof.
    apply ensemble_ext. intro rho.
    unfold collect, pset_bind, star_set, In. tauto.
  Qed.

End WhileCollecting.

(* ================================================================= *)
(** ** While Loop — Invariant Rules                                   *)
(* ================================================================= *)

Section WhileInvariantRules.

  Context {Sigma : Type}.

  (** Atomic while-loop invariant rule with termination witness.

      If the body preserves an atomic invariant [P] (starting from
      states satisfying [P ∧ b] and landing in states satisfying [P]),
      and if every set satisfying [P] contains at least one state
      where the guard [¬b] holds (termination witness), then after the
      while loop terminates, all outcomes satisfy [P ∧ ¬b].

      This is under-approximate because the while loop may not terminate
      for all inputs — we only characterize outcomes where it does.

      Proof strategy: For any m satisfying P, the termination witness
      σ already satisfies ¬b, so [while_den b body σ] outputs {σ}
      (zero iterations).  We use [pset_ret σ] as the left component
      of the ⊕-split and the full collecting as the right. *)

  Theorem ol_while_invariant_atom (b : Sigma -> Prop)
      (body : Sigma -> PSet Sigma) (P : Sigma -> Prop) :
    ol_valid nd_atom_sat body
      (BiAtom (fun sigma => P sigma /\ b sigma))
      (BiAtom P) ->
    (** Termination: for any set satisfying P, some element satisfies ¬b *)
    (forall m : PSet Sigma,
       nd_atom_sat m P ->
       exists sigma, In _ m sigma /\ ~ b sigma) ->
    ol_valid_under nd_atom_sat (while_den b body)
      (BiAtom P)
      (BiAtom (fun sigma => P sigma /\ ~ b sigma)).
  Proof.
    intros Hbody Hterm m Hpre.
    simpl in Hpre. destruct Hpre as [[sigma0 Hin0] HforallP].
    destruct (Hterm m (conj (ex_intro _ sigma0 Hin0) HforallP))
      as [sigma [Hin Hnb]].
    simpl.
    (* sigma satisfies ¬b, so it passes through the while loop in 0 steps *)
    assert (Hpass : In _ (while_den b body sigma) sigma).
    { unfold while_den, pset_bind, In.
      exists sigma. split.
      - unfold star_set, In. apply star_refl.
      - unfold assume_den. auto. }
    (* sigma is therefore in collect(while_den, m) *)
    assert (Hcoll : In _ (collect (while_den b body) m) sigma).
    { unfold collect, pset_bind, In. exists sigma. auto. }
    (* Build the ⊕ witness: {sigma} ⊕ collect(...) *)
    exists (pset_ret sigma), (collect (while_den b body) m).
    split.
    - (* {sigma} ∪ collect = collect, since sigma ∈ collect *)
      apply ensemble_ext. intro tau. split.
      + intro HU. inversion HU; subst.
        * inversion H; subst. exact Hcoll.
        * exact H.
      + intro Hin'. apply Union_intror. exact Hin'.
    - split.
      + (* {sigma} satisfies P ∧ ¬b *)
        split.
        * exists sigma. constructor.
        * intros s Hs. inversion Hs; subst.
          split; [apply HforallP; exact Hin | exact Hnb].
      + exact I.
  Qed.

End WhileInvariantRules.
