(** * OL/WHP.v — Weakest Hyper Pre Transformer and Subsumption

    Defines the Weakest Hyper Pre transformer (WHP) from arXiv:2404.05097
    and proves that Hoare Logic, Lisbon Logic, and Incorrectness Logic
    are all subsumed by OL via the □ and ◇ modalities.

    Main definitions:
    - [hyperquantity]      — predicate on predicates: (Σ→Prop)→Prop
    - [box Q] (□Q)         — ρ ⊆ Q   (must / always)
    - [diamond Q] (◇Q)     — Q ∩ ρ ≠ ∅ (may / sometimes)
    - [whp denote F P]     — F(sp(denote, P))

    Subsumption theorems (TOPLAS §5.5, Table 4):
    - Hoare  ↔ □P ⊆ whp(□Q)
    - Lisbon ↔ ◇P ⊆ whp(◇Q)

    Reference:
    - arXiv:2404.05097, §4 (WHP definition, characterization)
    - arXiv:2401.04594, §5.5 (□/◇ modalities, subsumption) *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Lang SP WP.
From OL.Rules Require Import Expression.

(* ================================================================= *)
(** ** Hyperquantities and Modalities                                 *)
(* ================================================================= *)

Section Modalities.

Context {Sigma : Type}.

(** A hyperquantity is a predicate on predicates (outcomes → Prop).
    In the Boolean semiring, this is (Σ → Prop) → Prop. *)
Definition hyperquantity := (Sigma -> Prop) -> Prop.

(** □Q (box / must / always): every state in ρ satisfies Q.
    Corresponds to ∀-modality / Hoare Logic. *)
Definition box (Q : Sigma -> Prop) : hyperquantity :=
  fun rho => forall sigma, rho sigma -> Q sigma.

(** ◇Q (diamond / may / sometimes): some state in ρ satisfies Q.
    Corresponds to ∃-modality / Lisbon Logic. *)
Definition diamond (Q : Sigma -> Prop) : hyperquantity :=
  fun rho => exists sigma, rho sigma /\ Q sigma.

(** □ and ◇ are De Morgan duals (requires classical logic). *)
Lemma box_diamond_dual (Q : Sigma -> Prop) (rho : Sigma -> Prop) :
  box Q rho <-> ~ diamond (fun s => ~ Q s) rho.
Proof.
  unfold box, diamond. split.
  - intros Hall [sigma [Hin HnQ]]. exact (HnQ (Hall sigma Hin)).
  - intros Hnn sigma Hin. apply NNPP. intro HnQ.
    apply Hnn. exists sigma. auto.
Qed.

Lemma diamond_box_dual (Q : Sigma -> Prop) (rho : Sigma -> Prop) :
  diamond Q rho <-> ~ box (fun s => ~ Q s) rho.
Proof.
  unfold box, diamond. split.
  - intros [sigma [Hin HQ]] Hall. exact (Hall sigma Hin HQ).
  - intro Hnn. apply NNPP. intro Hn.
    apply Hnn. intros sigma Hin HQ.
    apply Hn. exists sigma. auto.
Qed.

End Modalities.

(* ================================================================= *)
(** ** Weakest Hyper Pre Definition                                   *)
(* ================================================================= *)

Section WHPDef.

Context {Sigma : Type}.

(** [whp denote F P = F(sp denote P)]
    The WHP transformer simply applies the hyperquantity [F] to the
    strongest post of [P].  This is the key simplification from
    Theorem 4.3 of the WHP paper: [whp[C]\{F\}(f) = F(sp[C]\{f\})]. *)

Definition whp (denote : Sigma -> PSet Sigma)
    (F : hyperquantity) (P : Sigma -> Prop) : Prop :=
  F (sp denote P).

End WHPDef.

(* ================================================================= *)
(** ** Subsumption Theorems                                           *)
(* ================================================================= *)

(** These theorems show that Hoare Logic and Lisbon Logic are
    special cases of OL via the □/◇ modalities applied to WHP.
    From TOPLAS paper §5.5 and WHP paper Table 4. *)

Section Subsumption.

Context {Sigma : Type}.

(** *** Hoare Logic Subsumption

    Hoare {P} C {Q} ↔ □P ⊆ whp[C]{□Q}
    ↔ ∀ρ⊆P. sp(C,ρ) ⊆ Q
    ↔ ∀σ∈P. ∀τ∈⟦C⟧(σ). Q(τ) *)

Theorem hoare_iff_box_whp (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  (forall sigma, P sigma ->
    forall tau, In _ (denote sigma) tau -> Q tau) <->
  (forall rho, box P rho -> whp denote (box Q) rho).
Proof.
  unfold box, whp, sp, collect, pset_bind. split.
  - intros Hhoare rho Hsub tau [sigma [Hin Hden]].
    exact (Hhoare sigma (Hsub sigma Hin) tau Hden).
  - intros Hwhp sigma HP tau Hden.
    assert (Hsingle : box P (pset_ret sigma)).
    { intros s Hs. inversion Hs. subst. exact HP. }
    apply (Hwhp (pset_ret sigma) Hsingle tau).
    exists sigma. split; [constructor | exact Hden].
Qed.

(** Reformulation: WLP is exactly □-WHP. *)
Theorem wlp_iff_box_whp (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wlp denote Q sigma <->
  whp denote (box Q) (pset_ret sigma).
Proof.
  unfold wlp, whp, box, sp, collect, pset_bind. split.
  - intros Hwlp tau [s [Hs Hden]].
    inversion Hs. subst. exact (Hwlp tau Hden).
  - intros Hwhp tau Hden.
    apply (Hwhp tau). exists sigma. split; [constructor | exact Hden].
Qed.

(** *** Lisbon Logic Subsumption

    Lisbon {P} C {Q} ↔ ◇P ⊆ whp[C]{◇Q}
    ↔ ∀σ∈P. ∃τ∈⟦C⟧(σ). Q(τ) *)

Theorem lisbon_iff_diamond_whp (P : Sigma -> Prop)
    (denote : Sigma -> PSet Sigma) (Q : Sigma -> Prop) :
  (forall sigma, P sigma ->
    exists tau, In _ (denote sigma) tau /\ Q tau) <->
  (forall rho, diamond P rho -> whp denote (diamond Q) rho).
Proof.
  unfold diamond, whp, sp, collect, pset_bind. split.
  - intros Hlisbon rho [sigma [Hin HP]].
    destruct (Hlisbon sigma HP) as [tau [Hden HQ]].
    exists tau. split; [|exact HQ].
    exists sigma. auto.
  - intros Hwhp sigma HP.
    assert (Hsingle : diamond P (pset_ret sigma)).
    { exists sigma. split; [constructor | exact HP]. }
    destruct (Hwhp (pset_ret sigma) Hsingle) as [tau [[s [Hs Hden]] HQ]].
    inversion Hs. subst. exists tau. auto.
Qed.

(** Reformulation: WP is exactly ◇-WHP. *)
Theorem wp_iff_diamond_whp (denote : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  wp denote Q sigma <->
  whp denote (diamond Q) (pset_ret sigma).
Proof.
  unfold wp, whp, diamond, sp, collect, pset_bind. split.
  - intros [tau [Hden HQ]].
    exists tau. split; [|exact HQ].
    exists sigma. split; [constructor | exact Hden].
  - intros [tau [[s [Hs Hden]] HQ]].
    inversion Hs. subst. exists tau. auto.
Qed.

End Subsumption.

(* ================================================================= *)
(** ** WHP While Rules                                                *)
(* ================================================================= *)

(** The unified WHP while rule instantiates to both
    Hoare and Lisbon while rules via □ and ◇. *)

Section WHPWhile.

Context {Sigma : Type}.

(** WHP while characterization: [whp[while b C]{F}(P)] holds iff [F]
    is satisfied by the set of states reachable from [P] through
    iterated guarded bodies that exit with [¬b]. *)

(** Helper: sp of while_den equals the exit-state characterization. *)
Lemma sp_while_den_eq (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (P : Sigma -> Prop) :
  sp (while_den b body) P =
  (fun rho =>
    exists sigma, P sigma /\
      star (while_body_den b body) sigma rho /\ ~ b rho).
Proof.
  apply ensemble_ext. intro tau.
  unfold sp, collect, pset_bind,
         while_den, assume_den. split.
  - intros [sigma [HP [rho [Hstar [Heq Hnb]]]]].
    subst. exists sigma. auto.
  - intros [sigma [HP [Hstar Hnb]]].
    exists sigma. split; [exact HP|].
    exists tau. split; [exact Hstar|]. split; [reflexivity | exact Hnb].
Qed.

Lemma whp_while_characterization (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma) (F : hyperquantity)
    (P : Sigma -> Prop) :
  whp (while_den b body) F P <->
  F (fun rho =>
    exists sigma, P sigma /\
      star (while_body_den b body) sigma rho /\ ~ b rho).
Proof.
  unfold whp. rewrite sp_while_den_eq. reflexivity.
Qed.

(** □-instance: Hoare while = invariant rule.
    [whp[while b C]{□Q}(P)] means all reachable exit states satisfy Q. *)
Corollary whp_box_while_iff_wlp (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  whp (while_den b body) (box Q) (pset_ret sigma) <->
  wlp (while_den b body) Q sigma.
Proof.
  exact (iff_sym (wlp_iff_box_whp (while_den b body) Q sigma)).
Qed.

(** ◇-instance: Lisbon while = variant/reachability rule.
    [whp[while b C]{◇Q}(P)] means some reachable exit state satisfies Q. *)
Corollary whp_diamond_while_iff_wp (b : Sigma -> Prop)
    (body : Sigma -> PSet Sigma)
    (Q : Sigma -> Prop) (sigma : Sigma) :
  whp (while_den b body) (diamond Q) (pset_ret sigma) <->
  wp (while_den b body) Q sigma.
Proof.
  exact (iff_sym (wp_iff_diamond_whp (while_den b body) Q sigma)).
Qed.

End WHPWhile.
