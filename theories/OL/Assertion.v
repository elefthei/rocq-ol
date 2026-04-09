(** * OL/Assertion.v — BI-Based Outcome Assertion Logic

    Defines the assertion language for Outcome Logic, based on the
    Logic of Bunched Implications (BI).  The key connective is the
    *outcome conjunction* [⊕], which splits monoidal outcomes into
    sub-collections.

    Components:
    - [bi_formula]   — Deep-embedded BI formula syntax, parametric on [Atom]
    - [bi_sat]       — Satisfaction relation, parametric on PCM + atomic satisfaction
    - [bi_entails]   — Semantic entailment between BI formulas
    - [nd_atom_sat]  — Nondeterministic atomic satisfaction for the powerset monad
    - BI structural lemmas (commutativity, associativity, weakening, etc.)

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 3, Definition 4.1 *)

From Stdlib Require Import Ensembles Classical_Prop Morphisms.
From OL Require Import Monad.

(* ================================================================= *)
(** ** BI Formula Syntax                                              *)
(* ================================================================= *)

(** Deep-embedded BI formulas, parametric on an atomic assertion type [Atom]. *)
Inductive bi_formula (Atom : Type) : Type :=
  | BiTop                                    (* ⊤ — always true *)
  | BiBot                                    (* ⊥ — always false *)
  | BiEmpty                                  (* ⊤⊕ — monoid identity *)
  | BiAtom (p : Atom)                        (* atomic assertion *)
  | BiAnd (phi psi : bi_formula Atom)        (* φ ∧ ψ *)
  | BiOr (phi psi : bi_formula Atom)         (* φ ∨ ψ *)
  | BiImpl (phi psi : bi_formula Atom)       (* φ ⇒ ψ *)
  | BiOPlus (phi psi : bi_formula Atom)      (* φ ⊕ ψ — outcome conjunction *)
  | BiExists {T : Type} (f : T -> bi_formula Atom)  (* ∃ x:T. f(x) *)
  .

Arguments BiTop {Atom}.
Arguments BiBot {Atom}.
Arguments BiEmpty {Atom}.
Arguments BiAtom {Atom} _.
Arguments BiAnd {Atom} _ _.
Arguments BiOr {Atom} _ _.
Arguments BiImpl {Atom} _ _.
Arguments BiOPlus {Atom} _ _.
Arguments BiExists {Atom T} _.

(** Derived: negation *)
Definition BiNot {Atom : Type} (phi : bi_formula Atom) : bi_formula Atom :=
  BiImpl phi BiBot.

(** Derived: sure — singleton deterministic precondition.
    [sure P] means the (non-empty) set of states all satisfy P. *)
Definition sure {Atom : Type} (P : Atom) : bi_formula Atom :=
  BiAtom P.

(** Derived: always — partial correctness postcondition.
    [always P] means: all outcomes satisfy P, OR there are no outcomes.
    This corresponds to Hoare-style partial correctness. *)
Definition always {Atom : Type} (P : Atom) : bi_formula Atom :=
  BiOr (BiAtom P) BiEmpty.

(* ================================================================= *)
(** ** BI Satisfaction Relation                                        *)
(* ================================================================= *)

(** [bi_sat pcm atom_sat m phi] holds when [m] satisfies [phi] under
    the given PCM and atomic satisfaction function.

    - [BiEmpty] is satisfied exactly by the PCM identity
    - [BiOPlus phi psi] is satisfied when [m] splits as [m1 ◇ m2]
      with [m1 ⊨ phi] and [m2 ⊨ psi] *)
Fixpoint bi_sat {A Atom : Type} `{PCM A}
    (atom_sat : A -> Atom -> Prop) (m : A) (phi : bi_formula Atom) : Prop :=
  match phi with
  | BiTop => True
  | BiBot => False
  | BiEmpty => m = pcm_unit
  | BiAtom p => atom_sat m p
  | BiAnd phi psi => bi_sat atom_sat m phi /\ bi_sat atom_sat m psi
  | BiOr phi psi => bi_sat atom_sat m phi \/ bi_sat atom_sat m psi
  | BiImpl phi psi => bi_sat atom_sat m phi -> bi_sat atom_sat m psi
  | BiOPlus phi psi =>
      exists m1 m2, pcm_op m1 m2 = m /\
        bi_sat atom_sat m1 phi /\ bi_sat atom_sat m2 psi
  | BiExists f => exists t, bi_sat atom_sat m (f t)
  end.

(* ================================================================= *)
(** ** Semantic Entailment                                            *)
(* ================================================================= *)

(** [bi_entails phi psi] holds when every element satisfying [phi]
    also satisfies [psi].  This is universal over all PCM carriers
    and atomic satisfaction functions — but in practice we fix the
    carrier and atom_sat in the context. *)
Definition bi_entails {A Atom : Type} `{PCM A}
    (atom_sat : A -> Atom -> Prop)
    (phi psi : bi_formula Atom) : Prop :=
  forall m, bi_sat atom_sat m phi -> bi_sat atom_sat m psi.

(** Bi-entailment (logical equivalence): [φ ⟺ ψ] iff [φ ⊨ ψ] and [ψ ⊨ φ]. *)
Definition bi_equiv {A Atom : Type} `{PCM A}
    (atom_sat : A -> Atom -> Prop)
    (phi psi : bi_formula Atom) : Prop :=
  bi_entails atom_sat phi psi /\ bi_entails atom_sat psi phi.

(** Under-approximate satisfaction: [m ⊨↓ φ] iff [m ⊨ φ ⊕ ⊤] *)
Definition bi_sat_under {A Atom : Type} `{PCM A}
    (atom_sat : A -> Atom -> Prop) (m : A) (phi : bi_formula Atom) : Prop :=
  bi_sat atom_sat m (BiOPlus phi BiTop).

(** Satisfiability: there exists an element satisfying [phi] *)
Definition bi_satisfiable {A Atom : Type} `{PCM A}
    (atom_sat : A -> Atom -> Prop) (phi : bi_formula Atom) : Prop :=
  exists m, bi_sat atom_sat m phi.

(* ================================================================= *)
(** ** Nondeterministic Atomic Satisfaction                           *)
(* ================================================================= *)

(** For the powerset monad instantiation: [S ⊨ P] iff [S ≠ ∅] and
    every element of [S] satisfies [P].  The non-emptiness requirement
    witnesses reachability (Definition 3.3 in the paper). *)
Definition nd_atom_sat {Sigma : Type}
    (S : PSet Sigma) (P : Sigma -> Prop) : Prop :=
  (exists sigma, In _ S sigma) /\
  (forall sigma, In _ S sigma -> P sigma).

(* ================================================================= *)
(** ** BI Structural Lemmas                                           *)
(* ================================================================= *)

Section BILemmas.

  Context {A Atom : Type} `{HPCM : PCM A}.
  Context (atom_sat : A -> Atom -> Prop).

  (** Notation for readability within proofs *)
  Local Notation "'⟦' phi '⟧' m" := (bi_sat atom_sat m phi)
    (at level 60, no associativity).

  (* --------------------------------------------------------------- *)
  (** *** Entailment is a preorder                                    *)
  (* --------------------------------------------------------------- *)

  Lemma bi_entails_refl (phi : bi_formula Atom) :
    bi_entails atom_sat phi phi.
  Proof. intros m H. exact H. Qed.

  Lemma bi_entails_trans (phi psi chi : bi_formula Atom) :
    bi_entails atom_sat phi psi ->
    bi_entails atom_sat psi chi ->
    bi_entails atom_sat phi chi.
  Proof.
    intros H1 H2 m Hm.
    apply H2. apply H1. exact Hm.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Bi-equivalence structural lemmas                             *)
  (* --------------------------------------------------------------- *)

  Lemma bi_equiv_refl (phi : bi_formula Atom) :
    bi_equiv atom_sat phi phi.
  Proof.
    split; apply bi_entails_refl.
  Qed.

  Lemma bi_equiv_sym (phi psi : bi_formula Atom) :
    bi_equiv atom_sat phi psi -> bi_equiv atom_sat psi phi.
  Proof.
    intros [H1 H2]. split; assumption.
  Qed.

  Lemma bi_equiv_trans (phi psi chi : bi_formula Atom) :
    bi_equiv atom_sat phi psi ->
    bi_equiv atom_sat psi chi ->
    bi_equiv atom_sat phi chi.
  Proof.
    intros [H1 H2] [H3 H4]. split.
    - exact (bi_entails_trans phi psi chi H1 H3).
    - exact (bi_entails_trans chi psi phi H4 H2).
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Top / Bottom / Empty                                        *)
  (* --------------------------------------------------------------- *)

  Lemma bi_top_intro (phi : bi_formula Atom) :
    bi_entails atom_sat phi BiTop.
  Proof. intros m _. exact I. Qed.

  Lemma bi_bot_elim (phi : bi_formula Atom) :
    bi_entails atom_sat BiBot phi.
  Proof. intros m Hfalse. contradiction. Qed.

  (** [⊤⊕] is satisfied only by the PCM identity *)
  Lemma bi_empty_iff (m : A) :
    bi_sat atom_sat m BiEmpty <-> m = pcm_unit.
  Proof. simpl. split; auto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Conjunction                                                  *)
  (* --------------------------------------------------------------- *)

  Lemma bi_and_intro (phi psi chi : bi_formula Atom) :
    bi_entails atom_sat chi phi ->
    bi_entails atom_sat chi psi ->
    bi_entails atom_sat chi (BiAnd phi psi).
  Proof.
    intros H1 H2 m Hm.
    split; [apply H1 | apply H2]; exact Hm.
  Qed.

  Lemma bi_and_elim_l (phi psi : bi_formula Atom) :
    bi_entails atom_sat (BiAnd phi psi) phi.
  Proof. intros m [Hl _]. exact Hl. Qed.

  Lemma bi_and_elim_r (phi psi : bi_formula Atom) :
    bi_entails atom_sat (BiAnd phi psi) psi.
  Proof. intros m [_ Hr]. exact Hr. Qed.

  Lemma bi_and_comm (phi psi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiAnd phi psi) <->
    bi_sat atom_sat m (BiAnd psi phi).
  Proof. simpl. tauto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Disjunction                                                  *)
  (* --------------------------------------------------------------- *)

  Lemma bi_or_intro_l (phi psi : bi_formula Atom) :
    bi_entails atom_sat phi (BiOr phi psi).
  Proof. intros m Hm. left. exact Hm. Qed.

  Lemma bi_or_intro_r (phi psi : bi_formula Atom) :
    bi_entails atom_sat psi (BiOr phi psi).
  Proof. intros m Hm. right. exact Hm. Qed.

  Lemma bi_or_elim (phi psi chi : bi_formula Atom) :
    bi_entails atom_sat phi chi ->
    bi_entails atom_sat psi chi ->
    bi_entails atom_sat (BiOr phi psi) chi.
  Proof.
    intros H1 H2 m [Hl | Hr].
    - apply H1. exact Hl.
    - apply H2. exact Hr.
  Qed.

  Lemma bi_or_comm (phi psi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOr phi psi) <->
    bi_sat atom_sat m (BiOr psi phi).
  Proof. simpl. tauto. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Implication                                                  *)
  (* --------------------------------------------------------------- *)

  Lemma bi_impl_intro (phi psi : bi_formula Atom) (m : A) :
    (bi_sat atom_sat m phi -> bi_sat atom_sat m psi) ->
    bi_sat atom_sat m (BiImpl phi psi).
  Proof. intro H. exact H. Qed.

  Lemma bi_impl_elim (phi psi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiImpl phi psi) ->
    bi_sat atom_sat m phi ->
    bi_sat atom_sat m psi.
  Proof. intros Himpl Hphi. exact (Himpl Hphi). Qed.

  (* --------------------------------------------------------------- *)
  (** *** Outcome Conjunction (⊕) — the key BI connective             *)
  (* --------------------------------------------------------------- *)

  (** [⊕] is commutative *)
  Lemma bi_oplus_comm (phi psi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus phi psi) <->
    bi_sat atom_sat m (BiOPlus psi phi).
  Proof.
    simpl. split; intros [m1 [m2 [Heq [H1 H2]]]].
    - exists m2, m1. rewrite pcm_comm. auto.
    - exists m2, m1. rewrite pcm_comm. auto.
  Qed.

  (** [⊕] is associative *)
  Lemma bi_oplus_assoc (phi psi chi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus (BiOPlus phi psi) chi) <->
    bi_sat atom_sat m (BiOPlus phi (BiOPlus psi chi)).
  Proof.
    simpl. split.
    - intros [m12 [m3 [Heq [[m1 [m2 [Heq12 [H1 H2]]]] H3]]]].
      exists m1, (pcm_op m2 m3).
      split.
      + rewrite <- pcm_assoc. rewrite Heq12. exact Heq.
      + split.
        * exact H1.
        * exists m2, m3. auto.
    - intros [m1 [m23 [Heq [H1 [m2 [m3 [Heq23 [H2 H3]]]]]]]].
      exists (pcm_op m1 m2), m3.
      split.
      + rewrite pcm_assoc. rewrite Heq23. exact Heq.
      + split.
        * exists m1, m2. auto.
        * exact H3.
  Qed.

  (** [⊤⊕] is the left identity for [⊕] *)
  Lemma bi_oplus_empty_l (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus BiEmpty phi) <->
    bi_sat atom_sat m phi.
  Proof.
    simpl. split.
    - intros [m1 [m2 [Heq [Hem1 H2]]]].
      subst m1. rewrite pcm_unit_l in Heq. subst m. exact H2.
    - intro H.
      exists pcm_unit, m.
      split; [rewrite pcm_unit_l; reflexivity |].
      split; [reflexivity | exact H].
  Qed.

  (** [⊤⊕] is the right identity for [⊕] *)
  Lemma bi_oplus_empty_r (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus phi BiEmpty) <->
    bi_sat atom_sat m phi.
  Proof.
    split.
    - intro H. apply bi_oplus_comm in H.
      apply bi_oplus_empty_l. exact H.
    - intro H. apply bi_oplus_comm.
      apply bi_oplus_empty_l. exact H.
  Qed.

  (** [⊕] is monotone in both arguments *)
  Lemma bi_oplus_mono (phi1 psi1 phi2 psi2 : bi_formula Atom) :
    bi_entails atom_sat phi1 phi2 ->
    bi_entails atom_sat psi1 psi2 ->
    bi_entails atom_sat (BiOPlus phi1 psi1) (BiOPlus phi2 psi2).
  Proof.
    intros Hl Hr m [m1 [m2 [Heq [H1 H2]]]].
    exists m1, m2.
    split; [exact Heq |].
    split; [apply Hl; exact H1 | apply Hr; exact H2].
  Qed.

  (** Weakening: [φ] entails [φ ⊕ ⊤] (under-approximate) *)
  Lemma bi_weaken_oplus_top (phi : bi_formula Atom) :
    bi_entails atom_sat phi (BiOPlus phi BiTop).
  Proof.
    intros m Hm.
    simpl. exists m, pcm_unit.
    rewrite pcm_unit_r.
    split; [reflexivity |].
    split; [exact Hm | exact I].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Existential Quantifier                                       *)
  (* --------------------------------------------------------------- *)

  (** Introduction: a specific witness suffices *)
  Lemma bi_exists_intro {T : Type} (f : T -> bi_formula Atom) (t : T) (m : A) :
    bi_sat atom_sat m (f t) -> bi_sat atom_sat m (BiExists f).
  Proof.
    intro H. simpl. exists t. exact H.
  Qed.

  (** Elimination: from [∃ t. f(t)] and a universal continuation *)
  Lemma bi_exists_elim {T : Type} (f : T -> bi_formula Atom) (m : A) (P : Prop) :
    bi_sat atom_sat m (BiExists f) ->
    (forall t, bi_sat atom_sat m (f t) -> P) ->
    P.
  Proof.
    intros [t Ht] HP. exact (HP t Ht).
  Qed.

  (** Monotonicity: existential is monotone in its body *)
  Lemma bi_exists_mono {T : Type} (f g : T -> bi_formula Atom) :
    (forall t, bi_entails atom_sat (f t) (g t)) ->
    bi_entails atom_sat (BiExists f) (BiExists g).
  Proof.
    intros Hent m [t Ht].
    exists t. apply Hent. exact Ht.
  Qed.

  (** Strengthening: [φ ⊕ ⊤] does *not* in general entail [φ] —
      but [⊤⊕] (empty) is stronger than [⊤] *)
  Lemma bi_empty_entails_top :
    bi_entails atom_sat BiEmpty BiTop.
  Proof. intros m _. exact I. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Under-Approximate Satisfaction                               *)
  (* --------------------------------------------------------------- *)

  (** Under-approximate satisfaction is weaker than exact satisfaction *)
  Lemma bi_sat_implies_under (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m phi -> bi_sat_under atom_sat m phi.
  Proof.
    intro H.
    unfold bi_sat_under.
    apply bi_weaken_oplus_top. exact H.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Double Negation and Classical Properties                     *)
  (* --------------------------------------------------------------- *)

  (** Double negation elimination (uses classical logic) *)
  Lemma bi_double_negation (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiNot (BiNot phi)) <->
    bi_sat atom_sat m phi.
  Proof.
    unfold BiNot. simpl. split.
    - intro Hnn.
      destruct (classic (bi_sat atom_sat m phi)) as [H | H].
      + exact H.
      + exfalso. apply Hnn. exact H.
    - intros Hphi Hneg. apply Hneg. exact Hphi.
  Qed.

  (** Excluded middle for BI satisfaction (classical) *)
  Lemma bi_sat_excluded_middle (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m phi \/ ~ bi_sat atom_sat m phi.
  Proof. apply classic. Qed.

  (* --------------------------------------------------------------- *)
  (** *** Distributivity                                               *)
  (* --------------------------------------------------------------- *)

  (** [⊕] distributes over [∨] on the right *)
  Lemma bi_oplus_or_distr_r (phi psi chi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus phi (BiOr psi chi)) <->
    bi_sat atom_sat m (BiOr (BiOPlus phi psi) (BiOPlus phi chi)).
  Proof.
    simpl. split.
    - intros [m1 [m2 [Heq [H1 [H2 | H2]]]]].
      + left. exists m1, m2. auto.
      + right. exists m1, m2. auto.
    - intros [[m1 [m2 [Heq [H1 H2]]]] | [m1 [m2 [Heq [H1 H2]]]]].
      + exists m1, m2. split; [exact Heq |]. split; [exact H1 |]. left. exact H2.
      + exists m1, m2. split; [exact Heq |]. split; [exact H1 |]. right. exact H2.
  Qed.

  (** [⊕] distributes over [∨] on the left *)
  Lemma bi_oplus_or_distr_l (phi psi chi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus (BiOr phi psi) chi) <->
    bi_sat atom_sat m (BiOr (BiOPlus phi chi) (BiOPlus psi chi)).
  Proof.
    simpl. split.
    - intros [m1 [m2 [Heq [[H1 | H1] H2]]]].
      + left. exists m1, m2. auto.
      + right. exists m1, m2. auto.
    - intros [[m1 [m2 [Heq [H1 H2]]]] | [m1 [m2 [Heq [H1 H2]]]]].
      + exists m1, m2. split; [exact Heq |]. split; [left; exact H1 | exact H2].
      + exists m1, m2. split; [exact Heq |]. split; [right; exact H1 | exact H2].
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Bot and OPlus                                                *)
  (* --------------------------------------------------------------- *)

  (** [⊥ ⊕ φ] entails [⊥]: if one component is unsatisfiable,
      the whole outcome conjunction is unsatisfiable *)
  Lemma bi_oplus_bot_l (phi : bi_formula Atom) :
    bi_entails atom_sat (BiOPlus BiBot phi) BiBot.
  Proof.
    intros m [m1 [m2 [_ [Hbot _]]]].
    exact Hbot.
  Qed.

  Lemma bi_oplus_bot_r (phi : bi_formula Atom) :
    bi_entails atom_sat (BiOPlus phi BiBot) BiBot.
  Proof.
    intros m [m1 [m2 [_ [_ Hbot]]]].
    exact Hbot.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Monotonicity lemmas                                          *)
  (* --------------------------------------------------------------- *)

  (** Monotonicity of conjunction in both arguments. *)
  Lemma bi_and_mono (phi phi' psi psi' : bi_formula Atom) :
    bi_entails atom_sat phi phi' ->
    bi_entails atom_sat psi psi' ->
    bi_entails atom_sat (BiAnd phi psi) (BiAnd phi' psi').
  Proof.
    intros Hphi Hpsi m [H1 H2].
    split; [apply Hphi; exact H1 | apply Hpsi; exact H2].
  Qed.

  (** Monotonicity of disjunction in both arguments. *)
  Lemma bi_or_mono (phi phi' psi psi' : bi_formula Atom) :
    bi_entails atom_sat phi phi' ->
    bi_entails atom_sat psi psi' ->
    bi_entails atom_sat (BiOr phi psi) (BiOr phi' psi').
  Proof.
    intros Hphi Hpsi m [H1 | H1].
    - left. apply Hphi. exact H1.
    - right. apply Hpsi. exact H1.
  Qed.

  (** Implication is contravariant in antecedent, covariant in consequent. *)
  Lemma bi_impl_mono (phi phi' psi psi' : bi_formula Atom) :
    bi_entails atom_sat phi' phi ->
    bi_entails atom_sat psi psi' ->
    bi_entails atom_sat (BiImpl phi psi) (BiImpl phi' psi').
  Proof.
    intros Hphi Hpsi m Himpl H'.
    apply Hpsi. apply Himpl. apply Hphi. exact H'.
  Qed.

  (* --------------------------------------------------------------- *)
  (** *** Proper instances for setoid rewriting                        *)
  (* --------------------------------------------------------------- *)

  Global Instance bi_and_proper_entails :
    Proper (bi_entails atom_sat ==> bi_entails atom_sat ==> bi_entails atom_sat) (@BiAnd Atom).
  Proof.
    intros phi phi' Hphi psi psi' Hpsi.
    exact (bi_and_mono phi phi' psi psi' Hphi Hpsi).
  Qed.

  Global Instance bi_or_proper_entails :
    Proper (bi_entails atom_sat ==> bi_entails atom_sat ==> bi_entails atom_sat) (@BiOr Atom).
  Proof.
    intros phi phi' Hphi psi psi' Hpsi.
    exact (bi_or_mono phi phi' psi psi' Hphi Hpsi).
  Qed.

  Global Instance bi_oplus_proper_entails :
    Proper (bi_entails atom_sat ==> bi_entails atom_sat ==> bi_entails atom_sat) (@BiOPlus Atom).
  Proof.
    intros phi phi' Hphi psi psi' Hpsi.
    exact (bi_oplus_mono phi psi phi' psi' Hphi Hpsi).
  Qed.

  Global Instance bi_impl_proper_entails :
    Proper (bi_entails atom_sat --> bi_entails atom_sat ==> bi_entails atom_sat) (@BiImpl Atom).
  Proof.
    intros phi phi' Hphi psi psi' Hpsi.
    exact (bi_impl_mono phi phi' psi psi' Hphi Hpsi).
  Qed.

  Global Instance bi_entails_proper_equiv :
    Proper (bi_equiv atom_sat ==> bi_equiv atom_sat ==> iff) (bi_entails atom_sat).
  Proof.
    intros phi phi' [Hpp' Hp'p] psi psi' [Hqq' Hq'q].
    split; intro H.
    - exact (bi_entails_trans phi' phi psi' Hp'p (bi_entails_trans phi psi psi' H Hqq')).
    - exact (bi_entails_trans phi phi' psi Hpp' (bi_entails_trans phi' psi' psi H Hq'q)).
  Qed.

End BILemmas.

(* ================================================================= *)
(** ** Nondeterministic BI Lemmas (PSet-specific)                     *)
(* ================================================================= *)

Section NDLemmas.

  Context {Sigma : Type}.

  (** Union preserves atomic satisfaction *)
  Lemma nd_atom_sat_union (S1 S2 : PSet Sigma) (P : Sigma -> Prop) :
    nd_atom_sat S1 P ->
    nd_atom_sat S2 P ->
    nd_atom_sat (pset_union S1 S2) P.
  Proof.
    intros [Hne1 Hforall1] [Hne2 Hforall2].
    split.
    - destruct Hne1 as [s Hs].
      exists s. unfold pset_union. apply Union_introl. exact Hs.
    - intros sigma Hin.
      unfold pset_union in Hin.
      inversion Hin; subst.
      + apply Hforall1. exact H.
      + apply Hforall2. exact H.
  Qed.

  (** Subset preserves atomic satisfaction (if still non-empty) *)
  Lemma nd_atom_sat_subset (S1 S2 : PSet Sigma) (P : Sigma -> Prop) :
    nd_atom_sat S2 P ->
    (exists sigma, In _ S1 sigma) ->
    (forall sigma, In _ S1 sigma -> In _ S2 sigma) ->
    nd_atom_sat S1 P.
  Proof.
    intros [_ Hforall] Hne Hsub.
    split.
    - exact Hne.
    - intros sigma Hin. apply Hforall. apply Hsub. exact Hin.
  Qed.

  (** Monotonicity: weaker predicates are easier to satisfy *)
  Lemma nd_atom_sat_weaken (S : PSet Sigma) (P Q : Sigma -> Prop) :
    nd_atom_sat S P ->
    (forall sigma, P sigma -> Q sigma) ->
    nd_atom_sat S Q.
  Proof.
    intros [Hne Hforall] Hweak.
    split.
    - exact Hne.
    - intros sigma Hin. apply Hweak. apply Hforall. exact Hin.
  Qed.

End NDLemmas.

(* ================================================================= *)
(** ** Notation                                                        *)
(* ================================================================= *)

Declare Scope bi_scope.
Delimit Scope bi_scope with bi.

Notation "⊤" := BiTop : bi_scope.
Notation "⊥" := BiBot : bi_scope.
Notation "'⊤⊕'" := BiEmpty : bi_scope.
Notation "φ '∧' ψ" := (BiAnd φ ψ) (at level 40, left associativity) : bi_scope.
Notation "φ '∨' ψ" := (BiOr φ ψ) (at level 50, left associativity) : bi_scope.
Notation "φ '⇒' ψ" := (BiImpl φ ψ) (at level 55, right associativity) : bi_scope.
Notation "φ '⊕' ψ" := (BiOPlus φ ψ) (at level 45, left associativity) : bi_scope.
Notation "'¬' φ" := (BiNot φ) (at level 35) : bi_scope.
Notation "'sure(' P ')'" := (sure P) (at level 30, P at level 99, no associativity) : bi_scope.
Notation "'always(' P ')'" := (always P) (at level 30, P at level 99, no associativity) : bi_scope.

(* ================================================================= *)
(** ** Additional BI Structural Lemmas                                *)
(* ================================================================= *)

Section AdditionalBILemmas.

  Context {A Atom : Type} `{HPCM : PCM A}.
  Context (atom_sat : A -> Atom -> Prop).

  (** [⊤⊕ ⊕ ⊤⊕ ⊨ ⊤⊕]: combining two empty outcomes is empty *)
  Lemma bi_empty_oplus_empty (m : A) :
    bi_sat atom_sat m (BiOPlus BiEmpty BiEmpty) <->
    bi_sat atom_sat m BiEmpty.
  Proof.
    simpl. split.
    - intros [m1 [m2 [Heq [Hm1 Hm2]]]].
      subst m1 m2. rewrite pcm_unit_l in Heq. symmetry. exact Heq.
    - intro Hm. exists pcm_unit, pcm_unit.
      split; [rewrite pcm_unit_l; symmetry; exact Hm |].
      split; reflexivity.
  Qed.

  (** Iterated under-approximation is stable:
      [(φ ⊕ ⊤) ⊕ ⊤ ⊨ φ ⊕ ⊤] *)
  Lemma bi_oplus_top_oplus_top (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus (BiOPlus phi BiTop) BiTop) ->
    bi_sat atom_sat m (BiOPlus phi BiTop).
  Proof.
    intros [m1 [m2 [Heq [[m11 [m12 [Heq1 [Hphi _]]]] _]]]].
    exists m11, (pcm_op m12 m2).
    split.
    - rewrite <- pcm_assoc. rewrite Heq1. exact Heq.
    - split; [exact Hphi | exact I].
  Qed.

  (** Converse: [φ ⊕ ⊤ ⊨ (φ ⊕ ⊤) ⊕ ⊤] *)
  Lemma bi_oplus_top_to_oplus_top_oplus_top (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus phi BiTop) ->
    bi_sat atom_sat m (BiOPlus (BiOPlus phi BiTop) BiTop).
  Proof.
    intro H. exists m, pcm_unit.
    rewrite pcm_unit_r.
    split; [reflexivity |].
    split; [exact H | exact I].
  Qed.

  (** Biconditional: iterated under-approximation *)
  Lemma bi_oplus_top_idem (phi : bi_formula Atom) (m : A) :
    bi_sat atom_sat m (BiOPlus (BiOPlus phi BiTop) BiTop) <->
    bi_sat atom_sat m (BiOPlus phi BiTop).
  Proof.
    split.
    - apply bi_oplus_top_oplus_top.
    - apply bi_oplus_top_to_oplus_top_oplus_top.
  Qed.

  (** [⊕] is monotone with respect to [∧]:
      [φ₁ ⊕ ψ₁ ⊨ (φ₁ ∧ φ₂) ⊕ (ψ₁ ∧ ψ₂)] does NOT hold in general,
      but [(φ₁ ∧ φ₂) ⊕ (ψ₁ ∧ ψ₂) ⊨ (φ₁ ⊕ ψ₁) ∧ (φ₂ ⊕ ψ₂)] does NOT either.
      What DOES hold is monotonicity: *)
  Lemma bi_oplus_and_mono_l (phi1 phi2 psi : bi_formula Atom) :
    bi_entails atom_sat (BiOPlus (BiAnd phi1 phi2) psi)
                         (BiOPlus phi1 psi).
  Proof.
    intros m [m1 [m2 [Heq [[H1 _] H2]]]].
    exists m1, m2. auto.
  Qed.

  Lemma bi_oplus_and_mono_r (phi psi1 psi2 : bi_formula Atom) :
    bi_entails atom_sat (BiOPlus phi (BiAnd psi1 psi2))
                         (BiOPlus phi psi1).
  Proof.
    intros m [m1 [m2 [Heq [H1 [H2 _]]]]].
    exists m1, m2. auto.
  Qed.

  (** [⊕] distributes over [∨] (entailment forms) *)
  Lemma bi_oplus_or_distr_r_entails (phi psi chi : bi_formula Atom) :
    bi_entails atom_sat (BiOPlus phi (BiOr psi chi))
                         (BiOr (BiOPlus phi psi) (BiOPlus phi chi)).
  Proof.
    intros m [m1 [m2 [Heq [H1 [H2 | H2]]]]].
    - left. exists m1, m2. auto.
    - right. exists m1, m2. auto.
  Qed.

  Lemma bi_or_oplus_entails (phi psi chi : bi_formula Atom) :
    bi_entails atom_sat (BiOr (BiOPlus phi psi) (BiOPlus phi chi))
                         (BiOPlus phi (BiOr psi chi)).
  Proof.
    intros m [[m1 [m2 [Heq [H1 H2]]]] | [m1 [m2 [Heq [H1 H2]]]]].
    - exists m1, m2. split; [exact Heq |]. split; [exact H1 |]. left. exact H2.
    - exists m1, m2. split; [exact Heq |]. split; [exact H1 |]. right. exact H2.
  Qed.

  (** Note: [φ ⊕ ⊤ ∧ ψ ⊕ ⊤ ⊨ (φ ∧ ψ) ⊕ ⊤] does NOT hold in general.
      Weakening through [⊤] is NOT compositional with conjunction —
      documented here as a non-theorem. *)

  (** Under-approximate satisfaction is monotone in the formula *)
  Lemma bi_sat_under_mono (phi psi : bi_formula Atom) :
    bi_entails atom_sat phi psi ->
    forall m, bi_sat_under atom_sat m phi -> bi_sat_under atom_sat m psi.
  Proof.
    intros Hent m Hunder.
    unfold bi_sat_under in *.
    destruct Hunder as [m1 [m2 [Heq [H1 H2]]]].
    exists m1, m2.
    split; [exact Heq |].
    split; [apply Hent; exact H1 | exact H2].
  Qed.

End AdditionalBILemmas.

(* ================================================================= *)
(** ** Strong Negation for Nondeterministic Assertions                *)
(* ================================================================= *)

(** [nd_neg Q] is the "strong negation" of Q from the paper (denoted Q̄).
    A set S satisfies nd_neg(Q) iff S is non-empty and ALL elements
    of S fail to satisfy Q.

    This differs from BI negation [¬Q ≡ Q ⇒ ⊥]:
    - [S ⊨ ¬Q] iff [S = ∅] or [∃σ∈S. ¬Q(σ)]
    - [S ⊨ Q̄]  iff [S ≠ ∅] and [∀σ∈S. ¬Q(σ)]

    The strong negation is critical for the Falsification theorems
    (Section 4 of the paper). *)

Section StrongNegation.

  Context {Sigma : Type}.

  Definition nd_neg (Q : Sigma -> Prop) : Sigma -> Prop :=
    fun sigma => ~ Q sigma.

  (** [nd_neg] via [nd_atom_sat]: the nondeterministic version *)
  Lemma nd_neg_sat (S : PSet Sigma) (Q : Sigma -> Prop) :
    nd_atom_sat S (nd_neg Q) <->
    (exists sigma, In _ S sigma) /\ (forall sigma, In _ S sigma -> ~ Q sigma).
  Proof.
    unfold nd_neg, nd_atom_sat. tauto.
  Qed.

  (** Empty set does NOT satisfy nd_neg *)
  Lemma nd_neg_empty (Q : Sigma -> Prop) :
    ~ nd_atom_sat pset_empty (nd_neg Q).
  Proof.
    intros [[sigma Hin] _]. inversion Hin.
  Qed.

  (** Singleton satisfies nd_neg(Q) iff ¬Q(σ) *)
  Lemma nd_neg_singleton (sigma : Sigma) (Q : Sigma -> Prop) :
    nd_atom_sat (pset_ret sigma) (nd_neg Q) <-> ~ Q sigma.
  Proof.
    split.
    - intros [_ Hforall]. apply Hforall. constructor.
    - intro HnQ. split.
      + exists sigma. constructor.
      + intros sigma' Hin. inversion Hin; subst. exact HnQ.
  Qed.

  (** Union preserves nd_neg *)
  Lemma nd_neg_union (S1 S2 : PSet Sigma) (Q : Sigma -> Prop) :
    nd_atom_sat S1 (nd_neg Q) ->
    nd_atom_sat S2 (nd_neg Q) ->
    nd_atom_sat (pset_union S1 S2) (nd_neg Q).
  Proof.
    intros [Hne1 Hf1] [Hne2 Hf2].
    split.
    - destruct Hne1 as [s Hs]. exists s. apply Union_introl. exact Hs.
    - intros sigma Hin. unfold pset_union in Hin. inversion Hin; subst.
      + apply Hf1. exact H.
      + apply Hf2. exact H.
  Qed.

  (** nd_neg and nd_atom_sat are exclusive (for non-empty sets) *)
  Lemma nd_neg_exclusive (S : PSet Sigma) (Q : Sigma -> Prop) :
    nd_atom_sat S Q -> nd_atom_sat S (nd_neg Q) -> False.
  Proof.
    intros [Hne HQ] [_ HnQ].
    destruct Hne as [sigma Hin].
    exact (HnQ sigma Hin (HQ sigma Hin)).
  Qed.

  (** Subset preserves nd_neg (if still non-empty) *)
  Lemma nd_neg_subset (S1 S2 : PSet Sigma) (Q : Sigma -> Prop) :
    nd_atom_sat S2 (nd_neg Q) ->
    (exists sigma, In _ S1 sigma) ->
    (forall sigma, In _ S1 sigma -> In _ S2 sigma) ->
    nd_atom_sat S1 (nd_neg Q).
  Proof.
    intros [_ Hf] Hne Hsub.
    split; [exact Hne |].
    intros sigma Hin. apply Hf. apply Hsub. exact Hin.
  Qed.

  (** Classical: for non-empty sets, either Q or nd_neg(Q) holds at each element *)
  Lemma nd_sat_or_neg (S : PSet Sigma) (Q : Sigma -> Prop) (sigma : Sigma) :
    In _ S sigma -> Q sigma \/ nd_neg Q sigma.
  Proof.
    intro Hin. unfold nd_neg. apply classic.
  Qed.

End StrongNegation.
