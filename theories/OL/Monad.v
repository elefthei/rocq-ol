(** * OL/Monad.v — Powerset Monad and Partial Commutative Monoid

    Foundation for Outcome Logic's execution model.
    Defines the powerset monad [PSet] (via Ensembles), its monadic operations
    ([pset_ret], [pset_bind], [pset_union], [pset_empty]), the [PCM] typeclass,
    and the canonical [PCM_PSet] instance proving PSet with set union forms a PCM.

    Registers [PSet] as an instance of ExtLib's [Monad], [MonadZero],
    [MonadLaws], and [MonadZeroLaws] typeclasses so that standard
    monadic notation ([>>=], [x <- c1 ;; c2]) and generic lemmas
    ([bind_of_return], etc.) are available.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 3.1 *)

From Stdlib Require Import Ensembles.
From ExtLib Require Import
  Structures.Monad
  Structures.MonadZero
  Structures.MonadLaws.

(* ================================================================= *)
(** ** PSet: The Powerset Type                                        *)
(* ================================================================= *)

Definition PSet (A : Type) := Ensemble A.

(* ================================================================= *)
(** ** Monadic Operations                                             *)
(* ================================================================= *)

(** Monadic return: singleton set [{x}] *)
Definition pset_ret {A : Type} (x : A) : PSet A :=
  Singleton _ x.

(** Monadic bind: relational composition / Kleisli extension *)
Definition pset_bind {A B : Type} (m : PSet A) (k : A -> PSet B) : PSet B :=
  fun b => exists a, In _ m a /\ In _ (k a) b.

(** Empty set: identity for [pset_union] *)
Definition pset_empty {A : Type} : PSet A :=
  Empty_set _.

(** Set union: the PCM operation for the powerset monad *)
Definition pset_union {A : Type} (s1 s2 : PSet A) : PSet A :=
  Union _ s1 s2.

(* ================================================================= *)
(** ** Ensemble Extensionality                                        *)
(* ================================================================= *)

(** Two ensembles are equal when they contain the same elements. *)
Lemma ensemble_ext {A : Type} (S1 S2 : Ensemble A) :
  (forall x, In _ S1 x <-> In _ S2 x) -> S1 = S2.
Proof.
  intro H.
  apply Extensionality_Ensembles.
  split; intros x Hx.
  - exact (proj1 (H x) Hx).
  - exact (proj2 (H x) Hx).
Qed.

(* ================================================================= *)
(** ** Monad Laws                                                     *)
(* ================================================================= *)

Lemma pset_bind_ret_l {A B : Type} (a : A) (f : A -> PSet B) :
  pset_bind (pset_ret a) f = f a.
Proof.
  unfold pset_bind, pset_ret.
  apply ensemble_ext; intro b; split.
  - intros [a' [Hin Hk]].
    inversion Hin; subst. exact Hk.
  - intro Hb.
    exists a. split; [constructor | exact Hb].
Qed.

Lemma pset_bind_ret_r {A : Type} (m : PSet A) :
  pset_bind m pset_ret = m.
Proof.
  unfold pset_bind, pset_ret.
  apply ensemble_ext; intro a; split.
  - intros [a' [Hm Hs]].
    inversion Hs; subst. exact Hm.
  - intro Hm.
    exists a. split; [exact Hm | constructor].
Qed.

Lemma pset_bind_assoc {A B C : Type}
    (m : PSet A) (f : A -> PSet B) (g : B -> PSet C) :
  pset_bind (pset_bind m f) g = pset_bind m (fun a => pset_bind (f a) g).
Proof.
  unfold pset_bind.
  apply ensemble_ext; intro c; split.
  - intros [b [[a [Hm Hfa]] Hgb]].
    exists a. split; [exact Hm |].
    exists b. split; [exact Hfa | exact Hgb].
  - intros [a [Hm [b [Hfa Hgb]]]].
    exists b. split; [| exact Hgb].
    exists a. split; [exact Hm | exact Hfa].
Qed.

(** Monotonicity of [pset_bind] in the set argument. *)
Lemma pset_bind_monotone {A B : Type} (S1 S2 : PSet A) (f : A -> PSet B) :
  (forall a, In _ S1 a -> In _ S2 a) ->
  forall b, In _ (pset_bind S1 f) b -> In _ (pset_bind S2 f) b.
Proof.
  intros Hsub b Hb.
  unfold pset_bind, In in *.
  destruct Hb as [a [Ha Hfa]].
  exists a. split; [apply Hsub; exact Ha | exact Hfa].
Qed.

(** Congruence of [pset_bind] in the continuation. *)
Lemma pset_bind_cong {A B : Type} (S : PSet A) (f g : A -> PSet B) :
  (forall a, f a = g a) ->
  pset_bind S f = pset_bind S g.
Proof.
  intro Heq.
  apply ensemble_ext. intro b.
  unfold pset_bind, In.
  split; intros [a [Ha Hb]]; exists a; split; auto; rewrite Heq in *; exact Hb.
Qed.

(* ================================================================= *)
(** ** Distributivity Laws                                            *)
(* ================================================================= *)

Lemma pset_bind_union {A B : Type} (m1 m2 : PSet A) (f : A -> PSet B) :
  pset_bind (pset_union m1 m2) f =
    pset_union (pset_bind m1 f) (pset_bind m2 f).
Proof.
  unfold pset_bind, pset_union.
  apply ensemble_ext; intro b; split.
  - intros [a [Hunion Hfa]].
    inversion Hunion; subst.
    + apply Union_introl. exists a. split; assumption.
    + apply Union_intror. exists a. split; assumption.
  - intros Hunion. inversion Hunion; subst;
      destruct H as [a [Hm Hfa]]; exists a; split; auto.
    + apply Union_introl. exact Hm.
    + apply Union_intror. exact Hm.
Qed.

Lemma pset_bind_empty {A B : Type} (f : A -> PSet B) :
  pset_bind pset_empty f = pset_empty.
Proof.
  unfold pset_bind, pset_empty.
  apply ensemble_ext; intro b; split.
  - intros [a [Hempty _]]. inversion Hempty.
  - intro Hempty. inversion Hempty.
Qed.

(* ================================================================= *)
(** ** Partial Commutative Monoid                                     *)
(* ================================================================= *)

Class PCM (A : Type) := {
  pcm_op : A -> A -> A;
  pcm_unit : A;
  pcm_comm : forall x y, pcm_op x y = pcm_op y x;
  pcm_assoc : forall x y z,
    pcm_op (pcm_op x y) z = pcm_op x (pcm_op y z);
  pcm_unit_l : forall x, pcm_op pcm_unit x = x;
}.

(** Derived: right identity *)
Lemma pcm_unit_r {A : Type} `{PCM A} (x : A) :
  pcm_op x pcm_unit = x.
Proof.
  rewrite pcm_comm. apply pcm_unit_l.
Qed.

(* ================================================================= *)
(** ** PCM Instance for PSet (Set Union / Empty Set)                  *)
(* ================================================================= *)

Lemma pset_union_comm {A : Type} (s1 s2 : PSet A) :
  pset_union s1 s2 = pset_union s2 s1.
Proof.
  unfold pset_union.
  apply ensemble_ext; intro x; split; intro H; inversion H; subst.
  - apply Union_intror. exact H0.
  - apply Union_introl. exact H0.
  - apply Union_intror. exact H0.
  - apply Union_introl. exact H0.
Qed.

Lemma pset_union_assoc {A : Type} (s1 s2 s3 : PSet A) :
  pset_union (pset_union s1 s2) s3 =
    pset_union s1 (pset_union s2 s3).
Proof.
  unfold pset_union.
  apply ensemble_ext; intro x; split; intro H.
  - inversion H; subst.
    + inversion H0; subst.
      * apply Union_introl. exact H1.
      * apply Union_intror. apply Union_introl. exact H1.
    + apply Union_intror. apply Union_intror. exact H0.
  - inversion H; subst.
    + apply Union_introl. apply Union_introl. exact H0.
    + inversion H0; subst.
      * apply Union_introl. apply Union_intror. exact H1.
      * apply Union_intror. exact H1.
Qed.

Lemma pset_union_empty_l {A : Type} (s : PSet A) :
  pset_union pset_empty s = s.
Proof.
  unfold pset_union, pset_empty.
  apply ensemble_ext; intro x; split; intro H.
  - inversion H; subst.
    + inversion H0.
    + exact H0.
  - apply Union_intror. exact H.
Qed.

Lemma pset_union_empty_r {A : Type} (s : PSet A) :
  pset_union s pset_empty = s.
Proof.
  rewrite pset_union_comm. apply pset_union_empty_l.
Qed.

#[export] Instance PCM_PSet {A : Type} : PCM (PSet A) := {
  pcm_op := pset_union;
  pcm_unit := pset_empty;
  pcm_comm := pset_union_comm;
  pcm_assoc := pset_union_assoc;
  pcm_unit_l := pset_union_empty_l;
}.

(* ================================================================= *)
(** ** ExtLib Monad Instances for PSet                                *)
(* ================================================================= *)

(** PSet is a monad: [ret] = singleton, [bind] = relational composition. *)
#[export] Instance Monad_PSet : Monad PSet := {
  ret := @pset_ret;
  bind := @pset_bind;
}.

(** PSet has a zero: the empty set. *)
#[export] Instance MonadZero_PSet : MonadZero PSet := {
  mzero := @pset_empty;
}.

(** PSet satisfies the monad laws. *)
#[export] Instance MonadLaws_PSet : MonadLaws Monad_PSet := {
  bind_of_return := @pset_bind_ret_l;
  return_of_bind := @pset_bind_ret_r;
  bind_associativity := @pset_bind_assoc;
}.

(** PSet satisfies the zero law: [bind mzero f = mzero]. *)
#[export] Instance MonadZeroLaws_PSet : MonadZeroLaws Monad_PSet MonadZero_PSet := {
  bind_zero := @pset_bind_empty;
}.
