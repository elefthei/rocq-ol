(** * OL/Heap/Error.v — Error Monad for Outcome Logic

    Defines error-tagged states [err_state], error-tagged assertions
    [err_assert], and the parametric satisfaction relation [err_atom_sat].

    The error monad wraps an arbitrary state type [Sigma] with an
    Ok/Er tag, distinguishing successful outcomes from error outcomes.
    This is the foundation for OL's reasoning about manifest errors
    and error propagation in heap-manipulating programs.

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 5 *)

From Stdlib Require Import Ensembles.
From OL Require Import Monad.

(* ================================================================= *)
(** ** Error-Tagged States                                            *)
(* ================================================================= *)

(** A computation may finish in an ok state or an error state.
    Both branches carry the underlying state, enabling assertions
    to inspect the heap/store even after an error. *)
Inductive err_state (Sigma : Type) : Type :=
  | Ok (sigma : Sigma)
  | Er (sigma : Sigma).

Arguments Ok {Sigma} sigma.
Arguments Er {Sigma} sigma.

(* ================================================================= *)
(** ** Error-Tagged Assertions                                        *)
(* ================================================================= *)

(** Atomic assertions for the error monad, parametric over an
    underlying assertion type [Assert].  When instantiated with
    separation-logic assertions ([sl_assert] from Heap/Assertion.v),
    [AOk p] asserts "the outcome is ok and satisfies [p]", while
    [AEr q] asserts "the outcome is an error and satisfies [q]". *)
Inductive err_assert (Assert : Type) : Type :=
  | AOk (p : Assert)
  | AEr (q : Assert).

Arguments AOk {Assert} p.
Arguments AEr {Assert} q.

(* ================================================================= *)
(** ** Satisfaction Relation                                           *)
(* ================================================================= *)

(** [err_atom_sat] lifts an underlying satisfaction relation
    [sat : Sigma -> Assert -> Prop] to error-tagged states.
    An [Ok] state satisfies an [AOk] assertion, an [Er] state
    satisfies an [AEr] assertion; mismatched tags yield [False]. *)
Definition err_atom_sat {Sigma Assert : Type}
    (sat : Sigma -> Assert -> Prop)
    (s : err_state Sigma) (a : err_assert Assert) : Prop :=
  match s, a with
  | Ok sigma, AOk p => sat sigma p
  | Er sigma, AEr q => sat sigma q
  | _, _ => False
  end.

(* ================================================================= *)
(** ** Decidability and Inversion                                     *)
(* ================================================================= *)

(** [err_is_ok] and [err_is_er] classify error-tagged states. *)
Definition err_is_ok {Sigma : Type} (s : err_state Sigma) : Prop :=
  match s with
  | Ok _ => True
  | Er _ => False
  end.

Definition err_is_er {Sigma : Type} (s : err_state Sigma) : Prop :=
  match s with
  | Ok _ => False
  | Er _ => True
  end.

(* ================================================================= *)
(** ** Projections                                                    *)
(* ================================================================= *)

(** Extract the underlying state, discarding the tag. *)
Definition err_payload {Sigma : Type} (s : err_state Sigma) : Sigma :=
  match s with
  | Ok sigma => sigma
  | Er sigma => sigma
  end.

(* ================================================================= *)
(** ** Functorial Map                                                 *)
(* ================================================================= *)

(** [err_map f s] applies [f] to the payload while preserving the tag. *)
Definition err_map {A B : Type} (f : A -> B) (s : err_state A) : err_state B :=
  match s with
  | Ok sigma => Ok (f sigma)
  | Er sigma => Er (f sigma)
  end.

(* ================================================================= *)
(** ** Set-Level Projections (PSet Integration)                       *)
(* ================================================================= *)

(** Project out the ok-outcomes from a set of error-tagged states. *)
Definition err_ok_set {Sigma : Type} (S : PSet (err_state Sigma)) : PSet Sigma :=
  fun sigma => In _ S (Ok sigma).

(** Project out the er-outcomes. *)
Definition err_er_set {Sigma : Type} (S : PSet (err_state Sigma)) : PSet Sigma :=
  fun sigma => In _ S (Er sigma).

(** Inject a set of states as ok-outcomes. *)
Definition err_ok_inject {Sigma : Type} (S : PSet Sigma) : PSet (err_state Sigma) :=
  fun s => match s with
           | Ok sigma => In _ S sigma
           | Er _ => False
           end.

(** Inject a set of states as er-outcomes. *)
Definition err_er_inject {Sigma : Type} (S : PSet Sigma) : PSet (err_state Sigma) :=
  fun s => match s with
           | Ok _ => False
           | Er sigma => In _ S sigma
           end.

(* ================================================================= *)
(** ** Basic Lemmas                                                   *)
(* ================================================================= *)

(** Injectivity of constructors. *)
Lemma ok_inj {Sigma : Type} (s1 s2 : Sigma) :
  Ok s1 = Ok s2 -> s1 = s2.
Proof.
  intro H. inversion H. reflexivity.
Qed.

Lemma er_inj {Sigma : Type} (s1 s2 : Sigma) :
  Er s1 = Er s2 -> s1 = s2.
Proof.
  intro H. inversion H. reflexivity.
Qed.

(** Constructors are disjoint. *)
Lemma ok_neq_er {Sigma : Type} (s1 s2 : Sigma) :
  Ok s1 <> Er s2.
Proof.
  intro H. discriminate H.
Qed.

(** [err_map] preserves identity. *)
Lemma err_map_id {A : Type} (s : err_state A) :
  err_map (fun x => x) s = s.
Proof.
  destruct s; reflexivity.
Qed.

(** [err_map] composes. *)
Lemma err_map_compose {A B C : Type} (f : A -> B) (g : B -> C) (s : err_state A) :
  err_map g (err_map f s) = err_map (fun x => g (f x)) s.
Proof.
  destruct s; reflexivity.
Qed.

(** [err_payload] after [err_map]. *)
Lemma err_payload_map {A B : Type} (f : A -> B) (s : err_state A) :
  err_payload (err_map f s) = f (err_payload s).
Proof.
  destruct s; reflexivity.
Qed.

(** [err_is_ok] / [err_is_er] are complementary. *)
Lemma err_is_ok_or_er {Sigma : Type} (s : err_state Sigma) :
  err_is_ok s \/ err_is_er s.
Proof.
  destruct s; [left | right]; exact I.
Qed.

Lemma err_is_ok_not_er {Sigma : Type} (s : err_state Sigma) :
  err_is_ok s -> ~ err_is_er s.
Proof.
  destruct s; simpl; auto.
Qed.

Lemma err_is_er_not_ok {Sigma : Type} (s : err_state Sigma) :
  err_is_er s -> ~ err_is_ok s.
Proof.
  destruct s; simpl; auto.
Qed.

(** Satisfaction is exclusive: a state can satisfy [AOk p] or [AEr q]
    but never both (for any fixed [p] and [q]). *)
Lemma err_atom_sat_exclusive {Sigma Assert : Type}
    (sat : Sigma -> Assert -> Prop)
    (s : err_state Sigma) (p q : Assert) :
  err_atom_sat sat s (AOk p) -> ~ err_atom_sat sat s (AEr q).
Proof.
  destruct s; simpl; auto.
Qed.

(** Satisfaction under [AOk] requires an [Ok] state. *)
Lemma err_atom_sat_ok_inv {Sigma Assert : Type}
    (sat : Sigma -> Assert -> Prop)
    (s : err_state Sigma) (p : Assert) :
  err_atom_sat sat s (AOk p) ->
  exists sigma, s = Ok sigma /\ sat sigma p.
Proof.
  destruct s; simpl.
  - intro H. exists sigma. split; [reflexivity | exact H].
  - intro H. contradiction.
Qed.

(** Satisfaction under [AEr] requires an [Er] state. *)
Lemma err_atom_sat_er_inv {Sigma Assert : Type}
    (sat : Sigma -> Assert -> Prop)
    (s : err_state Sigma) (q : Assert) :
  err_atom_sat sat s (AEr q) ->
  exists sigma, s = Er sigma /\ sat sigma q.
Proof.
  destruct s; simpl.
  - intro H. contradiction.
  - intro H. exists sigma. split; [reflexivity | exact H].
Qed.

(** [err_ok_set] / [err_er_set] round-trip with injection. *)
Lemma err_ok_set_inject {Sigma : Type} (S : PSet Sigma) :
  err_ok_set (err_ok_inject S) = S.
Proof.
  unfold err_ok_set, err_ok_inject.
  apply ensemble_ext. intro sigma. split.
  - intro H. exact H.
  - intro H. exact H.
Qed.

Lemma err_er_set_inject {Sigma : Type} (S : PSet Sigma) :
  err_er_set (err_er_inject S) = S.
Proof.
  unfold err_er_set, err_er_inject.
  apply ensemble_ext. intro sigma. split.
  - intro H. exact H.
  - intro H. exact H.
Qed.

(** Projections of injections on the wrong tag yield empty. *)
Lemma err_er_set_ok_inject {Sigma : Type} (S : PSet Sigma) :
  err_er_set (err_ok_inject S) = pset_empty.
Proof.
  unfold err_er_set, err_ok_inject, pset_empty.
  apply ensemble_ext. intro sigma. split.
  - intro H. contradiction.
  - intro H. inversion H.
Qed.

Lemma err_ok_set_er_inject {Sigma : Type} (S : PSet Sigma) :
  err_ok_set (err_er_inject S) = pset_empty.
Proof.
  unfold err_ok_set, err_er_inject, pset_empty.
  apply ensemble_ext. intro sigma. split.
  - intro H. contradiction.
  - intro H. inversion H.
Qed.

(** A set of error-tagged states is the union of its ok and er parts. *)
Lemma err_state_decompose {Sigma : Type} (S : PSet (err_state Sigma)) :
  S = pset_union (err_ok_inject (err_ok_set S))
                 (err_er_inject (err_er_set S)).
Proof.
  unfold pset_union, err_ok_inject, err_er_inject, err_ok_set, err_er_set.
  apply ensemble_ext. intro s. split.
  - intro HS. destruct s.
    + apply Union_introl. simpl. exact HS.
    + apply Union_intror. simpl. exact HS.
  - intro HU. inversion HU; subst.
    + destruct s; simpl in H; [exact H | contradiction].
    + destruct s; simpl in H; [contradiction | exact H].
Qed.
