(** * examples/OL/WPExample.v — WP-Based Verification Examples

    Demonstrates WP/WLP backward reasoning including while-loop
    verification via the invariant rule (Hoare) and the variant
    rule (Lisbon/angelic).

    Examples:
    1. [countdown_wlp]   — WLP invariant rule for a countdown loop
    2. [countdown_wp]    — WP variant rule for same loop (reachability)
    3. [countdown_duality] — WP ↔ ¬WLP(¬Q) duality

    Reference:
    - arXiv:2404.05097 (WP/WLP definitions)
    - arXiv:2401.04594 (Invariant and Variant loop rules) *)

From Stdlib Require Import Ensembles PeanoNat.
From OL Require Import Monad Lang WP.
From OL.Rules Require Import Expression.

(* ================================================================= *)
(** ** Countdown Loop Example                                        *)
(* ================================================================= *)

(** A countdown loop: decrement a counter until it reaches 0.

    State = nat (the counter).
    Body = decrement: maps n to n-1.
    Guard = counter > 0.

    We verify:
    - WLP (demonic): all paths end at 0 (invariant rule)
    - WP (angelic): some path ends at 0 (variant rule) *)

Section CountdownLoop.

(** Decrement body: maps n to {n-1}. *)
Definition decrement (sigma : nat) : PSet nat :=
  match sigma with
  | O   => pset_ret O
  | S n => pset_ret n
  end.

(** Guard: counter > 0. *)
Definition counter_pos (sigma : nat) : Prop := sigma > 0.

(** The while loop: iterate decrement while counter > 0. *)
Definition countdown : nat -> PSet nat :=
  while_den counter_pos decrement.

(* ================================================================= *)
(** *** WLP Invariant Rule (Hoare / Demonic)                         *)
(* ================================================================= *)

(** Using the WLP invariant rule with [I = fun _ => True]:
    the trivial invariant is preserved by decrement, and when the
    guard is false, we know [sigma = 0].

    This proves: for ALL paths, the loop ends at 0. *)

Lemma countdown_wlp_zero : forall sigma : nat,
  wlp countdown (fun n => n = 0) sigma.
Proof.
  intro sigma.
  apply (wlp_while_invariant (fun _ => True)
           counter_pos decrement (fun n => n = 0)).
  - (* Body preserves invariant True on all paths *)
    intros s _ _. unfold wlp, decrement.
    destruct s; intros tau Hin; inversion Hin; subst; exact I.
  - (* True ∧ ¬(counter_pos s) → s = 0 *)
    intros s _ Hnb. unfold counter_pos in Hnb.
    destruct s.
    + reflexivity.
    + exfalso. apply Hnb. unfold counter_pos. apply Nat.lt_0_succ.
  - (* I sigma = True *)
    exact I.
Qed.

(* ================================================================= *)
(** *** WP Variant Rule (Lisbon / Angelic)                           *)
(* ================================================================= *)

(** Using the WP variant rule with [V n sigma ↔ sigma = n]:
    the body decreases the variant (S n ↦ n), and V 0 means
    the guard is false (sigma = 0).

    This proves: there EXISTS a path ending at 0. *)

Definition countdown_variant (n : nat) (sigma : nat) : Prop :=
  sigma = n.

Lemma countdown_wp_zero : forall n sigma : nat,
  countdown_variant n sigma ->
  wp countdown (fun s => s = 0) sigma.
Proof.
  apply (wp_while_variant
           countdown_variant
           counter_pos
           decrement
           (fun s => s = 0)).
  - (* V 0 → ¬ counter_pos *)
    intros s Hs. unfold countdown_variant in Hs. subst.
    unfold counter_pos. intro H. inversion H.
  - (* V (S n) → counter_pos *)
    intros n s Hs. unfold countdown_variant in Hs. subst.
    unfold counter_pos. apply Nat.lt_0_succ.
  - (* Body maps V (S n) to V n on some path *)
    intros n s Hs. unfold countdown_variant in Hs. subst.
    unfold wp, decrement. exists n. split; [constructor | reflexivity].
  - (* V 0 → Q *)
    intros s Hs. unfold countdown_variant in Hs. exact Hs.
Qed.

(* ================================================================= *)
(** *** WP–WLP Duality                                               *)
(* ================================================================= *)

(** [wp Q σ ↔ ¬ wlp (¬Q) σ]  — the De Morgan dual. *)

Lemma countdown_duality (sigma : nat) :
  wp countdown (fun s => s = 0) sigma <->
  ~ wlp countdown (fun s => s <> 0) sigma.
Proof.
  exact (wp_wlp_while_duality counter_pos decrement
           (fun s => s = 0) sigma).
Qed.

End CountdownLoop.
