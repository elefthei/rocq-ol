(** * examples/OL/Collatz.v — Collatz Conjecture in Outcome Logic

    Demonstrates WP/WLP backward reasoning on the Collatz problem:
    f(n) = n/2 if even, 3n+1 if odd.  The conjecture (unproven!)
    says repeated application from any positive n reaches 1.

    Examples:
    1. [collatz_partial_correctness] — WLP invariant: IF it terminates, result = 1
    2. [collatz_reaches_one_from_4]  — WP variant: 4 DOES reach 1 in 2 steps
    3. [collatz_duality]             — WP ↔ ¬WLP(¬Q) duality

    Reference:
    - arXiv:2401.04594 §5.4 (Collatz as loop-rule example)
    - arXiv:2404.05097 (WP/WLP definitions) *)

From Stdlib Require Import Ensembles PeanoNat Lia.
From OL Require Import Monad Lang WP.
From OL.Rules Require Import Expression.

(* ================================================================= *)
(** ** Collatz Step and Loop                                          *)
(* ================================================================= *)

(** State = nat (the current value).
    One Collatz step: divide by 2 if even, else 3n+1. *)

Section CollatzDefinitions.

Definition collatz_step (sigma : nat) : PSet nat :=
  if Nat.even sigma then pset_ret (Nat.div sigma 2)
  else pset_ret (3 * sigma + 1).

(** Guard: value ≠ 1 (loop continues). *)
Definition collatz_guard (sigma : nat) : Prop := sigma <> 1.

(** The Collatz loop: iterate [collatz_step] while value ≠ 1. *)
Definition collatz_loop : nat -> PSet nat :=
  while_den collatz_guard collatz_step.

End CollatzDefinitions.

(* ================================================================= *)
(** ** Partial Correctness (WLP Invariant Rule)                       *)
(* ================================================================= *)

(** Using WLP invariant rule with [I = fun σ ⇒ σ > 0]:
    positivity is preserved by the Collatz step, and when
    the guard fails (σ = 1), the postcondition [σ = 1] holds.

    This proves: on ALL terminating paths, the result is 1.
    (The Collatz conjecture—whether it always terminates—is open.) *)

Section CollatzPartialCorrectness.

Lemma collatz_step_preserves_pos :
  forall sigma, sigma > 0 -> collatz_guard sigma ->
    wlp collatz_step (fun s => s > 0) sigma.
Proof.
  intros sigma Hpos Hguard.
  unfold wlp, collatz_step.
  destruct (Nat.even sigma) eqn:Heven; intros tau Hin;
    inversion Hin; subst; clear Hin.
  - (* even: sigma / 2 > 0 *)
    assert (sigma >= 2).
    { unfold collatz_guard in Hguard. lia. }
    apply Nat.div_str_pos. lia.
  - (* odd: 3 * sigma + 1 > 0 *)
    lia.
Qed.

Theorem collatz_partial_correctness :
  forall sigma, sigma > 0 ->
    wlp collatz_loop (fun n => n = 1) sigma.
Proof.
  intros sigma Hpos.
  apply (wlp_while_invariant (fun s => s > 0)
           collatz_guard collatz_step (fun n => n = 1)).
  - (* Body preserves invariant under guard *)
    exact collatz_step_preserves_pos.
  - (* I ∧ ¬guard → Q *)
    intros s Hs Hng.
    unfold collatz_guard in Hng.
    destruct (Nat.eq_dec s 1) as [Heq | Hneq].
    + exact Heq.
    + exfalso. exact (Hng Hneq).
  - (* I holds initially *)
    exact Hpos.
Qed.

End CollatzPartialCorrectness.

(* ================================================================= *)
(** ** Reachability from 4 (WP Variant Rule)                          *)
(* ================================================================= *)

(** Using WP variant rule with the Collatz trace 4 → 2 → 1:
    the variant [V n σ] tracks the sequence backwards.

    This proves: there EXISTS a path from 4 to 1 (angelic). *)

Section CollatzReachability.

(** Variant: tracks the 2-step Collatz sequence starting from 4. *)
Definition collatz_variant_4 (n : nat) (sigma : nat) : Prop :=
  match n with
  | 0 => sigma = 1
  | 1 => sigma = 2
  | 2 => sigma = 4
  | _ => False
  end.

Theorem collatz_reaches_one_from_4 :
  wp collatz_loop (fun n => n = 1) 4.
Proof.
  assert (H : forall n sigma, collatz_variant_4 n sigma ->
    wp collatz_loop (fun s => s = 1) sigma).
  { unfold collatz_loop.
    apply (wp_while_variant collatz_variant_4 collatz_guard collatz_step
             (fun s => s = 1)).
    - (* V 0 σ → ¬ guard *)
      intros s Hs. simpl in Hs. subst.
      unfold collatz_guard. intro Hc. exact (Hc eq_refl).
    - (* V (S n) σ → guard *)
      intros n s Hs. unfold collatz_guard.
      destruct n; [simpl in Hs; subst; discriminate |
        destruct n; [simpl in Hs; subst; discriminate |
          simpl in Hs; contradiction]].
    - (* V (S n) σ → wp body (V n) σ *)
      intros n s Hs.
      destruct n.
      + (* n = 0: V 1 s, so s = 2 *)
        simpl in Hs. subst.
        unfold wp, collatz_step. simpl.
        exists 1. split; [constructor | reflexivity].
      + destruct n.
        * (* n = 1: V 2 s, so s = 4 *)
          simpl in Hs. subst.
          unfold wp, collatz_step. simpl.
          exists 2. split; [constructor | reflexivity].
        * (* n ≥ 2: V (S (S (S n))) s = False *)
          simpl in Hs. contradiction.
    - (* V 0 σ → Q *)
      intros s Hs. simpl in Hs. exact Hs.
  }
  exact (H 2 4 eq_refl).
Qed.

End CollatzReachability.

(* ================================================================= *)
(** ** WP–WLP Duality                                                 *)
(* ================================================================= *)

(** [wp Q σ ↔ ¬ wlp (¬Q) σ] — the De Morgan dual. *)

Section CollatzDuality.

Lemma collatz_duality (sigma : nat) :
  wp collatz_loop (fun s => s = 1) sigma <->
  ~ wlp collatz_loop (fun s => s <> 1) sigma.
Proof.
  exact (wp_wlp_while_duality collatz_guard collatz_step
           (fun s => s = 1) sigma).
Qed.

End CollatzDuality.
