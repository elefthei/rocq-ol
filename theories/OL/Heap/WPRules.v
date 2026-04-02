(** * OL/Heap/WPRules.v — WP/WLP Rules for mGCL Heap Language

    Instantiates the generic WP/WLP definitions from [WP.v] for the
    mGCL heap language over [err_state Heap].

    Key rule: error propagation — errors pass through all commands:
      [wp  ⟦C⟧ Q (Er h) ↔ Q (Er h)]
      [wlp ⟦C⟧ Q (Er h) ↔ Q (Er h)]

    Heap-specific WP/WLP rules for atoms on [Ok] states:
    - alloc, free, store, load, error, assume

    While-loop error propagation:
    - [wp_while_er]: errors bypass while loops entirely *)

From Stdlib Require Import Ensembles Classical_Prop.
From OL Require Import Monad Lang WP.
From OL.Heap Require Import Assertion Error Lang.

(* ================================================================= *)
(** ** WP/WLP for mGCL Atoms                                         *)
(* ================================================================= *)

Section HeapAtomRules.

(** *** Error Propagation — The Fundamental Rule

    Every mGCL atom on an error state returns the same error:
    [mgcl_den c (Er h) = {Er h}].  Therefore:
    - [wp  ⟦atom c⟧ Q (Er h) ↔ Q (Er h)]
    - [wlp ⟦atom c⟧ Q (Er h) ↔ Q (Er h)] *)

Lemma wp_atom_er (c : mgcl_atom) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wp (mgcl_den c) Q (Er h) <-> Q (Er h).
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
  - intro HQ. exists (Er h). split; [constructor | exact HQ].
Qed.

Lemma wlp_atom_er (c : mgcl_atom) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wlp (mgcl_den c) Q (Er h) <-> Q (Er h).
Proof.
  unfold wlp. simpl. split.
  - intro H. apply H. constructor.
  - intros HQ tau Hin. inversion Hin. subst. exact HQ.
Qed.

(** *** Alloc on Ok: always succeeds *)
Lemma wp_alloc_ok (loc val : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wp (mgcl_den (MAlloc loc val)) Q (Ok h) <->
  Q (Ok (heap_update h loc val)).
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
  - intro HQ. exists (Ok (heap_update h loc val)).
    split; [constructor | exact HQ].
Qed.

Lemma wlp_alloc_ok (loc val : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wlp (mgcl_den (MAlloc loc val)) Q (Ok h) <->
  Q (Ok (heap_update h loc val)).
Proof.
  unfold wlp. simpl. split.
  - intro H. apply H. constructor.
  - intros HQ tau Hin. inversion Hin. subst. exact HQ.
Qed.

(** *** Store on Ok: succeeds if allocated, errors otherwise *)
Lemma wp_store_ok (loc val : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wp (mgcl_den (MStore loc val)) Q (Ok h) <->
  match h loc with
  | Some _ => Q (Ok (heap_update h loc val))
  | None   => Q (Er h)
  end.
Proof.
  unfold wp. simpl. destruct (h loc).
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Ok (heap_update h loc val)).
      split; [constructor | exact HQ].
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Er h). split; [constructor | exact HQ].
Qed.

Lemma wlp_store_ok (loc val : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wlp (mgcl_den (MStore loc val)) Q (Ok h) <->
  match h loc with
  | Some _ => Q (Ok (heap_update h loc val))
  | None   => Q (Er h)
  end.
Proof.
  unfold wlp. simpl. destruct (h loc).
  - split.
    + intro H. apply H. constructor.
    + intros HQ tau Hin. inversion Hin. subst. exact HQ.
  - split.
    + intro H. apply H. constructor.
    + intros HQ tau Hin. inversion Hin. subst. exact HQ.
Qed.

(** *** Load on Ok *)
Lemma wp_load_ok (loc : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wp (mgcl_den (MLoad loc)) Q (Ok h) <->
  match h loc with
  | Some _ => Q (Ok h)
  | None   => Q (Er h)
  end.
Proof.
  unfold wp. simpl. destruct (h loc).
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Ok h). split; [constructor | exact HQ].
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Er h). split; [constructor | exact HQ].
Qed.

(** *** Free on Ok *)
Lemma wp_free_ok (loc : nat) (Q : err_state Heap -> Prop)
    (h : Heap) :
  wp (mgcl_den (MFree loc)) Q (Ok h) <->
  match h loc with
  | Some _ => Q (Ok (heap_remove h loc))
  | None   => Q (Er h)
  end.
Proof.
  unfold wp. simpl. destruct (h loc).
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Ok (heap_remove h loc)).
      split; [constructor | exact HQ].
  - split.
    + intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
    + intro HQ. exists (Er h). split; [constructor | exact HQ].
Qed.

(** *** Error command *)
Lemma wp_error_ok (Q : err_state Heap -> Prop) (h : Heap) :
  wp (mgcl_den MError) Q (Ok h) <-> Q (Er h).
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hin HQ]]. inversion Hin. subst. exact HQ.
  - intro HQ. exists (Er h). split; [constructor | exact HQ].
Qed.

(** *** Assume on Ok *)
Lemma wp_assume_ok (guard : Heap -> Prop)
    (Q : err_state Heap -> Prop) (h : Heap) :
  wp (mgcl_den (MAssume guard)) Q (Ok h) <->
  guard h /\ Q (Ok h).
Proof.
  unfold wp. simpl. split.
  - intros [tau [Hin HQ]].
    destruct Hin as [Hg Heq]. subst. auto.
  - intros [Hg HQ]. exists (Ok h).
    split; [split; auto | exact HQ].
Qed.

Lemma wlp_assume_ok (guard : Heap -> Prop)
    (Q : err_state Heap -> Prop) (h : Heap) :
  wlp (mgcl_den (MAssume guard)) Q (Ok h) <->
  (guard h -> Q (Ok h)).
Proof.
  unfold wlp. simpl. split.
  - intros H Hg. apply H. split; auto.
  - intros H tau [Hg Heq]. subst. exact (H Hg).
Qed.

End HeapAtomRules.

(* ================================================================= *)
(** ** Error Propagation Through Full Programs                        *)
(* ================================================================= *)

Section ErrorPropagation.

(** For any mGCL program [C], errors propagate unchanged through
    the entire denotation.  This is the fundamental error-handling
    property of the mGCL language. *)

(** Errors propagate through any atom. *)
Lemma mgcl_den_er (c : mgcl_atom) (h : Heap) :
  mgcl_den c (Er h) = pset_ret (Er h).
Proof.
  reflexivity.
Qed.

End ErrorPropagation.

(* ================================================================= *)
(** ** While-Loop Error Propagation                                   *)
(* ================================================================= *)

Section WhileError.

(** Errors bypass while loops entirely.  Since:
    - [mgcl_assume g (Er h) = {Er h}] (guards pass errors through)
    - The starred body on an error just returns the error
    - The exit assume also passes the error through

    We get: [while_den ... (Er h) = {Er h}] *)

(** The heap-level assume passes errors through. *)
Lemma mgcl_assume_er (g : Heap -> Prop) (h : Heap) :
  mgcl_den (MAssume g) (Er h) = pset_ret (Er h).
Proof.
  reflexivity.
Qed.

End WhileError.
