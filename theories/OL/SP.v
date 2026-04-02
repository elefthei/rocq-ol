(** * OL/SP.v — Strongest Postcondition Transformer

    Defines the forward predicate transformer SP (Strongest Post)
    from the WHP paper (arXiv:2404.05097, Zhang–Zilberstein–Kaminski–Silva).

    For the Boolean semiring (nondeterministic powerset), SP coincides
    with the collecting semantics already present as [collect] in [Lang.v].

    Main definitions:
    - [sp denote P]       — {τ | ∃σ∈P. τ ∈ denote(σ)}
    - Inductive SP rules  — sp_zero, sp_one, sp_seq, sp_plus, sp_atom

    Reference: Table 1 (middle column) of arXiv:2404.05097 *)

From Stdlib Require Import Ensembles.
From OL Require Import Monad Lang.

(* ================================================================= *)
(** ** Strongest Post Definition                                      *)
(* ================================================================= *)

(** [sp denote P] is the strongest postcondition: the set of all states
    reachable from some state in [P] under denotation [denote].
    This is exactly [collect denote P = pset_bind P denote]. *)

Definition sp {Sigma : Type}
    (denote : Sigma -> PSet Sigma) (P : PSet Sigma) : PSet Sigma :=
  collect denote P.

(* ================================================================= *)
(** ** SP Characterization                                            *)
(* ================================================================= *)

Section SPRules.

Context {Atom Sigma : Type}.
Variable atom_den : Atom -> Sigma -> PSet Sigma.

Let den := ol_denote atom_den.

(** Forward/backward characterization of SP membership. *)
Lemma sp_characterization (C : ol_prog Atom) (P : PSet Sigma) (tau : Sigma) :
  In _ (sp (den C) P) tau <->
  exists sigma, In _ P sigma /\ In _ (den C sigma) tau.
Proof.
  unfold sp, collect, pset_bind. split.
  - intros [sigma [HP Htau]]. exists sigma. auto.
  - intros [sigma [HP Htau]]. exists sigma. auto.
Qed.

(* ================================================================= *)
(** ** Inductive SP Rules                                             *)
(* ================================================================= *)

(** SP of abort is empty — no reachable states. *)
Lemma sp_zero (P : PSet Sigma) :
  sp (den OLZero) P = pset_empty.
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [HP Habs]]. exact Habs.
  - intro Habs. destruct Habs.
Qed.

(** SP of skip is the identity — same states reachable. *)
Lemma sp_one (P : PSet Sigma) :
  sp (den OLOne) P = P.
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [HP Hret]].
    simpl in Hret. inversion Hret. subst. exact HP.
  - intro HP.
    exists tau. split; [exact HP | constructor].
Qed.

(** SP distributes through sequential composition. *)
Lemma sp_seq (C1 C2 : ol_prog Atom) (P : PSet Sigma) :
  sp (den (OLSeq C1 C2)) P = sp (den C2) (sp (den C1) P).
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [HP Hseq]].
    simpl in Hseq. destruct Hseq as [mid [HC1 HC2]].
    exists mid. split.
    + exists sigma. auto.
    + exact HC2.
  - intros [mid [Hsp1 HC2]].
    destruct Hsp1 as [sigma [HP HC1]].
    exists sigma. split; [exact HP|].
    simpl. exists mid. auto.
Qed.

(** SP of nondeterministic choice is the union of SPs. *)
Lemma sp_plus (C1 C2 : ol_prog Atom) (P : PSet Sigma) :
  sp (den (OLPlus C1 C2)) P = pset_union (sp (den C1) P) (sp (den C2) P).
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [HP Hplus]].
    simpl in Hplus. destruct Hplus as [H1 | H2].
    + apply Union_introl. exists sigma. auto.
    + apply Union_intror. exists sigma. auto.
  - intro HU. inversion HU; subst.
    + destruct H as [sigma [HP Hden]].
      exists sigma. split; [exact HP|]. simpl. left. exact Hden.
    + destruct H as [sigma [HP Hden]].
      exists sigma. split; [exact HP|]. simpl. right. exact Hden.
Qed.

(** SP of an atomic command uses the atom denotation. *)
Lemma sp_atom (a : Atom) (P : PSet Sigma) :
  sp (den (OLAtom a)) P = sp (atom_den a) P.
Proof.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** SP Monotonicity                                                *)
(* ================================================================= *)

(** SP is monotone in the precondition. *)
Lemma sp_monotone (denote : Sigma -> PSet Sigma)
    (P Q : PSet Sigma) :
  (forall sigma, In _ P sigma -> In _ Q sigma) ->
  forall tau, In _ (sp denote P) tau -> In _ (sp denote Q) tau.
Proof.
  intros Hsub tau [sigma [HP Hden]].
  exists sigma. split; [apply Hsub; exact HP | exact Hden].
Qed.

(** SP preserves emptiness. *)
Lemma sp_empty (denote : Sigma -> PSet Sigma) :
  sp denote pset_empty = pset_empty.
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [Habs _]]. destruct Habs.
  - intro Habs. destruct Habs.
Qed.

(** SP distributes over union in the precondition. *)
Lemma sp_union (denote : Sigma -> PSet Sigma)
    (P Q : PSet Sigma) :
  sp denote (pset_union P Q) = pset_union (sp denote P) (sp denote Q).
Proof.
  apply ensemble_ext. intro tau. split.
  - intros [sigma [HPQ Hden]].
    inversion HPQ; subst.
    + apply Union_introl. exists sigma. auto.
    + apply Union_intror. exists sigma. auto.
  - intro HU. inversion HU; subst;
      destruct H as [sigma [HP Hden]];
      exists sigma; split; auto.
    + left. exact HP.
    + right. exact HP.
Qed.

End SPRules.
