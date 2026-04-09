(** * OL/Lang.v — OL Language Syntax, Powerset Denotation, Kleene Star

    Defines the command language from Figure 3 of the Outcome Logic paper:
    [𝟎] (abort), [𝟏] (skip), [;] (seq), [+] (choice), [C⋆] (Kleene star),
    and parametrizable atomic commands.

    The denotation [ol_denote] maps programs directly to a powerset semantics
    [Σ → PSet Σ], where the Kleene star is given by the reflexive–transitive
    closure of the one-step relation.  A collecting extension [collect] lifts
    this to [PSet Σ → PSet Σ].

    Reference: Zilberstein, Dreyer, Silva —
      "Outcome Logic" (OOPSLA 2023), Section 2 (Figure 3) *)

From Stdlib Require Import Ensembles.
From OL Require Import Monad.

(* ================================================================= *)
(** ** OL Language Syntax                                              *)
(* ================================================================= *)

(** The language is parametric over a type [Atom] of atomic commands.
    This follows Figure 3 of the paper exactly. *)

Section Syntax.

  Context {Atom : Type}.

  Inductive ol_prog : Type :=
    | OLZero                              (** 𝟎 — abort / diverge      *)
    | OLOne                               (** 𝟏 — skip                 *)
    | OLSeq  (C1 C2 : ol_prog)           (** C₁ ; C₂                  *)
    | OLPlus (C1 C2 : ol_prog)           (** C₁ + C₂ — nondeterminism *)
    | OLStar (C : ol_prog)               (** C⋆ — Kleene iteration     *)
    | OLAtom (c : Atom)                   (** atomic command            *)
    .

End Syntax.

Arguments ol_prog : clear implicits.
Arguments OLZero  {Atom}.
Arguments OLOne   {Atom}.
Arguments OLSeq   {Atom}.
Arguments OLPlus  {Atom}.
Arguments OLStar  {Atom}.
Arguments OLAtom  {Atom}.

(* ================================================================= *)
(** ** Kleene Star — Reflexive–Transitive Closure                     *)
(* ================================================================= *)

(** [star step σ τ] holds when [τ] is reachable from [σ] by zero or
    more applications of the one-step relation [step].  This is the
    least fixed point of [F(f)(σ) = f†(step(σ)) ∪ {σ}] from the paper,
    instantiated for the powerset monad where [⊔] = [∪]. *)

Section Star.

  Context {Sigma : Type}.

  Inductive star (step : Sigma -> PSet Sigma) : Sigma -> Sigma -> Prop :=
    | star_refl : forall sigma,
        star step sigma sigma
    | star_step : forall sigma tau rho,
        In _ (step sigma) tau ->
        star step tau rho ->
        star step sigma rho.

End Star.

Arguments star {Sigma}.
Arguments star_refl {Sigma step}.
Arguments star_step {Sigma step}.

(** [star_set step σ] is the set of all states reachable from [σ]
    via zero or more [step]-transitions — i.e., [⟦C⋆⟧(σ)]. *)
Definition star_set {Sigma : Type}
    (step : Sigma -> PSet Sigma) (sigma : Sigma) : PSet Sigma :=
  fun rho => star step sigma rho.

(* ================================================================= *)
(** ** Direct Powerset Denotation                                     *)
(* ================================================================= *)

(** [ol_denote atom_den C σ] gives the set of states reachable from
    [σ] by executing [C], using [atom_den] for atomic commands.

    Matches the paper's Figure 3 semantics exactly:
    - [⟦𝟎⟧(σ) = ∅]
    - [⟦𝟏⟧(σ) = {σ}]
    - [⟦C₁;C₂⟧(σ) = bind(⟦C₁⟧(σ), ⟦C₂⟧)]
    - [⟦C₁+C₂⟧(σ) = ⟦C₁⟧(σ) ∪ ⟦C₂⟧(σ)]
    - [⟦C⋆⟧(σ) = lfp(λf.λσ. f†(⟦C⟧(σ)) ∪ {σ})(σ)]
    - [⟦c⟧(σ) = ⟦c⟧_atom(σ)] *)

Section Denotation.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  Fixpoint ol_denote (C : ol_prog Atom) : Sigma -> PSet Sigma :=
    match C with
    | OLZero      => fun _ => pset_empty
    | OLOne       => fun sigma => pset_ret sigma
    | OLSeq C1 C2 => fun sigma => pset_bind (ol_denote C1 sigma) (ol_denote C2)
    | OLPlus C1 C2 => fun sigma => pset_union (ol_denote C1 sigma) (ol_denote C2 sigma)
    | OLStar C    => fun sigma => star_set (ol_denote C) sigma
    | OLAtom c    => atom_den c
    end.

End Denotation.

Arguments ol_denote {Atom Sigma}.

(* ================================================================= *)
(** ** Collecting Semantics                                           *)
(* ================================================================= *)

(** Given a per-state denotation [f : Σ → PSet Σ], the collecting
    extension [f†] lifts it to [PSet Σ → PSet Σ] via Kleisli
    extension (monadic bind). *)

Definition collect {Sigma : Type}
    (f : Sigma -> PSet Sigma) (S : PSet Sigma) : PSet Sigma :=
  pset_bind S f.

(* ================================================================= *)
(** ** Syntactic Sugar                                                *)
(* ================================================================= *)

(** [ol_iter C n] is the [n]-fold sequential composition [Cⁿ]:
    [C⁰ = 𝟏] and [Cⁿ⁺¹ = C ; Cⁿ]. *)
Fixpoint ol_iter {Atom : Type} (C : ol_prog Atom) (n : nat) : ol_prog Atom :=
  match n with
  | O   => OLOne
  | S k => OLSeq C (ol_iter C k)
  end.

(** [ol_for n C ≜ Cⁿ] — bounded iteration, per the paper. *)
Definition ol_for {Atom : Type} (n : nat) (C : ol_prog Atom) : ol_prog Atom :=
  ol_iter C n.

(** [ol_if guard_true guard_false C1 C2 ≜ (guard_true; C₁) + (guard_false; C₂)]
    Generic GCL conditional: the two guard programs encode the true/false
    branches.  Instantiate with [assume(b)] / [assume(¬b)] for standard
    if–then–else. *)
Definition ol_if {Atom : Type}
    (guard_true guard_false : ol_prog Atom)
    (C1 C2 : ol_prog Atom) : ol_prog Atom :=
  OLPlus (OLSeq guard_true C1) (OLSeq guard_false C2).

(** [ol_while guard_true guard_false C ≜ (guard_true; C)⋆; guard_false]
    Generic GCL while loop: iterated guarded body followed by exit guard.
    Instantiate with [assume(b)] / [assume(¬b)] for standard while(b). *)
Definition ol_while {Atom : Type}
    (guard_true guard_false : ol_prog Atom)
    (body : ol_prog Atom) : ol_prog Atom :=
  OLSeq (OLStar (OLSeq guard_true body)) guard_false.

Arguments ol_if  {Atom} guard_true guard_false C1 C2 /.
Arguments ol_while {Atom} guard_true guard_false body /.

(* ================================================================= *)
(** ** Star — Fundamental Properties                                  *)
(* ================================================================= *)

Section StarProperties.

  Context {Sigma : Type}.
  Variable step : Sigma -> PSet Sigma.

  (** One step embeds into the star. *)
  Lemma star_one_step : forall sigma tau,
    In _ (step sigma) tau -> star step sigma tau.
  Proof.
    intros sigma tau Hin.
    eapply star_step; [exact Hin | apply star_refl].
  Qed.

  (** Star is transitive. *)
  Lemma star_trans : forall sigma tau rho,
    star step sigma tau ->
    star step tau rho ->
    star step sigma rho.
  Proof.
    intros sigma tau rho H1 H2.
    induction H1 as [| s t u Hst _ IH].
    - exact H2.
    - eapply star_step; [exact Hst | exact (IH H2)].
  Qed.

  (** The star satisfies the fixed-point equation:
      [star_set step σ = {σ} ∪ bind(step(σ), star_set step)].
      This is the Coq rendition of [C⋆ = 𝟏 + C;C⋆]. *)
  Lemma star_unfold : forall sigma rho,
    In _ (star_set step sigma) rho <->
    In _ (pset_union (pset_ret sigma)
                     (pset_bind (step sigma)
                                (fun tau => star_set step tau))) rho.
  Proof.
    intros sigma rho. split.
    - intro Hstar. unfold star_set, In in Hstar.
      inversion Hstar; subst.
      + (* refl *) apply Union_introl. constructor.
      + (* step *) apply Union_intror.
        unfold pset_bind, In.
        exists tau. split; assumption.
    - intro Hunion. unfold star_set, In.
      inversion Hunion; subst.
      + (* ret *) inversion H; subst. apply star_refl.
      + (* bind *) destruct H as [tau [Hstep Hstar]].
        eapply star_step; [exact Hstep | exact Hstar].
  Qed.

  (** Star of a function that always returns empty yields only the
      starting state: [⟦𝟎⋆⟧(σ) = {σ}]. *)
  Lemma star_empty_step : forall sigma,
    star_set (fun _ : Sigma => pset_empty) sigma = pset_ret sigma.
  Proof.
    intro sigma. apply ensemble_ext. intro rho. split.
    - intro Hstar. unfold star_set, In in Hstar.
      inversion Hstar; subst.
      + constructor.
      + exfalso. inversion H.
    - intro Hret. inversion Hret; subst.
      unfold star_set, In. apply star_refl.
  Qed.

  (** [star step σ σ] always holds (reflexivity exposed at PSet level). *)
  Lemma star_set_refl : forall sigma,
    In _ (star_set step sigma) sigma.
  Proof. intro. unfold star_set, In. apply star_refl. Qed.

  (** Stepping then starring embeds in the star. *)
  Lemma star_set_step : forall sigma tau rho,
    In _ (step sigma) tau ->
    In _ (star_set step tau) rho ->
    In _ (star_set step sigma) rho.
  Proof.
    intros sigma tau rho Hstep Hstar.
    unfold star_set, In in *.
    eapply star_step; eassumption.
  Qed.

End StarProperties.

(* ================================================================= *)
(** ** Denotation Lemmas                                              *)
(* ================================================================= *)

Section DenotationLemmas.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** [⟦𝟎⟧(σ) = ∅] *)
  Lemma denote_zero : forall sigma,
    ol_denote atom_den OLZero sigma = pset_empty.
  Proof. reflexivity. Qed.

  (** [⟦𝟏⟧(σ) = {σ}] *)
  Lemma denote_one : forall sigma,
    ol_denote atom_den OLOne sigma = pset_ret sigma.
  Proof. reflexivity. Qed.

  (** Unfolding lemma for sequential composition. *)
  Lemma denote_seq : forall (C1 C2 : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq C1 C2) sigma =
      pset_bind (ol_denote atom_den C1 sigma) (ol_denote atom_den C2).
  Proof. reflexivity. Qed.

  (** Unfolding lemma for nondeterministic choice. *)
  Lemma denote_plus : forall (C1 C2 : ol_prog Atom) sigma,
    ol_denote atom_den (OLPlus C1 C2) sigma =
      pset_union (ol_denote atom_den C1 sigma) (ol_denote atom_den C2 sigma).
  Proof. reflexivity. Qed.

  (** Unfolding lemma for Kleene star. *)
  Lemma denote_star : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLStar C) sigma =
      star_set (ol_denote atom_den C) sigma.
  Proof. reflexivity. Qed.

  (** Unfolding lemma for atomic commands. *)
  Lemma denote_atom : forall (c : Atom) sigma,
    ol_denote atom_den (OLAtom c) sigma = atom_den c sigma.
  Proof. reflexivity. Qed.

  (** [⟦𝟎⋆⟧(σ) = {σ}] — the star of abort is skip. *)
  Lemma denote_star_zero : forall sigma,
    ol_denote atom_den (OLStar OLZero) sigma = pset_ret sigma.
  Proof.
    intro sigma. simpl. apply star_empty_step.
  Qed.

  (** [⟦C⋆⟧ = ⟦𝟏 + C ; C⋆⟧] — the key induction/unfolding principle. *)
  Lemma denote_star_unfold : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLStar C) sigma =
      ol_denote atom_den (OLPlus OLOne (OLSeq C (OLStar C))) sigma.
  Proof.
    intros C sigma. simpl.
    apply ensemble_ext. intro rho.
    apply star_unfold.
  Qed.

  (** Sequential composition respects denotational equality of the
      first component. *)
  Lemma denote_seq_cong_l : forall (C1 C1' C2 : ol_prog Atom),
    (forall sigma, ol_denote atom_den C1 sigma = ol_denote atom_den C1' sigma) ->
    forall sigma,
      ol_denote atom_den (OLSeq C1 C2) sigma =
        ol_denote atom_den (OLSeq C1' C2) sigma.
  Proof.
    intros C1 C1' C2 Heq sigma. simpl. rewrite Heq. reflexivity.
  Qed.

  (** Choice is commutative under the denotation. *)
  Lemma denote_plus_comm : forall (C1 C2 : ol_prog Atom) sigma,
    ol_denote atom_den (OLPlus C1 C2) sigma =
      ol_denote atom_den (OLPlus C2 C1) sigma.
  Proof.
    intros C1 C2 sigma. simpl. apply pset_union_comm.
  Qed.

  (** Choice is associative under the denotation. *)
  Lemma denote_plus_assoc : forall (C1 C2 C3 : ol_prog Atom) sigma,
    ol_denote atom_den (OLPlus (OLPlus C1 C2) C3) sigma =
      ol_denote atom_den (OLPlus C1 (OLPlus C2 C3)) sigma.
  Proof.
    intros C1 C2 C3 sigma. simpl. apply pset_union_assoc.
  Qed.

  (** [𝟎] is a left zero for sequential composition:
      [⟦𝟎 ; C⟧(σ) = ∅]. *)
  Lemma denote_seq_zero_l : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq OLZero C) sigma = pset_empty.
  Proof.
    intros C sigma. simpl. apply pset_bind_empty.
  Qed.

  (** [𝟏] is a left identity for sequential composition:
      [⟦𝟏 ; C⟧(σ) = ⟦C⟧(σ)]. *)
  Lemma denote_seq_one_l : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq OLOne C) sigma =
      ol_denote atom_den C sigma.
  Proof.
    intros C sigma. simpl. apply pset_bind_ret_l.
  Qed.

  (** [𝟏] is a right identity for sequential composition:
      [⟦C ; 𝟏⟧(σ) = ⟦C⟧(σ)]. *)
  Lemma denote_seq_one_r : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq C OLOne) sigma =
      ol_denote atom_den C sigma.
  Proof.
    intros C sigma. simpl. apply pset_bind_ret_r.
  Qed.

  (** Sequential composition is associative:
      [⟦(C₁ ; C₂) ; C₃⟧(σ) = ⟦C₁ ; (C₂ ; C₃)⟧(σ)]. *)
  Lemma denote_seq_assoc : forall (C1 C2 C3 : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq (OLSeq C1 C2) C3) sigma =
      ol_denote atom_den (OLSeq C1 (OLSeq C2 C3)) sigma.
  Proof.
    intros C1 C2 C3 sigma. simpl. apply pset_bind_assoc.
  Qed.

  (** [𝟎] is a left identity for choice: [⟦𝟎 + C⟧(σ) = ⟦C⟧(σ)]. *)
  Lemma denote_plus_zero_l : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLPlus OLZero C) sigma =
      ol_denote atom_den C sigma.
  Proof.
    intros C sigma. simpl. apply pset_union_empty_l.
  Qed.

  (** [𝟎] is a right identity for choice: [⟦C + 𝟎⟧(σ) = ⟦C⟧(σ)]. *)
  Lemma denote_plus_zero_r : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (OLPlus C OLZero) sigma =
      ol_denote atom_den C sigma.
  Proof.
    intros C sigma. simpl. apply pset_union_empty_r.
  Qed.

  (** Choice distributes over sequential composition (left):
      [⟦(C₁ + C₂) ; C₃⟧(σ) = ⟦C₁;C₃ + C₂;C₃⟧(σ)]. *)
  Lemma denote_seq_plus_distr_l : forall (C1 C2 C3 : ol_prog Atom) sigma,
    ol_denote atom_den (OLSeq (OLPlus C1 C2) C3) sigma =
      pset_union (ol_denote atom_den (OLSeq C1 C3) sigma)
                 (ol_denote atom_den (OLSeq C2 C3) sigma).
  Proof.
    intros C1 C2 C3 sigma. simpl. apply pset_bind_union.
  Qed.

End DenotationLemmas.

(* ================================================================= *)
(** ** Collecting Semantics — Properties                              *)
(* ================================================================= *)

Section CollectProperties.

  Context {Sigma : Type}.

  (** Collecting over the empty set yields the empty set. *)
  Lemma collect_empty : forall (f : Sigma -> PSet Sigma),
    collect f pset_empty = pset_empty.
  Proof. intro f. unfold collect. apply pset_bind_empty. Qed.

  (** Collecting distributes over union. *)
  Lemma collect_union : forall (f : Sigma -> PSet Sigma) (S1 S2 : PSet Sigma),
    collect f (pset_union S1 S2) =
      pset_union (collect f S1) (collect f S2).
  Proof.
    intros f S1 S2. unfold collect. apply pset_bind_union.
  Qed.

  (** Collecting a singleton is just function application. *)
  Lemma collect_ret : forall (f : Sigma -> PSet Sigma) (sigma : Sigma),
    collect f (pset_ret sigma) = f sigma.
  Proof. intros f sigma. unfold collect. apply pset_bind_ret_l. Qed.

  (** Collecting composes: [collect g ∘ collect f = collect (λσ. collect g (f σ))]. *)
  Lemma collect_compose : forall (f g : Sigma -> PSet Sigma) (S : PSet Sigma),
    collect g (collect f S) = collect (fun sigma => collect g (f sigma)) S.
  Proof. intros f g S. unfold collect. apply pset_bind_assoc. Qed.

End CollectProperties.

(* ================================================================= *)
(** ** N-fold Iteration — Properties                                  *)
(* ================================================================= *)

Section IterProperties.

  Context {Atom Sigma : Type}.
  Variable atom_den : Atom -> Sigma -> PSet Sigma.

  (** [C⁰ = 𝟏]. *)
  Lemma ol_iter_0 : forall (C : ol_prog Atom),
    ol_iter C 0 = OLOne.
  Proof. reflexivity. Qed.

  (** [Cⁿ⁺¹ = C ; Cⁿ]. *)
  Lemma ol_iter_S : forall (C : ol_prog Atom) (n : nat),
    ol_iter C (S n) = OLSeq C (ol_iter C n).
  Proof. reflexivity. Qed.

  (** [⟦C¹⟧(σ) = ⟦C⟧(σ)] — one iteration is just [C]. *)
  Lemma denote_iter_1 : forall (C : ol_prog Atom) sigma,
    ol_denote atom_den (ol_iter C 1) sigma =
      ol_denote atom_den C sigma.
  Proof. intros C sigma. simpl. apply pset_bind_ret_r. Qed.

  (** Every state reachable by [Cⁿ] starting from [σ] is reachable
      by [C⋆] starting from [σ]. *)
  Lemma iter_included_in_star : forall (C : ol_prog Atom) (n : nat) sigma rho,
    In _ (ol_denote atom_den (ol_iter C n) sigma) rho ->
    In _ (ol_denote atom_den (OLStar C) sigma) rho.
  Proof.
    intros C n. revert C.
    induction n as [| k IH]; intros C sigma rho Hin.
    - (* n = 0 *)
      simpl in Hin. inversion Hin; subst.
      simpl. apply star_set_refl.
    - (* n = S k *)
      simpl in Hin.
      unfold pset_bind, In in Hin.
      destruct Hin as [tau [Hc Hiter]].
      simpl. unfold star_set, In.
      eapply star_step.
      + exact Hc.
      + apply IH in Hiter. simpl in Hiter.
        exact Hiter.
  Qed.

  (** The star is the union of all finite iterations:
      [⟦C⋆⟧(σ) = ⋃ₙ ⟦Cⁿ⟧(σ)]. *)
  Lemma star_is_union_of_iters : forall (C : ol_prog Atom) sigma rho,
    In _ (ol_denote atom_den (OLStar C) sigma) rho <->
    exists n, In _ (ol_denote atom_den (ol_iter C n) sigma) rho.
  Proof.
    intros C sigma rho. split.
    - (* star -> exists n *)
      intro Hstar. simpl in Hstar. unfold star_set, In in Hstar.
      induction Hstar as [s | s t r Hstep _ IH].
      + exists 0. simpl. constructor.
      + destruct IH as [k Hk].
        exists (S k). simpl.
        unfold pset_bind, In.
        exists t. split; assumption.
    - (* exists n -> star *)
      intros [n Hn].
      apply iter_included_in_star with (n := n). exact Hn.
  Qed.

End IterProperties.
