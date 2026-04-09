(** * OL/SimpleGCL.v — Simple Guarded Command Language

    A clean instantiation of [ol_prog] for programs with just
    [assume] and [assign] atoms — no heap, no errors.
    Bridges the gap between abstract [ol_prog CAtom] and the
    full heap-based [mgcl_prog]. *)

From Stdlib Require Import Ensembles.
From OL Require Import Monad Assertion Lang Triple.
From OL.Rules Require Import Expression Generic.

(* ================================================================= *)
(** ** Simple Atoms                                                    *)
(* ================================================================= *)

(** Simple atoms: guards and deterministic state transforms. *)
Inductive simple_atom (Sigma : Type) : Type :=
  | SAssume (b : Sigma -> Prop)
  | SAssign (f : Sigma -> Sigma).

Arguments SAssume {Sigma} _.
Arguments SAssign {Sigma} _.

(* ================================================================= *)
(** ** Atom Denotation                                                 *)
(* ================================================================= *)

(** Denotation of simple atoms. *)
Definition simple_den {Sigma : Type}
    (a : simple_atom Sigma) : Sigma -> PSet Sigma :=
  match a with
  | SAssume b => assume_den b
  | SAssign f => assign_den f
  end.

(* ================================================================= *)
(** ** Program Type and Denotation                                     *)
(* ================================================================= *)

(** Simple GCL program type. *)
Definition sgcl_prog (Sigma : Type) := ol_prog (simple_atom Sigma).

(** Program denotation. *)
Definition sgcl_denote {Sigma : Type} (C : sgcl_prog Sigma) :=
  ol_denote simple_den C.

(* ================================================================= *)
(** ** Convenience Constructors                                        *)
(* ================================================================= *)

Definition sgcl_assume {Sigma} (b : Sigma -> Prop) : sgcl_prog Sigma :=
  OLAtom (SAssume b).

Definition sgcl_assign {Sigma} (f : Sigma -> Sigma) : sgcl_prog Sigma :=
  OLAtom (SAssign f).

Definition sgcl_if {Sigma} (b : Sigma -> Prop)
    (C1 C2 : sgcl_prog Sigma) : sgcl_prog Sigma :=
  ol_if (sgcl_assume b) (sgcl_assume (fun s => ~ b s)) C1 C2.

Definition sgcl_while {Sigma} (b : Sigma -> Prop)
    (body : sgcl_prog Sigma) : sgcl_prog Sigma :=
  ol_while (sgcl_assume b) (sgcl_assume (fun s => ~ b s)) body.

Arguments sgcl_assume {Sigma} b /.
Arguments sgcl_if {Sigma} b C1 C2 /.
Arguments sgcl_while {Sigma} b body /.
