
Require Import Coq.Init.Datatypes.
Require Import Coq.Init.Notations.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.


Inductive RuleName : Type :=
  | ruleName : string -> RuleName.

Inductive NameComp : Type :=
  | nc_wild : NameComp
  | nc_exact : string -> NameComp
  | nc_indexed : NameComp -> NameComp
  | nc_sequence : NameComp -> NameComp.

Inductive MatchPattern : Type :=
  | matchPattern : list NameComp -> MatchPattern.

Inductive RuleParameter : Type :=
  | rp_indexed : nat -> RuleParameter
  | rp_const : list NameComp -> RuleParameter.

Inductive Action : Type :=
  | action : RuleName -> list RuleParameter -> Action.

Inductive Expr : Type :=
  | expr : RuleName -> MatchPattern -> Action -> Expr.

Inductive Program : Type :=
  | program: list Expr -> Program.

Definition sampleRuleName := ruleName "test".

Definition sampleProgram :=
  program [(expr (ruleName "article")
                 (matchPattern [(nc_indexed (nc_sequence nc_wild));
                                  (nc_exact "blog");
                                  (nc_exact "article")])
                 (action (ruleName "author") [(rp_indexed 1)]))
          ].

Print sampleProgram.

(* maybe vector is better for proofing something related to length. *)