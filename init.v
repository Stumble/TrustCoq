
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Strlib.

Import ListNotations.

Definition Name := list string.

Definition Data := prod Name Name.

Inductive RuleName : Type :=
| ruleName : string -> RuleName.

Inductive MatchComp : Type :=
  | mc_wild : MatchComp
  | mc_sequence_wild : MatchComp
  | mc_exact : string -> MatchComp
  | mc_indexed : MatchComp -> MatchComp.

Definition MatchPattern := list MatchComp.

Inductive RuleParameter : Type :=
  | rp_indexed : nat -> RuleParameter
  | rp_const : Name -> RuleParameter.

Inductive Action : Type :=
  | action : RuleName -> list RuleParameter -> Action.

Inductive Expr : Type :=
  | expr : RuleName -> MatchPattern -> Action -> Expr.

Inductive Program : Type :=
  | program: list Expr -> Program.

Example sampleRuleName: RuleName := ruleName "test".

Example sampleProgram :=
  program [(expr (ruleName "article")
                 [(mc_indexed (mc_sequence_wild));
                                  (mc_exact "blog");
                                  (mc_exact "article")]
                 (action (ruleName "author") [(rp_indexed 1)]))
          ].

Print sampleProgram.

(* Definition tuple  := (true, true, true). *)


(* Fixpoint expandPattern (mp:MatchPattern) (rp:RuleParameter) : MatchPattern := *)
(*   end. *)

(* firstPart, rest(targetIncluded) *)
Fixpoint findFirst (target:string) (nm:Name) : Name * Name :=
  match nm with
  | [] => ([], [])
  | h :: t => match (beq_string target h) with
              | true => ([], h :: t)
              | false => let (matched, rest):= (findFirst target t) in
                         (h :: matched, rest)
              end
  end.

Compute findFirst "test"%string [  "a"%string;
                                   "b"%string;
                                   "c"%string;
                                   "test"%string;
                                   "e"%string
                                ].
Print MatchComp.

Fixpoint getExactContent (mc:MatchComp) : string :=
  match mc with
  | mc_wild => ""%string
  | mc_sequence_wild => ""%string
  | mc_exact s => s
  | mc_indexed mc' => getExactContent mc'
  end.

Compute (hd mc_wild []).
              
Fixpoint isMatch (nm:Name) (mp:MatchPattern) : bool * (list Name) :=
  match mp with
  | [] => match nm with
          | [] => (true, [])
          | h :: t => (false, [])
          end
  | h :: t => match h with
              | mc_wild => isMatch (tl nm) t
              | mc_sequence_wild => let target := getExactContent (hd mc_wild t) in
                                    let (part1, rest) := findFirst target nm in
                                    (isMatch rest t)
              | mc_exact ss => match nm with
                               | [] => (false, [])
                               | hd_nm :: tl_nm =>
                                 if (beq_string ss hd_nm)
                                 then isMatch (tl_nm) t
                                 else (false, [])
                               end
              | mc_indexed nmx => match nmx with
                                  | mc_wild => let (isOk, indexedList) := isMatch (tl nm) t in
                                               (isOk, [(hd ""%string nm)] :: indexedList)
                                  | mc_exact ss => match nm with
                                                   | [] => (false, [])
                                                   | hd_nm :: tl_nm => if (beq_string ss hd_nm)
                                                                       then
                                                                         let (isOk, indexedList) := isMatch tl_nm t in
                                                                         (isOk, [ss]::indexedList)
                                                                       else (false, [])
                                                   end
                                  | mc_sequence_wild => let target := getExactContent (hd mc_wild t) in
                                                        let (indexedName, rest) := findFirst target nm in
                                                        let (isOk, indexedList) := isMatch rest t in
                                                        (isOk, indexedName :: indexedList)
                                  | _ => (false, [])
                                  end
              end
  end.

Local Open Scope string_scope.
Example isMatch_test1 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild));
                                  (mc_exact "c");
                                  (mc_exact "d")] = (true, [["a";"b"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test2 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild))] = (true, [["a";"b";"c";"d"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test3 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild));
                                                     (mc_exact "e")]
                        = (false, [["a";"b";"c";"d"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test4 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild));
                                                     (mc_exact "c")]
                        = (false, [["a";"b"]]).
Proof.
  simpl. reflexivity.
Qed.

Definition Network := list Data.

(* Fixpoint execution (prog:program) (input:map) : bool := *)

(* isMatch examples *)

(* this kind of definition of regular expression cut off the backtracking part of
   usuall regular expression. In another word, there is only one way that a string
   could be match.
   This result is very intuitive, since it only run a one-way pass alone the way, instead of
   doing a backtracking search that might have server cases. *)

(* execution *)

(* if prog violate some rules, then is will fail in checker *)

(* Fixpoint checker (prog:program) : bool :=. *)

(* Fixpoint execution (prog:program) (input:map) : bool := *)

(* Fixpoint firstRule (prog:program) (data:Data) (network) *)
(*          find the first match. *)
(*   call execution (ruleName) parameter program Newdata network  *)

       (* to make at least one parameter shrink, here we have to use network as List Data
          and erase data every time you fetch it.
        this serves the same function as having a map to prevent dealing with same data packet*)
  

(* todo *)
(* how to use map *)
(* write execution *)

(* write a dummy matching interface*)