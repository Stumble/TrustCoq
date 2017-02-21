
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Strlib.
Require Export Setoid.

Import ListNotations.

Definition NameComp := string.

Definition Name := list NameComp.

Fixpoint beq_name (n1:Name) (n2:Name) : bool :=
  match n1,n2 with
  | [],[] => true
  | h1::t1, h2::t2 => if beq_string h1 h2 then beq_name t1 t2 else false
  | _, _ => false
  end.

(* Definition Data := prod (prod Name Name) Data. *)

Inductive Data : Type :=
| wraped_data : Name -> Name -> Data -> Data
| data : Name -> Name -> Data.

Inductive RuleName : Type :=
| ruleName : string -> RuleName.

Inductive MatchComp : Type :=
  | mc_wild : MatchComp
  | mc_sequence_wild : string -> MatchComp
  | mc_exact : string -> MatchComp
  | mc_indexed : MatchComp -> MatchComp.
(* you can't have index inside a index *)

Definition MatchPattern := list MatchComp.

Inductive MatchCompMatch : MatchComp -> NameComp -> Prop :=
| mcm_wild : forall x, MatchCompMatch mc_wild x
| mcm_exact : forall x,  MatchCompMatch (mc_exact x) x
| mcm_index : forall x y, MatchCompMatch x y -> MatchCompMatch (mc_indexed x) y
| mcm_seq : forall x y, x <> y -> MatchCompMatch (mc_sequence_wild x) y
.

Inductive regMatch : MatchPattern -> Name -> Prop :=
| Msingle : forall x y, MatchCompMatch x y -> regMatch [x] [y]
| Mseq : forall n1 n2 s1,
    regMatch [(mc_sequence_wild s1)] n1 ->
    regMatch [(mc_sequence_wild s1)] n2 ->
    regMatch [(mc_sequence_wild s1)] (n1 ++ n2)
| MApp : forall s1 r1 s2 r2,
    regMatch r1 s1 ->
    regMatch r2 s2 ->
    regMatch (r1 ++ r2) (s1 ++ s2).

Local Open Scope string_scope.

Example mcm1 : MatchCompMatch (mc_indexed (mc_sequence_wild "blog")) "a".
Proof.
  apply mcm_index. apply mcm_seq. apply string_neq_ref. reflexivity.
Qed.

Example regMatch1 : regMatch [(mc_indexed (mc_sequence_wild "blog"));
                              (mc_exact "blog");
                              (mc_exact "article")]
                             ["a";"b";"blog";"article"].
Proof.
Admitted.

Inductive RuleParameter : Type :=
  | rp_indexed : nat -> RuleParameter
  | rp_prefixOfIndexed : nat -> nat -> RuleParameter.

Inductive RuleCall : Type :=
  | ruleCall : RuleName -> list RuleParameter -> RuleCall.  

Inductive Action : Type :=
| actTryElse       : RuleCall -> RuleCall -> Action  
(* try expr1, if authentication failed, unwrap data and try Rule *)
| actRc            : RuleCall -> Action
| actOrAnchor      : RuleCall -> RuleCall -> Action
| actAnchor        : string -> Action.
(* if first pattern match, use first one, if pattern does not match try second anchor call *)

Inductive Expr : Type :=
  | expr : RuleName -> MatchPattern -> Action -> Expr.

Definition Program := list Expr.

Example sampleRuleName: RuleName := ruleName "test".

Example sampleProgram1 :=
  [(expr (ruleName "article")
                 [(mc_indexed (mc_sequence_wild "blog"));
                              (mc_exact "blog");
                              (mc_exact "article")]
                 (actRc (ruleCall (ruleName "author") [(rp_indexed 1)])
                 )
   );
     (expr (ruleName "author")
           [(mc_indexed (mc_sequence_wild "blog"));
              (mc_exact "blog");
              (mc_exact "article")]
           (actRc (ruleCall (ruleName "article") [(rp_prefixOfIndexed 1 1)])
         )
   )
  ].

Print sampleProgram1.

(* Definition tuple  := (true, true, true). *)

Print MatchPattern.
Print RuleParameter.

(*  *)
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

(* Fixpoint getExactContent (mc:MatchComp) : string := *)
(*   match mc with *)
(*   | mc_wild => ""%string *)
(*   | mc_sequence_wild => ""%string *)
(*   | mc_exact s => s *)
(*   | mc_indexed mc' => getExactContent mc' *)
(*   end. *)

Compute (hd mc_wild []).
              
Fixpoint isMatch (nm:Name) (mp:MatchPattern) : bool * (list Name) :=
  match mp with
  | [] => match nm with
          | [] => (true, [])
          | h :: t => (false, [])
          end
  | h :: t => match h with
              | mc_wild => isMatch (tl nm) t
              | mc_sequence_wild s => let (part1, rest) := findFirst s nm in
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
                                  | mc_sequence_wild s => let (indexedName, rest) := findFirst s nm in
                                                          let (isOk, indexedList) := isMatch rest t in
                                                          (isOk, indexedName :: indexedList)
                                  | _ => (false, [])
                                  end
              end
  end.

Example isMatch_test1 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild "c"));
                                  (mc_exact "c");
                                  (mc_exact "d")] = (true, [["a";"b"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test2 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild ""))] = (true, [["a";"b";"c";"d"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test3 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild "e"));
                                                     (mc_exact "e")]
                        = (false, [["a";"b";"c";"d"]]).
Proof.
  simpl. reflexivity.
Qed.

Example isMatch_test4 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild "c"));
                                                     (mc_exact "c")]
                        = (false, [["a";"b"]]).
Proof.
  simpl. reflexivity.
Qed.

Definition Network := list Data.

Definition empty_name : Name := [""].
Definition empty_data : Data := data empty_name empty_name.
Definition empty_expr : Expr := (expr (ruleName "") []
                                      (actRc (ruleCall (ruleName "") []))).

(* Definition State : Type := prod bool (prod RuleName nat). *)
(* bool, if it is firstTime, currentRule, recursive maximum times *)

Print Expr.

(* leave this part for later, right now, if not exist, just return False *)
(* Fixpoint ruleDefined (nm:string) (prog:Program) := *)
(*   match prog with *)
(*   | [] => false *)
(*   | e::t => let '(expr (ruleName rn) mp act) := e in *)
(*   end. *)

(* Fixpoint syntaxCheck (prog:Program) : bool := *)
(*   match prog with *)
(*   | [] => true *)
(*   | e::t => let '(expr (ruleName rn) mp act) := e in *)
(*             if ruleDefined rn prog *)
(*             then  *)
(*             else false *)
(*   end. *)

(*
syntax check:
1. ruleCall exist
2. indexedValue used is no more than indexed in matchPattern
3. substitution call is no more than indexed in matchPattern
*)


Fixpoint checker (prog:Program) : bool :=
  match prog with
  | [] => true
  | e::t => false
  end.

Print Expr.

Fixpoint hasPrefix (para:list RuleParameter) : bool :=
  match para with
  | [] => false
  | p::t => match p with
            | rp_indexed _ => false
            | rp_prefixOfIndexed _ _ => true
            end
  end.

Example hasPrefixTest1 : hasPrefix [(rp_prefixOfIndexed 1 1)] = true.
Proof.
  reflexivity.
Qed.

Fixpoint actionOf (name:string) (prog:Program) : Action :=
  match prog with
  | [] => actRc (ruleCall (ruleName "RuleNotExist") [])
  | e::t => match e with
            | expr (ruleName rname) _ act => if beq_string rname name
                                             then act
                                             else actionOf name t
            end
  end.


Fixpoint hasActLoop (rname:string) (act:Action) (limit:nat) (prog:Program) : bool :=
  match limit with
  | 0 => false
  | S n' =>
    match act with
    | actTryElse (ruleCall (ruleName rcname) para) _ => (if beq_string rcname rname
                                                         then true
                                                         else (hasActLoop rname (actionOf rcname prog) n' prog))
    | actOrAnchor (ruleCall (ruleName rcname) para) _ => if hasPrefix para then false else
                                                           (if (beq_string rcname rname) then true
                                                           else hasActLoop rname (actionOf rcname prog) n' prog)
    | actRc (ruleCall (ruleName rcname) para) =>  if hasPrefix para then false else
                                                    (if (beq_string rcname rname) then true
                                                     else hasActLoop rname (actionOf rcname prog) n' prog)
    | actAnchor _ => false
   end
  end.

Fixpoint hasLoop (e:Expr) (prog:Program) : bool :=
  let n := List.length prog in
  match e with
  | expr (ruleName s) mp act => hasActLoop s act n prog
  end.

Fixpoint checkNoLoopImpl (prog:Program) (progConst:Program) : bool :=
  match prog with
  | [] => true
  | e::t => if (hasLoop e progConst)
            then false
            else checkNoLoopImpl t progConst
  end.

Definition noLoop (prog:Program) := checkNoLoopImpl prog prog.

Example checkLoopTest1: noLoop sampleProgram1 = true.
Proof.
  unfold noLoop. simpl. reflexivity. 
  Qed.

Example sampleProgram2 :=
  [(expr (ruleName "article")
         [(mc_indexed (mc_sequence_wild "blog"));
                      (mc_exact "blog");
                      (mc_exact "article")]
         (actRc (ruleCall (ruleName "author") [(rp_indexed 1)])
         )
   );
     (expr (ruleName "author")
           [(mc_indexed (mc_sequence_wild "blog"));
              (mc_exact "blog");
              (mc_exact "article")]
           (actRc (ruleCall (ruleName "article") [(rp_indexed 1)])
         )
   )
  ].

Example checkLoopTest2 : noLoop sampleProgram2 = false.
Proof.
  reflexivity.
Qed.

Example sampleProgram3 :=
  [(expr (ruleName "article")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actRc (ruleCall (ruleName "author") [(rp_indexed 1)])
         )
   );
(expr (ruleName "author")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actRc (ruleCall (ruleName "admin") [(rp_indexed 1)])
         )
   );
(expr (ruleName "admin")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actRc (ruleCall (ruleName "author") [(rp_prefixOfIndexed 1 1)])
         )
   )
].

Example checkLoopTest3 : noLoop sampleProgram3 = true.
Proof.
  reflexivity.
Qed.

(* loop-trust: done *)


Fixpoint hasActAnchor (rname:string) (act:Action) (limit:nat) (prog:Program) : bool :=
  match limit with
  | 0 => false
  | S n' =>
    match act with
    | actTryElse (ruleCall (ruleName tryRule) _) (ruleCall (ruleName elseRule) _) =>
      if andb (hasActAnchor tryRule (actionOf tryRule prog) n' prog) (hasActAnchor elseRule (actionOf elseRule prog) n' prog)
      then true
      else false
    | actOrAnchor _ _ => true
    | actRc (ruleCall (ruleName rcname) para) => (hasActAnchor rcname (actionOf rcname prog) n' prog)
    | actAnchor _ => true
   end
  end.

Fixpoint hasAnchorCheck (e:Expr) (prog:Program) : bool :=
  let n := List.length prog in
  match e with
  | expr (ruleName s) mp act => hasActAnchor s act n prog
  end.

Fixpoint hasAnchorImpl (prog:Program) (progConst:Program) : bool :=
  match prog with
  | [] => true
  | e::t => if (hasAnchorCheck e progConst)
            then hasAnchorImpl t progConst
            else false
  end.

Definition hasAnchor (prog:Program) := hasAnchorImpl prog prog.

Example hasAnchorTest1 : hasAnchor sampleProgram1 = false.
Proof.
  reflexivity.
Qed.

Example hasAnchorTest2 : hasAnchor sampleProgram2 = false.
Proof.
  reflexivity.
Qed.

Example hasAnchorTest3 : hasAnchor sampleProgram3 = false.
Proof.
  reflexivity.
Qed.

Example sampleProgram4 :=
  [(expr (ruleName "article")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actRc (ruleCall (ruleName "author") [(rp_indexed 1)])
         )
   );
     (expr (ruleName "author")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actRc (ruleCall (ruleName "admin") [(rp_indexed 1)])
         )
   );
     (expr (ruleName "admin")
         [(mc_indexed (mc_sequence_wild "blog"))]
         (actOrAnchor (ruleCall (ruleName "author") [(rp_prefixOfIndexed 1 1)])
                     (ruleCall (ruleName "root") [])
         )
   );
     (expr (ruleName "root")
           [(mc_indexed (mc_sequence_wild "blog"))]
           (actAnchor "/usr/local/key1")
     )
].


Example hasAnchorTest4 : hasAnchor sampleProgram4 = true.
Proof.
  reflexivity.
Qed.

(* recursive dependecy on trust anchor: done*)

Fixpoint noSameAnchorBeforeBack (prog:Program) (anchorName:string) (homeName:string) (limit:nat) (act:Action) :=
  match limit with
  | 0 => false
  | S n' =>
    match act with
    | actTryElse (ruleCall (ruleName tryRule) _) _ => 
      if beq_string tryRule homeName then true
      else (if beq_string tryRule anchorName
            then false
            else (noSameAnchorBeforeBack prog anchorName homeName n' (actionOf tryRule prog )))
    | actAnchor _ => true
    | actOrAnchor (ruleCall (ruleName nextRule) _) (ruleCall (ruleName anchorRule) _) =>
      if beq_string anchorRule anchorName
      then false
      else (if beq_string homeName nextRule
            then true
            else (noSameAnchorBeforeBack prog anchorName homeName n' (actionOf nextRule prog))
           )
    | actRc (ruleCall (ruleName nextRule) para) =>
      (if beq_string homeName nextRule
       then true
       else (if beq_string nextRule anchorName
             then false
             else (noSameAnchorBeforeBack prog anchorName homeName n' (actionOf nextRule prog ))
            )
      )
    end
  end.
         

Fixpoint satisfyLppCheck (e:Expr) (prog:Program) : bool :=
  let n := List.length prog in
  match e with
  | expr (ruleName exprName) mp act =>
    match act with
    | actOrAnchor (ruleCall (ruleName nextRule) _) (ruleCall (ruleName anchorRule) _) =>
      noSameAnchorBeforeBack prog anchorRule exprName n (actionOf nextRule prog) 
    | _ => true
    end
  end.

Fixpoint satisfyLppImpl (prog:Program) (progConst:Program) : bool :=
  match prog with
  | [] => true
  | e::t => if (satisfyLppCheck e progConst)
            then satisfyLppImpl t progConst
            else false
  end.

Definition satisfyLpp (prog:Program) := satisfyLppImpl prog prog.

Example satisfyLppTest1 : satisfyLpp sampleProgram1 = true.
Proof.
  reflexivity.
Qed.

Example satisfyLppTest2 : satisfyLpp sampleProgram2 = true.
Proof.
  reflexivity.
Qed.

Example satisfyLppTest3 : satisfyLpp sampleProgram3 = true.
Proof.
  reflexivity.
Qed.

Example satisfyLppTest4 : satisfyLpp sampleProgram4 = true.
Proof.
  reflexivity.
Qed.

Example sampleProgram5 :=
  [
    (expr (ruleName "sub.foo.com")
         []
         (actRc (ruleCall (ruleName "foo.com") [(rp_indexed 1)])
         )
   );
     (expr (ruleName "foo.com")
         []
         (actRc (ruleCall (ruleName ".com") [(rp_indexed 1)])
         )
   );
     (expr (ruleName "bar.com")
         []
         (actOrAnchor (ruleCall (ruleName "foo.com") [(rp_prefixOfIndexed 1 1)])
                     (ruleCall (ruleName ".com") [])
         )
   );
     (expr (ruleName ".com")
           []
           (actAnchor "/usr/local/key1")
     )
].

Example satisfyLppTest5 : satisfyLpp sampleProgram5 = false.
Proof.
  reflexivity.
Qed.

(* least privilege principle: done*)


(* Lemma regEquivlence : forall name p, regMatch p name <-> fst (isMatch name p) = true. *)
(* Proof. *)
(* Admitted. *)

(* Lemma interpreterTerminate : forall prog net data, *)
(*     propertyCheck prog -> exists i, interpreter i prog net data emptyState = Some rst. *)
(* Proof. *)
(* Admitted. *)


Inductive Rtn : Type :=
| keyNotMatch : Rtn
| authFail : Rtn 
| networkFail : Rtn
| succ : Rtn
| noMatchingRule : Rtn
| noMorePrefix : Rtn
| unwrapFailed : Rtn
.

Definition getKeyLocator (data:Data) : Name :=
  match data with
  | data name key => key
  | wraped_data name key _ => key
  end.

Definition getName (data:Data) : Name :=
  match data with
  | data name key => name
  | wraped_data name key _ => name
  end.

Definition unwrap (data:Data) : option Data :=
  match data with
  | data _ _ => None
  | wraped_data _ _ d => Some d
  end.

(* one more check on that data is mostly wraped once *)

(* 当匹配时，目前先传n'，到时候再看是不是可以传更科学的数值，例如程序的最长环的长度 * name的长度？ *)
Print isMatch.
Print Expr.
Print RuleParameter.

Fixpoint getPrefix (nm:Name) (n:nat) : option Name :=
  match n with
  | 0 => Some []
  | S n' => match nm with
            | [] => None
            | h::t => match (getPrefix t n') with
                      | None => None
                      | Some rtn => Some (h::rtn)
                      end
            end
  end.

Fixpoint genArgs (indexed:list Name) (rp: list RuleParameter) : option (list Name) :=
  match rp with
  | [] => Some []
  | h::t => match h with
            | rp_indexed n => let nm := (nth (pred n) indexed empty_name) in
                              match (genArgs indexed t) with
                              | None => None
                              | Some rtn => Some (nm :: rtn)
                              end
            | rp_prefixOfIndexed n nPrefix => let nm := (nth (pred n) indexed empty_name) in
                                              match (getPrefix nm nPrefix) with
                                              | None => None
                                              | Some prefix => match (genArgs indexed t) with
                                                               | None => None
                                                               | Some rtn => Some (prefix::rtn)
                                                               end
                                              end
            end
  end.

Fixpoint getExpr (prog:Program) (name:RuleName) : Expr :=
  match prog with
  | [] => empty_expr
  | e::t => let '(expr (ruleName ename) _ _) := e in
            let '(ruleName rname) := name in
            if beq_string ename rname
            then e
            else getExpr t name
  end.

Example getExprTest1 : getExpr sampleProgram5 (ruleName ".com") = (expr (ruleName ".com") [] (actAnchor "/usr/local/key1")).
Proof.
  reflexivity.
Qed.

Fixpoint getKey (net:Network) (data:Data) :=
  match net with
  | [] => empty_data
  | h::t => if beq_name (getName h) (getKeyLocator data)
            then h
            else getKey t data
  end.

Fixpoint argTest (arg1:list Name) (arg2:list Name) : bool :=
  match arg1,arg2 with
  | _, [] => true
  | h1::t1,h2::t2 => if beq_name h1 h2
                     then argTest t1 t2
                     else false
  | _,_ => false
  end.

Fixpoint interpr_follow (progConst:Program) (n:nat) (net:Network)
         (data:Data) (expr:Expr) (args:list Name) :=
  match n with
  | 0 => None
  | S n' =>
    let interpr_follow_next := interpr_follow progConst n' net in
    let '(expr rname mp act) := expr in
    match isMatch (getName data) mp with
    | (false, _) => Some keyNotMatch
    | (true, indexed) =>
      match (argTest indexed args) with
      | false => Some keyNotMatch
      | true =>
              match act with
              | actTryElse tr el =>
                let '(ruleCall trRn trPl) := tr in
                let '(ruleCall elRn elPl) := el in
                match (genArgs indexed trPl) with
                | None => Some noMorePrefix
                | Some trArgs =>  match interpr_follow_next (getKey net data) (getExpr progConst trRn) (trArgs) with
                                  | Some authFail =>
                                    match unwrap data with
                                    | None => Some unwrapFailed
                                    | Some idata => interpr_follow_next (getKey net idata) (getExpr progConst elRn) []
                                    end
                                  | otherwise => otherwise
                                  end
                end
              | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with
                                                | None => Some noMorePrefix
                                                | Some nxtArgs => 
                                                  interpr_follow_next (getKey net data) (getExpr progConst nxtRn) nxtArgs
                                                end
              | actAnchor addr => Some succ
              | actOrAnchor pRule aRule =>
                let '(ruleCall pRn pPl) := pRule in
                let '(ruleCall aRn aPl) := aRule in
                match (genArgs indexed pPl) with
                | None => Some noMorePrefix
                | Some pArgs =>
                  match interpr_follow_next (getKey net data) (getExpr progConst pRn) pArgs with
                  | Some keyNotMatch =>
                    match (genArgs indexed aPl) with
                    | None => None
                    | Some aArgs => interpr_follow_next (getKey net data) (getExpr progConst aRn) aArgs
                    end
                  | otherwise => otherwise
                  end
                end
              end
      end
    end
  end.

Fixpoint interpr_findMatchRule (progConst:Program) (n:nat) (prog:Program) (net:Network)
         (data:Data) : option Rtn:=
  match n with
  | 0 => None
  | S n' => match prog with
            | [] => Some noMatchingRule
            | (expr rname mp act)::t =>
              let '(bMatch, indexed) := isMatch (getName data) mp in
              match bMatch with
              | false => interpr_findMatchRule progConst n' t net data
              | true => interpr_follow progConst n' net data (getExpr progConst rname) []
              end
            end
  end.

Fixpoint interpr_findMatchRule_check (progConst:Program) (n:nat) (prog:Program) (net:Network)
         (data:Data) : option Expr:=
  match n with
  | 0 => None
  | S n' => match prog with
            | [] => None
            | (expr rname mp act)::t =>
              let '(bMatch, indexed) := isMatch (getName data) mp in
              match bMatch with
              | false => interpr_findMatchRule_check progConst n' t net data
              | true => Some (getExpr progConst rname)
              end
            end
  end.



Example sampleProgram6 :=
  [(expr (ruleName "article")
         [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "article");(mc_wild)]
         (actRc (ruleCall (ruleName "author") [(rp_indexed 1)]))
   );
     (expr (ruleName "author")
           [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "author");(mc_wild)]
           (actRc (ruleCall (ruleName "admin") [(rp_indexed 1)]))
     );
     (expr (ruleName "admin")
           [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "admin");(mc_wild)]
           (actRc (ruleCall (ruleName "root") [(rp_indexed 1)]))
     );
     (expr (ruleName "root")
           [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "KEY");(mc_wild)]
           (actAnchor "/usr/local/key1")
     )
  ].

Example dataArticle := data ["domain";"test";"blog";"article";"1"] ["domain";"test";"blog";"author";"1"].
Example dataAuthor := data ["domain";"test";"blog";"author";"1"] ["domain";"test";"blog";"admin";"1"].
Example dataAdmin:= data ["domain";"test";"blog";"admin";"1"] ["domain";"test";"blog";"KEY";"1"].
Example dataKey := data ["domain";"test";"blog";"KEY";"1"] [""].

Example blogNet := [dataKey; dataAdmin; dataAuthor; dataArticle].

Compute interpr_findMatchRule sampleProgram6 10 sampleProgram6 blogNet dataArticle.

(* Compute interpr_follow sampleProgram6 9 blogNet dataAdmin (getExpr sampleProgram6 (ruleName "admin")) []. *)

(* Compute isMatch (getName dataKey) [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "KEY");(mc_wild)]. *)

(* Compute let '(expr rname mp act) := (getExpr sampleProgram6 (ruleName "admin")) in *)
(* match isMatch (getName dataAdmin) mp with *)
(* | (false, _) => None *)
(* | (true, indexed) =>  *)
(*   match (argTest indexed []) with *)
(*   | false => None *)
(*   | true => match act with *)
(*             | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with *)
(*                                               | None => None *)
(*                                               | Some nxtArgs =>  *)
(*                                                 Some (getKey blogNet dataAdmin) *)
(*                                                 (* interpr_follow_next (getKey net data) (getExpr progConst nxtRn) nxtArgs *) *)
(*                                               end *)
(*             | _ => None *)
(*             end *)
(*   end *)
(* end. *)

              


Definition beq_data (d1:Data) (d2:Data) : bool :=
  beq_name (fst d1) (fst d2).


Fixpoint bin_network (data:Data) (network:Network) : bool :=
  match network with
  | [] => false 
  | h :: t => if (beq_data data h) then bin_network data t else false
  end.

(* we have to assume that the data from network is formed in a
   ordered-list that the next one is the one that we want
*)

(* Fixpoint shrink_network (data:Data) (network:Network) : Network := *)
(*   match network with *)
(*   | [] => [] *)
(*   | h :: t => if (beq_data data h) *)
(*               then shrink_network data t *)
(*               else h::(shrink_network data t) *)
(*   end. *)



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
