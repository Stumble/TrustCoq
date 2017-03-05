Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Strlib.
Require Import Notations Logic Datatypes.
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

Fixpoint nameToString (name:Name) : string :=
  match name with
  | h :: t => h
  | _ => ""
  end.

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
(*
   if first pattern match, use first one,
   if pattern does not match,
   or get an exception of noMorePrefix,
   try second anchor call
 *)

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

(* Fixpoint getExactContent (mc:MatchComp) : string := *)
(*   match mc with *)
(*   | mc_wild => ""%string *)
(*   | mc_sequence_wild => ""%string *)
(*   | mc_exact s => s *)
(*   | mc_indexed mc' => getExactContent mc' *)
(*   end. *)

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

Example isMatch_test5 : isMatch ["a";"b";"c";"d"] [(mc_indexed (mc_sequence_wild "a"));
                                                     (mc_exact "a");(mc_sequence_wild "")]
                        = (true, [[]]).
Proof.
  simpl. reflexivity.
Qed.

Definition Network := list Data.

Definition empty_name : Name := [""].
Definition empty_data : Data := data empty_name empty_name.
Definition empty_expr : Expr := (expr (ruleName "") []
                                      (actRc (ruleCall (ruleName "") []))).

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

Fixpoint has1stArg (para:list RuleParameter) : bool :=
  match para with
  | [] => false
  | p::t => match p with
            | rp_indexed _ => true
            | rp_prefixOfIndexed _ n => Nat.leb n 1
            end
  end.

Fixpoint mustHave1stArg (prog:Program) : bool :=
  match prog with
  | [] => true
  | (expr _ _ act)::t => match act with
                      | actTryElse _ _=> mustHave1stArg t
                      | actOrAnchor (ruleCall _ para) _ =>
                        if has1stArg para then mustHave1stArg t
                        else false
                      | actRc (ruleCall _ para) => if has1stArg para then mustHave1stArg t
                                            else false
                      | actAnchor _ => mustHave1stArg t
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

Inductive Rtn : Type :=
| keyNotMatch : Rtn
| authFail : Rtn
| networkFail : Rtn
| succ : Rtn
| noMatchingRule : Rtn
| noMorePrefix : Rtn
| unwrapFailed : Rtn
| debug1 : Rtn
| debug2 : Rtn
| rtnDebugExpr : Expr -> Rtn
| rtnDebugAny :  forall X, X -> Rtn
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

Fixpoint getPrefix (nm:Name) (n:nat) : option Name :=
  let len := length nm in
  match Nat.ltb len n with
  | true => None
  | false => match Nat.eqb len n with
             | true => Some []
             | false => match nm with
                        | h::t => match (getPrefix t n) with
                                  | None => None
                                  | Some rtn => Some (h::rtn)
                                  end
                        | _ => None
                        end
             end
  end.

Example getPrefixTest1 : getPrefix ["a";"b";"c";"d"] 2 = Some ["a";"b"].
Proof.
  reflexivity.
Qed.

Example getPrefixTest2 : getPrefix ["c";"d"] 2 = Some [].
Proof.
  reflexivity.
Qed.

Example getPrefixTest3 : getPrefix ["c";"d"] 3 = None.
Proof.
  reflexivity.
Qed.

Example getPrefixTest4 : getPrefix [] 1 = None.
Proof.
  reflexivity.
Qed.

Fixpoint genArgs (indexed:list Name) (rp: list RuleParameter) : option (list Name) :=
  match rp with
  | [] => Some []
  | h::t => match h with
            | rp_indexed n => let nm := (nth (pred n) indexed empty_name) in
                              match (genArgs indexed t) with
                              | None => None
                              | Some rtn => Some (nm :: rtn)
                              end
            | rp_prefixOfIndexed n minusN => let nm := (nth (pred n) indexed empty_name) in
                                              match (getPrefix nm minusN) with
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
          | Some trArgs =>  match interpr_follow_next data (getExpr progConst trRn) (trArgs) with
                            | Some authFail =>
                              (* Some (rtnDebugAny Expr (getExpr progConst elRn)) *)
                              match unwrap data with
                              | None => Some unwrapFailed
                              (* handover the inner_data to elseRule *)
                              | Some idata => interpr_follow_next idata (getExpr progConst elRn) []
                              end
                            | otherwise => otherwise
                            end
          end
        | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with
                                          | None => Some noMorePrefix
                                          | Some nxtArgs =>
                                            interpr_follow_next (getKey net data) (getExpr progConst nxtRn) nxtArgs
                                          end
        | actAnchor addr => if beq_string addr (nameToString (getKeyLocator data))
                            then Some succ
                            else Some authFail
        | actOrAnchor pRule aRule =>
          let '(ruleCall pRn pPl) := pRule in
          let '(ruleCall aRn aPl) := aRule in
          match (genArgs indexed pPl) with
          (* this mean no more prefix, directly handover this packet to anchor rule *)
          | None =>
            (* (rtnDebugAny Data data) *)
            match (genArgs indexed aPl) with
            | None => None
            | Some aArgs => interpr_follow_next data (getExpr progConst aRn) aArgs
            end
          | Some pArgs =>
            (* Some (rtnDebugAny Data data) *)
            interpr_follow_next (getKey net data) (getExpr progConst pRn) pArgs
          end
        end
      end
    end
  end.

Fixpoint interpr_findMatchRule (prog:Program) (data:Data) : option Expr :=
  match prog with
  | [] => None
  | h::t =>
    let '(expr rname mp act) := h in
    let '(bMatch, indexed) := isMatch (getName data) mp in
    match bMatch with
    | false => interpr_findMatchRule t data
    | true => Some h
    end
  end.

Fixpoint interpr_main (prog:Program) (n:nat)
         (net:Network) (data:Data) : option Rtn :=
  match interpr_findMatchRule prog data with
  | None => Some noMatchingRule
  | Some eMatched => interpr_follow prog n net data eMatched []
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
Example dataKey := data ["domain";"test";"blog";"KEY";"1"] ["/usr/local/key1"].

Example blogNet := [dataKey; dataAdmin; dataAuthor; dataArticle].

Example interpreterTest1 : interpr_main sampleProgram6 10 blogNet dataArticle = Some succ.
Proof.
  reflexivity.
Qed.

Example sampleProgramNdns :=
  [(expr (ruleName "CacheResolver")
         [(mc_exact "NDNS-R");(mc_sequence_wild "")]
         (actTryElse (ruleCall (ruleName "Local") []) (ruleCall (ruleName "NDNS-data") []))
   );
     (expr (ruleName "NDNS-data")
           [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_wild);(mc_exact "NS");(mc_indexed (mc_sequence_wild ""))]
           (actRc (ruleCall (ruleName "NDNS-DSK") [(rp_indexed 1)]))
     );

     (expr (ruleName "NDNS-DSK")
           [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_exact "DSK");(mc_indexed (mc_sequence_wild ""))]
           (actRc (ruleCall (ruleName "NDNS-KSK") [(rp_indexed 1)]))
     );

     (expr (ruleName "NDNS-KSK")
           [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_exact "KSK");(mc_indexed (mc_sequence_wild ""))]
           (actOrAnchor (ruleCall (ruleName "NDNS-DKEY") [(rp_prefixOfIndexed 1 1)])
                        (ruleCall (ruleName "NDNS-Root") []))
     );

     (expr (ruleName "NDNS-DKEY")
           [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_wild);(mc_exact "DKEY");(mc_indexed (mc_sequence_wild ""))]
           (actRc (ruleCall (ruleName "NDNS-DSK") [(rp_indexed 1)]))
     );

     (expr (ruleName "Local")
           [(mc_exact "NDNS-R");(mc_sequence_wild "")]
           (actAnchor "/usr/local/ucla/key")
     );

     (expr (ruleName "NDNS-Root")
           [(mc_exact "NDNS");(mc_sequence_wild "")]
           (actAnchor "/usr/local/dns/key")
     )
  ].

(* "NDNS-R/com/ucla/NDNS/www/NS/v1/s1" *)
(*   "usr/local/ucla/key" *)
(* "com/ucla/NDNS/www/NS/v1/s1" *)
(* "com/ucla/NDNS/DSK/CERT/1" *)
(* "com/ucla/NDNS/KSK/CERT/1" *)
(* "com/NDNS/ucla/DKEY/CERT/1" *)
(* "com/NDNS/DSK/CERT/1" *)
(* "com/NDNS/KSK/CERT/1" *)
(* "NDNS/com/DKEY/CERT/1" *)
(* "NDNS/DSK/CERT/1" *)
(* "NDNS/KSK/CERT/1" *)
(* "usr/local/dns/key" *)

Example data0 := data ["com";"ucla";"NDNS";"www";"NS";"v1";"s1"] ["com";"ucla";"NDNS";"DSK";"CERT";"1"].
Example data1 := data ["com";"ucla";"NDNS";"DSK";"CERT";"1"] ["com";"ucla";"NDNS";"KSK";"CERT";"1"].
Example data2 := data ["com";"ucla";"NDNS";"KSK";"CERT";"1"] ["com";"NDNS";"ucla";"DKEY";"CERT";"1"].
Example data3 := data ["com";"NDNS";"ucla";"DKEY";"CERT";"1"] ["com";"NDNS";"DSK";"CERT";"1"].
Example data4 := data ["com";"NDNS";"DSK";"CERT";"1"] ["com";"NDNS";"KSK";"CERT";"1"].
Example data5 := data ["com";"NDNS";"KSK";"CERT";"1"] ["NDNS";"com";"DKEY";"CERT";"1"].
Example data6 := data ["NDNS";"com";"DKEY";"CERT";"1"] ["NDNS";"DSK";"CERT";"1"].
Example data7 := data ["NDNS";"DSK";"CERT";"1"] ["NDNS";"KSK";"CERT";"1"].
Example data8 := data ["NDNS";"KSK";"CERT";"1"] ["/usr/local/dns/key"].
Example dataR := wraped_data ["NDNS-R";"com";"ucla";"NDNS";"www";"NS";"v1";"s1"] ["/usr/local/mit/key"] data0.
Example NdnsNet := [data0;data1;data2;data3;data4;data5;data6;data7;data8;dataR].

Example interpreterTest2 : interpr_main sampleProgramNdns 100 NdnsNet dataR = Some succ.
Proof.
  reflexivity.
Qed.

Fixpoint exprLength (prog:Program) : nat :=
  match prog with
  | [] => 0
  | h::t => Nat.add 1 (exprLength t)
  end.

Fixpoint similarFindMatch (n:nat) (l:list nat) (target:nat) : option bool :=
  match n with
  | 0 => None
  | S n' => match l with
            | [] => Some false
            | h::t => if Nat.eqb h target
                      then Some true
                      else similarFindMatch n' t target
            end
  end.

(* Arguments similarFindMatch n l target: simpl never. *)
(* Arguments Nat.add n m: simpl never. *)
(* Arguments Nat.add n m : simpl never. *)
Lemma similarProofTerminate : forall l target,
    exists nStep rtn, similarFindMatch nStep l target = Some rtn.
Proof.
  intros.
  exists (S (List.length l)).
  induction l as [|h t].
  - simpl. exists false. reflexivity.
  - destruct IHt. simpl. destruct Nat.eqb.
    + eauto.
    + eauto.
Qed.

Inductive State : Type :=
| state : Program -> Data -> Network -> Expr -> (list Name)-> nat -> State
| state_finished : Rtn -> State.

Inductive Rst : Type :=
| unfinish
| finished : Rtn -> Rst.

Print Rst_ind.

Fixpoint interpr_step (st:State) : State :=
  match st with
  | state_finished r => state_finished r
  | state progConst dt net e args nStepAfterArgDeduction =>
    let '(expr rname mp act) := e in
    match isMatch (getName dt) mp with
    | (false, _) => state_finished keyNotMatch
    | (true, indexed) =>
      match (argTest indexed args) with
      | false => state_finished keyNotMatch
      | true =>
        match act with
        | actTryElse tr el => state_finished noMorePrefix
        | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with
                                          | None => state_finished noMorePrefix
                                          | Some nxtArgs => (state progConst (getKey net dt) net (getExpr progConst nxtRn) nxtArgs 0)
                                          end
        | actAnchor addr => if beq_string addr (nameToString (getKeyLocator dt))
                            then state_finished succ
                            else state_finished authFail
        | actOrAnchor pRule aRule =>
          let '(ruleCall pRn pPl) := pRule in
          let '(ruleCall aRn aPl) := aRule in
          match (genArgs indexed pPl) with
          (* this mean no more prefix, directly handover this packet to anchor rule *)
          | None =>
            (* (rtnDebugAny Data data) *)
            match (genArgs indexed aPl) with
            | None => state_finished noMorePrefix
            | Some aArgs => state progConst dt net (getExpr progConst aRn) aArgs 0
            end
          | Some pArgs =>
            (* Some (rtnDebugAny Data data) *)
            state progConst (getKey net dt) net (getExpr progConst pRn) pArgs 0
          end
        end
      end
    end
  end.

Fixpoint getnPrefix (args: list Name) : nat :=
  match args with
  | [] => 0
  | h::t => (List.length h)
  end.
  
Fixpoint F (st:State) : nat :=
  match st with
  | (state prog dt net e args nStepAfterArgDeduction) =>
    (List.length prog) * (getnPrefix args) - nStepAfterArgDeduction + (List.length prog)
  | state_finished _ => 0
  end.

Print State_ind.

Lemma boring : forall st st' prog prog' dt dt' net net' e e' args args' n n' rname mp act indexed,
    (e = expr rname mp act) ->
    (isMatch (getName dt) mp = (true, indexed)) ->
    (argTest indexed args = true) ->
    (st = state prog dt net e args n) -> (st' = state prog' dt' net' e' args' n')
                              -> (interpr_step st = st') -> prog = prog'.
  intros st st' prog prog' dt dt' net net' e e' args args' n n' rname mp act indexed.
  intros Hexpr HisMatch HargTest Hst Hst' Hstep.
  rewrite Hexpr in Hst.
  rewrite Hst in Hstep.
  unfold interpr_step in Hstep.
  rewrite HisMatch in Hstep.
  rewrite HargTest in Hstep.
  destruct act.
  + rewrite Hst' in Hstep.
    inversion Hstep.
  + 
    Admitted.
(*   (* destruct net. *) *)
(*   (* unfold interpr_step in H1. *) *)
(* (* | state : Program -> Data -> Network -> Expr -> (list Name)-> nat -> State *) *)
(* (* | state_finished : Rtn -> State. *) *)

(*   (* + destruct expr0 as [rname0 mp0 act0]. *) *)
(* destruct (getName dt0) eqn:Heq1. *)
(* destruct mp0. *)
(* simpl in H1. *)
(* destruct args0. *)
(*   destruct expr0. *)
(*   rewrite (xx indexed args0) in H1. *)
(*   (* Case: st = prog0...nstep0 *) *)
(*   + destruct expr0 as [rname0 mp0 act0]. destruct (getName dt0) eqn:Heq1. *)
(*     destruct mp0. *)
(*     - simpl in H1. destruct args0. destruct act0. *)
(*       * rewrite H0 in H1. inversion H1. *)
(*       * destruct r. destruct l. simpl in H1. rewrite H0 in H1. inversion H1. rewrite <- H3. rewrite H9. reflexivity. *)
(*         destruct r0. destruct n0. simpl in H1.  *)
(*         simpl in H1. *)
  
Lemma FzeroTerminate : forall st rtn,
    F st = 0 -> interpr_step st = state_finished rtn.
  
Fixpoint interpr_step_main (n:nat) (st:State) : Rst :=
  match n with
  | 0 => unfinish
  | S n' => let rst := interpr_step st in
            match rst with
            | state _ _ _ _ _ _ => interpr_step_main n' rst
            | state_finished rtn => finished rtn
            end
  end.

Lemma interpreterTerminate : forall prog net data,
    noLoop prog = true -> hasAnchor prog = true ->
    exists i rval, interpr_main prog i net data = Some rval.
Proof.
  intros.
  exists (Nat.add 10 (exprLength prog)).
  (* unfold interpr_findMatchRule. *)
  induction prog as [|expr t].
  - simpl. exists noMatchingRule. reflexivity.
  -


(* Compute interpr_follow sampleProgram6 9 blogNet dataAdmin (getExpr sampleProgram6 (ruleName "admin")) []. *)

(* Compute isMatch (getName dataKey) [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "KEY");(mc_wild)]. *)

(* isMatch examples *)

(* this kind of definition of regular expression cut off the backtracking part of
   usuall regular expression. In another word, there is only one way that a string
   could be match.
   This result is very intuitive, since it only run a one-way pass alone the way, instead of
   doing a backtracking search that might have server cases. *)

(* todo *)
(* how to use map *)
(* write execution *)

(* write a dummy matching interface*)
