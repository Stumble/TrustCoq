Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Strlib.
Require Import Notations Logic Datatypes.
Require Export Setoid.
Require Import LibTactics.
Require Import Coq.omega.Omega.

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

Inductive RuleParameter : Type :=
  | rp_indexed : nat -> RuleParameter
  | rp_prefixOfIndexed : nat -> nat -> RuleParameter.

Inductive RuleCall : Type :=
  | ruleCall : RuleName -> list RuleParameter -> RuleCall.

Inductive Action : Type :=
(* TryElse is temporarily removed, it introduces too much problems when proofing *)
(* | actTryElse       : RuleCall -> RuleCall -> Action *)
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

Inductive ExprMiddle : Type :=
| exprm : RuleName -> MatchPattern -> Action -> option nat -> ExprMiddle.

(* last nat is nToShrink *)
Inductive ExprLabeled : Type :=
  | exprl : RuleName -> MatchPattern -> Action -> nat -> ExprLabeled.

Definition Program := list Expr.

Definition ProgramMiddle := list ExprMiddle.

Definition ProgramLabeled := list ExprLabeled.

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
Definition empty_expr_middle: ExprMiddle := (exprm (ruleName "") []
                                               (actRc (ruleCall (ruleName "") []))
                                               None).

Definition empty_expr_labeled : ExprLabeled := (exprl (ruleName "") []
                                               (actRc (ruleCall (ruleName "") []))
                                               0).

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

Lemma hasPrefixHd : forall h t,
    hasPrefix (h::t) = true ->
    (exists x y, h = rp_prefixOfIndexed x y).
Proof.
  intros.
  unfold hasPrefix in H.
  destruct h.
  inversion H.
  exists n n0. eauto.
Qed.

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

Lemma getPrefixLt :
  forall nm n nm',
    (getPrefix nm n = Some nm') ->
    length nm' < length nm.
Proof.
Admitted.

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

Fixpoint getNinList (n:nat) {T:Type} (l:list T) : option T :=
  match n with
  | 0 => match l with
         | [] => None
         | h :: t => Some h
         end
  | S n' => match l with
            | [] => None
            | h :: t => getNinList n' t
            end
  end.

Check [].

Lemma getNinListEmptyList : forall n T (l:list T),
    (l = []) ->
    getNinList n l = None.
Proof.
  intros.
  rewrite H.
  unfold getNinList.
  destruct n. eauto. eauto.
Qed.

Fixpoint genArgs (indexed:list Name) (rp: list RuleParameter) : option (list Name) :=
  match rp with
  | [] => Some []
  | h::t => match h with
            | rp_indexed n =>
              match indexed with
              | [] => None
              | hdIndexed::tlIndexed =>
                match (genArgs tlIndexed t) with
                | None => None
                | Some rtn => Some (hdIndexed :: rtn)
                end
              end
            | rp_prefixOfIndexed n minusN =>
              match indexed with
              | [] => None
              | hdIndexed::tlIndexed =>
                match (getPrefix hdIndexed minusN) with
                | None => None
                | Some prefix => match (genArgs tlIndexed t) with
                                 | None => None
                                 | Some rtn => Some (prefix::rtn)
                                 end
                end
              end
            end
  end.

(* Fixpoint getExpr (prog:Program) (name:RuleName) : Expr := *)
(*   match prog with *)
(*   | [] => empty_expr *)
(*   | e::t => let '(expr (ruleName ename) _ _) := e in *)
(*             let '(ruleName rname) := name in *)
(*             if beq_string ename rname *)
(*             then e *)
(*             else getExpr t name *)
(*   end. *)

Fixpoint getExprM (prog:ProgramMiddle) (name:RuleName) : ExprMiddle :=
  match prog with
  | [] => empty_expr_middle
  | e::t => let '(exprm (ruleName ename) _ _ _) := e in
            let '(ruleName rname) := name in
            if beq_string ename rname
            then e
            else getExprM t name
  end.


Fixpoint getExpr (prog:ProgramLabeled) (name:RuleName) : ExprLabeled :=
  match prog with
  | [] => empty_expr_labeled
  | e::t => let '(exprl (ruleName ename) _ _ _) := e in
            let '(ruleName rname) := name in
            if beq_string ename rname
            then e
            else getExpr t name
  end.

(* Example getExprTest1 : getExpr sampleProgram5 (ruleName ".com") = (expr (ruleName ".com") [] (actAnchor "/usr/local/key1")). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

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

(* Fixpoint interpr_follow (progConst:Program) (n:nat) (net:Network) *)
(*          (data:Data) (expr:Expr) (args:list Name) := *)
(*   match n with *)
(*   | 0 => None *)
(*   | S n' => *)
(*     let interpr_follow_next := interpr_follow progConst n' net in *)
(*     let '(expr rname mp act) := expr in *)
(*     match isMatch (getName data) mp with *)
(*     | (false, _) => Some keyNotMatch *)
(*     | (true, indexed) => *)
(*       match (argTest indexed args) with *)
(*       | false => Some keyNotMatch *)
(*       | true => *)
(*         match act with *)
(*         | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with *)
(*                                           | None => Some noMorePrefix *)
(*                                           | Some nxtArgs => *)
(*                                             interpr_follow_next (getKey net data) (getExpr progConst nxtRn) nxtArgs *)
(*                                           end *)
(*         | actAnchor addr => if beq_string addr (nameToString (getKeyLocator data)) *)
(*                             then Some succ *)
(*                             else Some authFail *)
(*         | actOrAnchor pRule aRule => *)
(*           let '(ruleCall pRn pPl) := pRule in *)
(*           let '(ruleCall aRn aPl) := aRule in *)
(*           match (genArgs indexed pPl) with *)
(*           (* this mean no more prefix, directly handover this packet to anchor rule *) *)
(*           | None => *)
(*             (* (rtnDebugAny Data data) *) *)
(*             match (genArgs indexed aPl) with *)
(*             | None => None *)
(*             | Some aArgs => interpr_follow_next data (getExpr progConst aRn) aArgs *)
(*             end *)
(*           | Some pArgs => *)
(*             (* Some (rtnDebugAny Data data) *) *)
(*             interpr_follow_next (getKey net data) (getExpr progConst pRn) pArgs *)
(*           end *)
(*         end *)
(*       end *)
(*     end *)
(*   end. *)

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

(* Fixpoint interpr_main (prog:Program) (n:nat) *)
(*          (net:Network) (data:Data) : option Rtn := *)
(*   match interpr_findMatchRule prog data with *)
(*   | None => Some noMatchingRule *)
(*   | Some eMatched => interpr_follow prog n net data eMatched [] *)
(*   end. *)

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

(* Example interpreterTest1 : interpr_main sampleProgram6 10 blogNet dataArticle = Some succ. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* -------------------------------- example NDNS --------------------------- *)
(* This example includes use of TryElse rule, now it's temporarily removed *)

(* Example sampleProgramNdns := *)
(*   [(expr (ruleName "CacheResolver") *)
(*          [(mc_exact "NDNS-R");(mc_sequence_wild "")] *)
(*          (actTryElse (ruleCall (ruleName "Local") []) (ruleCall (ruleName "NDNS-data") [])) *)
(*    ); *)
(*      (expr (ruleName "NDNS-data") *)
(*            [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_wild);(mc_exact "NS");(mc_indexed (mc_sequence_wild ""))] *)
(*            (actRc (ruleCall (ruleName "NDNS-DSK") [(rp_indexed 1)])) *)
(*      ); *)

(*      (expr (ruleName "NDNS-DSK") *)
(*            [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_exact "DSK");(mc_indexed (mc_sequence_wild ""))] *)
(*            (actRc (ruleCall (ruleName "NDNS-KSK") [(rp_indexed 1)])) *)
(*      ); *)

(*      (expr (ruleName "NDNS-KSK") *)
(*            [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_exact "KSK");(mc_indexed (mc_sequence_wild ""))] *)
(*            (actOrAnchor (ruleCall (ruleName "NDNS-DKEY") [(rp_prefixOfIndexed 1 1)]) *)
(*                         (ruleCall (ruleName "NDNS-Root") [])) *)
(*      ); *)

(*      (expr (ruleName "NDNS-DKEY") *)
(*            [(mc_indexed (mc_sequence_wild "NDNS"));(mc_exact "NDNS");(mc_wild);(mc_exact "DKEY");(mc_indexed (mc_sequence_wild ""))] *)
(*            (actRc (ruleCall (ruleName "NDNS-DSK") [(rp_indexed 1)])) *)
(*      ); *)

(*      (expr (ruleName "Local") *)
(*            [(mc_exact "NDNS-R");(mc_sequence_wild "")] *)
(*            (actAnchor "/usr/local/ucla/key") *)
(*      ); *)

(*      (expr (ruleName "NDNS-Root") *)
(*            [(mc_exact "NDNS");(mc_sequence_wild "")] *)
(*            (actAnchor "/usr/local/dns/key") *)
(*      ) *)
(*   ]. *)

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

(* Example data0 := data ["com";"ucla";"NDNS";"www";"NS";"v1";"s1"] ["com";"ucla";"NDNS";"DSK";"CERT";"1"]. *)
(* Example data1 := data ["com";"ucla";"NDNS";"DSK";"CERT";"1"] ["com";"ucla";"NDNS";"KSK";"CERT";"1"]. *)
(* Example data2 := data ["com";"ucla";"NDNS";"KSK";"CERT";"1"] ["com";"NDNS";"ucla";"DKEY";"CERT";"1"]. *)
(* Example data3 := data ["com";"NDNS";"ucla";"DKEY";"CERT";"1"] ["com";"NDNS";"DSK";"CERT";"1"]. *)
(* Example data4 := data ["com";"NDNS";"DSK";"CERT";"1"] ["com";"NDNS";"KSK";"CERT";"1"]. *)
(* Example data5 := data ["com";"NDNS";"KSK";"CERT";"1"] ["NDNS";"com";"DKEY";"CERT";"1"]. *)
(* Example data6 := data ["NDNS";"com";"DKEY";"CERT";"1"] ["NDNS";"DSK";"CERT";"1"]. *)
(* Example data7 := data ["NDNS";"DSK";"CERT";"1"] ["NDNS";"KSK";"CERT";"1"]. *)
(* Example data8 := data ["NDNS";"KSK";"CERT";"1"] ["/usr/local/dns/key"]. *)
(* Example dataR := wraped_data ["NDNS-R";"com";"ucla";"NDNS";"www";"NS";"v1";"s1"] ["/usr/local/mit/key"] data0. *)
(* Example NdnsNet := [data0;data1;data2;data3;data4;data5;data6;data7;data8;dataR]. *)

(* Example interpreterTest2 : interpr_main sampleProgramNdns 100 NdnsNet dataR = Some succ. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* -----------------------end of example NDNS -------------------------------- *)

Fixpoint exprLength (prog:Program) : nat :=
  match prog with
  | [] => 0
  | h::t => S (exprLength t)
  end.

(* Inductive Action : Type := *)
(* (* TryElse is temporarily removed, it introduces too much problems when proofing *) *)
(* (* | actTryElse       : RuleCall -> RuleCall -> Action *) *)
(* (* try expr1, if authentication failed, unwrap data and try Rule *) *)
(* | actRc            : RuleCall -> Action *)
(* | actOrAnchor      : RuleCall -> RuleCall -> Action *)
(* | actAnchor        : string -> Action. *)

Definition exprInitLabel (expr:Expr) : ExprMiddle :=
  let '(expr rname mp act) := expr in
  (exprm rname mp act None).

Definition progInitLabel (prog:Program) : ProgramMiddle :=
  map exprInitLabel prog.

Fixpoint caculateExprLabel (prog:ProgramMiddle) (expr:ExprMiddle) : ExprMiddle :=
  let '(exprm rname mp act label) := expr in
  match act with
  | actRc (ruleCall nxtRn nxtPl) => if (hasPrefix nxtPl)
                                    then exprm rname mp act (Some 0)
                                    else let nxtExpr := (getExprM prog nxtRn) in
                                         let '(exprm _ _ _ nxtLabel) := nxtExpr in
                                         match nxtLabel with
                                         | None => exprm rname mp act None
                                         | Some n' => exprm rname mp act (Some (S n'))
                                         end
  | actAnchor addr => exprm rname mp act (Some 0)
  | actOrAnchor pRule aRule =>
    let '(ruleCall pRn pPl) := pRule in
    if (hasPrefix pPl)
    then exprm rname mp act (Some 0)
    else let nxtExpr := (getExprM prog pRn) in
         let '(exprm _ _ _ pLabel) := nxtExpr in
         match pLabel with
         | None => exprm rname mp act None
         | Some n' => exprm rname mp act (Some (S n'))
         end
  end.

Fixpoint iterativeLabel (n:nat) (prog:ProgramMiddle) : ProgramMiddle :=
  match n with
  | 0 => prog
  | S n' => let tmp := (map (caculateExprLabel prog) prog) in
            iterativeLabel n' tmp
  end.

Fixpoint ExprMiddle2Label (expr:ExprMiddle) : ExprLabeled :=
  let '(exprm rn mp act optNat) := expr in
  match optNat with
  | None => exprl rn mp act 0
  | Some x => exprl rn mp act x
  end.

Fixpoint progMiddle2Labled (prog:ProgramMiddle) : ProgramLabeled :=
  map ExprMiddle2Label prog.

Fixpoint labelProgram (prog:Program) : ProgramLabeled :=
  let n := List.length prog in
  let progInitMiddle := (progInitLabel prog) in
  let progFinalMidle := iterativeLabel n progInitMiddle in
  progMiddle2Labled progFinalMidle.

Compute (labelProgram sampleProgram6).

(* check program labels against specs *)
(* 1. expr with getPrefix in parameter: n2s = 0 *)
(* 2. expr anchor has: n2s = 0 *)
(* 3. expr without prefix nor anchor: n2s = (getExpr prog n)'s n + 1 *)

(* Must use function due to there are _ in matching,
   coq can't unfold match with _*)
Function checkExpr (prog:ProgramLabeled) (e:ExprLabeled) : bool :=
  let '(exprl _ _ act n2s) := e in
  (* match e with *)
  (* | (exprl _ _ act n2s) => *)
  match act with
  | actRc (ruleCall nxtRn nxtPl) =>
    if Nat.eqb n2s 0
    then (if hasPrefix nxtPl
          then true
          else false)
    else (let e' := getExpr prog nxtRn in
          let '(exprl _ _ _ n2s') := e' in
          Nat.ltb n2s' n2s
         )
  | actOrAnchor
      (ruleCall nxtRn1 nxtPl1)
      (ruleCall nxtRn2 nxtPl2) =>
    if Nat.eqb n2s 0
    then (if hasPrefix nxtPl1
          then (hasPrefix nxtPl2)
          else false)
    else (let e' := getExpr prog nxtRn1 in
          let '(exprl _ _ _ n2s') := e' in
          let e'' := getExpr prog nxtRn2 in
          let '(exprl _ _ _ n2s'') := e'' in
          if Nat.ltb n2s' n2s
          then (if Nat.ltb n2s'' n2s then true else false)
          else false
         )
  | actAnchor _ => Nat.eqb n2s 0
  end.

(* small trick: use eqb true is easier to say every expr is true *)
Fixpoint checkLabeledProgramExpr (prog:ProgramLabeled) : bool :=
  let temp := (map (checkExpr prog) prog) in
  fold_left eqb temp true.

Fixpoint checkProg (prog:ProgramLabeled) : bool :=
  if (Nat.leb (length prog) 0)
  then false
  else
    checkLabeledProgramExpr prog.

Definition getNPrefix (args:list Name) : nat :=
  match args with
  | [] => 0
  | h :: t => List.length h
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
| state : ProgramLabeled -> Data -> Network -> ExprLabeled -> (list Name)-> State
| state_finished : Rtn -> State.

Fixpoint checkState (st:State): bool :=
  match st with
  | state prog dt net e args =>
    checkProg prog
  | state_finished rtn => true
  end.

Lemma checkStateImplyCheckProg : forall st prog dt net e args,
    st = state prog dt net e args ->
    checkState st = true ->
    checkProg prog = true.
  intros.
  unfold checkState in H0.
  rewrite H in H0.
  eauto.
Qed.

Inductive Rst : Type :=
| unfinish
| finished : Rtn -> Rst.

Print Rst_ind.

Fixpoint interpr_step (st:State) : State :=
  match st with
  | state_finished r => state_finished r
  | state progConst dt net e args =>
    let '(exprl rname mp act nToShrink) := e in
    match isMatch (getName dt) mp with
    | (false, _) => state_finished keyNotMatch
    | (true, indexed) =>
      match (argTest indexed args) with
      | false => state_finished keyNotMatch
      | true =>
        match act with
        | actRc (ruleCall nxtRn nxtPl) => match (genArgs indexed nxtPl) with
                                          | None => state_finished noMorePrefix
                                          | Some nxtArgs => (state progConst (getKey net dt) net (getExpr progConst nxtRn) nxtArgs)
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
            | Some aArgs => state progConst dt net (getExpr progConst aRn) aArgs
            end
          | Some pArgs =>
            (* Some (rtnDebugAny Data data) *)
            state progConst (getKey net dt) net (getExpr progConst pRn) pArgs
          end
        end
      end
    end
  end.

Fixpoint interpr_multi_step (n:nat) (st:State) : State :=
  match n with
  | 0 => st
  | S n' => interpr_multi_step n' (interpr_step st)
  end.

Fixpoint F (st:State) : nat :=
  match st with
  | (state prog dt net (exprl _ _ _ n) args) =>
    (List.length prog) * (getNPrefix args) + n
  | state_finished _ => 0
  end.

Lemma progUntouchedAfterStep: forall st st' prog prog' dt dt' net net' e e' args args' rname mp act nToShrink indexed,
    (e = exprl rname mp act nToShrink) ->
    (isMatch (getName dt) mp = (true, indexed)) ->
    (argTest indexed args = true) ->
    (st = state prog dt net e args) -> (st' = state prog' dt' net' e' args')
                              -> (interpr_step st = st') -> prog = prog'.
  intros st st' prog prog' dt dt' net net' e e' args args' rname mp act nToShrink indexed.
  intros Hexpr HisMatch HargTest Hst Hst' Hstep.
  rewrite Hexpr in Hst.
  rewrite Hst in Hstep.
  unfold interpr_step in Hstep.
  rewrite HisMatch in Hstep.
  rewrite HargTest in Hstep.
  rewrite Hst' in Hstep.
  destruct act as [rc | rc1 rc2 | anchorStr ].
  + destruct rc as [nxtRn nxtPl].
    destruct (genArgs indexed nxtPl) eqn:Heq1.
    - inversion Hstep. eauto.
    - inversion Hstep.
  + destruct rc1 as [pRn pPl].
    destruct rc2 as [aRn aPl].
    destruct (genArgs indexed pPl) eqn:Heq1.
    - inversion Hstep. try eauto.
    - destruct (genArgs indexed aPl) eqn:Heq2.
      * inversion Hstep. try eauto.
      * inversion Hstep.
  + destruct (beq_string anchorStr (nameToString (getKeyLocator dt)));inversion Hstep.
Qed.

Fixpoint interpr_step_main (n:nat) (st:State) : Rst :=
  match n with
  | 0 => unfinish
  | S n' => let rst := interpr_step st in
            match rst with
            | state _ _ _ _ _ => interpr_step_main n' rst
            | state_finished rtn => finished rtn
            end
  end.

(* if st_cont => st', st' = finished \/ st'=cont && F st' < F st_cont. *)
(* | state : ProgramLabeled -> Data -> Network -> ExprLabeled -> (list Name)-> State *)
(* | state_finished : Rtn -> State. *)

(* Lemma *)
(* This one has a almost same proof above
   but only some conditions are changed so that it
   is easier to use. *)
Lemma step_prog_equal :
  forall st prog dt net e a st' p' d' n' e' a',
    st = state prog dt net e a ->
    st' = state p' d' n' e' a' ->
    interpr_step st = st' ->
    prog = p'.
Admitted.

Fixpoint hasPrefixRc (rc:RuleCall) : bool :=
  match rc with
  | ruleCall rn pl => hasPrefix pl
  end.

Lemma hasPrefixRcToPrefix :
  forall rc rn pl,
    (rc = ruleCall rn pl) ->
    (hasPrefixRc rc = true) -> (hasPrefix pl = true).
Proof.
  intros.
  unfold hasPrefixRc in H0.
  rewrite H in H0.
  eauto.
Qed.

Inductive hasPrefixOrAnchor :
  Action -> Prop :=
  | hpa_anchor : forall str act, act = actAnchor str -> hasPrefixOrAnchor act 
  | hpa_actRc : forall rc act, (hasPrefixRc rc = true) -> act = actRc rc -> hasPrefixOrAnchor act
  | hpa_actOrAnchor : forall rc1 rc2 act, (hasPrefixRc rc1 = true) -> (hasPrefixRc rc2 = true) -> act = actOrAnchor rc1 rc2 -> hasPrefixOrAnchor act.

Lemma checkStateImply :
  forall st prog dt net e args,
    checkState st = true ->
    st = state prog dt net e args ->
    (checkExpr prog e = true
     /\
    checkProg prog = true).
Admitted.

Lemma checkExprImply1 :
  forall e rn mp act n prog,
    e = exprl rn mp act n ->
    checkExpr prog e = true ->
    n = 0 ->
    hasPrefixOrAnchor act.
  intros e rn mp act n prog.
  intros He Hck Hn0.
  unfold checkExpr in Hck.
  rewrite He in Hck.
  destruct act eqn:Hact.
  + destruct r eqn:Heqr.
    rewrite Hn0 in Hck.
    simpl in Hck.
    destruct (hasPrefix l) eqn:HhasPrefix.
    - rewrite <- Hact.
      apply hpa_actRc in Hact. eauto.
      unfold hasPrefixRc. eauto.
    - inversion Hck.
  + destruct r eqn:Heqr.
    destruct r0 eqn:Heqr0.
    rewrite Hn0 in Hck.
    simpl in Hck.
    destruct (hasPrefix l) eqn:HhasPrefix.
    - rewrite <- Hact.
      apply hpa_actOrAnchor in Hact. eauto.
      eauto.
      unfold hasPrefixRc. eauto.
    - inversion Hck.
      + rewrite <- Hact.
        apply hpa_anchor in Hact.
        eauto.
Qed.

Lemma checkExprImplyRc :
  forall prog e rn mp act n nxtRn nxtPl,
    e = exprl rn mp act n ->
    n > 0 ->
    act = actRc (ruleCall nxtRn nxtPl) ->
    checkExpr prog e = true ->
    (forall e' rn' mp' act' n', e' = exprl rn' mp' act' n' ->
                                e' = (getExpr prog nxtRn) ->
                                n' < n).
  intros prog e rn mp act n nxtRn nxtPl.
  intros He Hnl0 Hact Hck.
  intros e' rn' mp' act' n'.
  intros He'.
  intros HeGet.
  rewrite He in Hck.
  unfold checkExpr in Hck.
  destruct act eqn:HeqAct.
  + destruct r eqn:HeqR.
    destruct n.
    inversion Hnl0.
    simpl in Hck.
    destruct (getExpr prog r0) eqn:HeqE'.
    inversion Hact.
    rewrite H0 in HeqE'.
    rewrite HeGet in He'.
    rewrite He' in HeqE'.
    inversion HeqE'.
    inversion Hck.
    apply Nat.ltb_lt in H6.
    omega.
  + inversion Hact.
  + inversion Hact.
Qed.
  

Lemma checkExprImplyOr :
  forall prog e rn mp act n nxtRn1 nxtPl1 nxtRn2 nxtPl2,
    e = exprl rn mp act n ->
    n > 0 ->
    act = actOrAnchor (ruleCall nxtRn1 nxtPl1)
                      (ruleCall nxtRn2 nxtPl2) ->
    checkExpr prog e = true ->
    (forall e' rn' mp' act' n',
          e' = exprl rn' mp' act' n' ->
          ((e' = (getExpr prog nxtRn1)) \/ e' = (getExpr prog nxtRn2)) ->
          n' < n).
  intros prog e rn mp act n nxtRn1 nxtPl1 nxtRn2 nxtPl2.
  intros He Hnlt0 Hact Hck.
  intros e' rn' mp' act' n'.
  intro He'.
  intros Hrst.
  rewrite Hact in He.
  rewrite He in Hck.
  unfold checkExpr in Hck.
  destruct n.
  inversion Hnlt0.
  simpl in Hck.
  destruct (getExpr prog nxtRn1) eqn:HG1.
  destruct (getExpr prog nxtRn2) eqn:HG2.
  destruct (n0 <? S n) eqn:HeqLt1.
  Focus 2. inversion Hck.
  inversion Hck.
  destruct (n1 <? S n) eqn:HeqLt2.
  Focus 2. inversion H0.
  destruct Hrst as [Hn0 | Hn1].
  +  rewrite Hn0 in He'.
     inversion He'.
     rewrite <- H4.
     apply Nat.ltb_lt in HeqLt1.
     eauto.
  +  rewrite Hn1 in He'.
     inversion He'.
     rewrite <- H4.
     apply Nat.ltb_lt in HeqLt2.
     eauto.
Qed.

Lemma labeled_prog_args_shrink_rc:
  forall st prog dt net e args rn mp act n nxtRn nxtPl,
    checkState st = true ->
    st = state prog dt net e args ->
    e = exprl rn mp act n ->
    act = actRc (ruleCall nxtRn nxtPl) ->
    ( (n = 0 /\ hasPrefixOrAnchor act)
      \/
      ((n > 0) /\ forall e' rn' mp' act' n', e' = exprl rn' mp' act' n' ->
                                 e' = (getExpr prog nxtRn) ->
                                 n' < n)
    ).
Proof.
  intros st prog dt net e args rn mp act n nxtRn nxtPl.
  intros Hck Hst He Hact.
  destruct n.
  + left. split. eauto.
    eapply checkStateImply in Hck.
    Focus 2. eauto.
    inversion Hck.
    eapply checkExprImply1 in H.
    Focus 2. eauto. Focus 2. eauto.
    eauto.
  + right.
    split.
    omega.
    intros e' rn' mp' act' n'.
    intros He'.
    intros HgetE'.
    eapply checkStateImply in Hck.
    Focus 2. eauto.
    inversion Hck.
    eapply checkExprImplyRc in H;
    repeat eauto.
    omega.
Qed.


Lemma labeled_prog_args_shrink_or:
  forall st prog dt net e args rn mp act n nxtRn1 nxtPl1 nxtRn2 nxtPl2,
    checkState st = true ->
    st = state prog dt net e args ->
    e = exprl rn mp act n ->
    act = actOrAnchor (ruleCall nxtRn1 nxtPl1)
                      (ruleCall nxtRn2 nxtPl2)->
    ( (n = 0 /\ hasPrefixOrAnchor act)
      \/
      (forall e' rn' mp' act' n',
          e' = exprl rn' mp' act' n' ->
          ((e' = (getExpr prog nxtRn1)) \/ e' = (getExpr prog nxtRn2)) ->
          n' < n)
    ).
Proof.
  intros st prog dt net e args rn mp act n nxtRn1 nxtPl1 nxtRn2 nxtPl2.
  intros Hck Hst He Hact.
  destruct n.
  + left. split. eauto.
    eapply checkStateImply in Hck.
    Focus 2. eauto.
    inversion Hck.
    eapply checkExprImply1 in H.
    Focus 2. eauto. Focus 2. eauto.
    eauto.
  + right.
    intros e' rn' mp' act' n'.
    intros He'.
    intros HgetE'.
    eapply checkStateImply in Hck.
    Focus 2. eauto.
    inversion Hck.
    eapply checkExprImplyOr in H;
    repeat eauto.
    omega.
Qed.

Lemma progLengthLt0 : forall st prog dt net e args,
    (checkProg prog = true) ->
    (st = state prog dt net e args) ->
    (length prog > 0).
Proof.
  intros st prog dt net e args.
  intros Hck Hst.
  unfold checkProg in Hck.
  remember (length prog) as pl.
  destruct prog.
  + simpl in Hck. inversion Hck.
  + destruct (length (e0 :: prog)) eqn:HeqIf.
    simpl in Hck. inversion Hck.
    rewrite Heqpl. omega.
Qed.

Lemma labelLtProgLength :
  forall st prog dt net e a rn mp act n2s,
    st = state prog dt net e a ->
    e = exprl rn mp act n2s ->
    n2s <= List.length prog.
Admitted.

Lemma argTest_le : forall indexed args,
    argTest indexed args = true ->
    getNPrefix indexed <= getNPrefix args.
Proof.
Admitted.

Lemma prefixZeroTerminate : forall st prog dt net e args,
    (st = state prog dt net e args) ->
    (getNPrefix args = 0) ->
    (* missing condition, expr's n2s = 0 *)
    exists rtn, interpr_step st = state_finished rtn.
Proof.
  intros st prog dt net e args.
  intros Hst Hp0.
  rewrite Hst.
  unfold interpr_step.

Admitted.

Lemma genArgs_lt_if_prefix : forall indexed nxtPl l,
    (genArgs indexed nxtPl = Some l) ->
    (hasPrefix nxtPl = true) ->
    (getNPrefix l < getNPrefix indexed).
Proof.
  intros.
  destruct indexed.
  + (* empty *)
    
    eauto.
    destruct nxtPl.
    unfold genArgs in H.
    inversion H0.
    unfold genArgs in H.
    destruct r eqn:Heqr.
    inversion H. inversion H.
  + destruct nxtPl.
    inversion H0.
    unfold genArgs in H.
    fold genArgs in H.
    destruct r eqn:Heqr.
    destruct (genArgs indexed nxtPl) eqn:Heqrtn.
    inversion H.
    unfold getNPrefix.
    apply hasPrefixHd in H0.
    (* destruct on exists *)
    destruct H0 as (x & y & Hgg).
    inversion Hgg.
    apply hasPrefixHd in H0.
    destruct H0 as (x & y & Hgg).
    inversion Hgg.
    destruct (getPrefix n n1) eqn:Hgetp.
    destruct (genArgs indexed nxtPl) eqn:HeqGen.
    inversion H.
    unfold getNPrefix.
    apply getPrefixLt with (n:=n1). eauto. 
    inversion H.
    inversion H.
Qed.

Lemma genArgs_le : forall indexed nxtPl l,
    (genArgs indexed nxtPl = Some l) ->
    (getNPrefix l <= getNPrefix indexed).
Proof.
  intros.
  destruct indexed.
  + (* indexed empty *)
    destruct nxtPl.
    unfold genArgs in H.
    inversion H.
    simpl. eauto.
    unfold genArgs in H.
    destruct r.
    inversion H. inversion H.
  +  destruct nxtPl.
     * unfold genArgs in H.
       inversion H. simpl. omega. 
     * unfold genArgs in H.
       destruct r.
       fold genArgs in H.
       - destruct (genArgs indexed nxtPl) eqn:Heq2.
         inversion H. unfold getNPrefix. omega.
         inversion H.
       - fold genArgs in H.
         destruct (getPrefix n n1) eqn:Hgp.
         destruct (genArgs indexed nxtPl) eqn:Heqg.
         inversion H.
         unfold getNPrefix.
         Check getPrefixLt.
         apply getPrefixLt in Hgp.
         omega.
         inversion H. inversion H.
Qed.

Lemma mathBasic_lelt : forall a b c,
    a < b ->
    b <= c ->
    a < c.
Proof.
  intros.
  omega.
Qed.

Lemma hasPrefixOrAnchor_on_nxtPl :
  forall nxtRn nxtPl,
    (hasPrefixOrAnchor (actRc (ruleCall nxtRn nxtPl))) ->
    hasPrefix nxtPl = true.
Proof.
  intros.
  inversion H.
  inversion H0.
  inversion H1.
  apply hasPrefixRcToPrefix with (rc:=rc) (rn:=nxtRn).
  eauto. eauto.
  inversion H2.
Qed.

Lemma hasPrefixOrAnchor_on_all_nxtPl :
  forall nxtRn1 nxtPl1 nxtRn2 nxtPl2,
    (hasPrefixOrAnchor (actOrAnchor (ruleCall nxtRn1 nxtPl1)
                                    (ruleCall nxtRn2 nxtPl2))) ->
    (hasPrefix nxtPl1 = true) /\ (hasPrefix nxtPl2 = true).
Proof.
  intros.
  rename H into Hhas.
  inversion Hhas.
  + inversion H.
  + inversion H0.
  + inversion H1.
    split.
    apply hasPrefixRcToPrefix with (rc:=rc1) (rn:=nxtRn1).
    eauto. eauto.
    apply hasPrefixRcToPrefix with (rc:=rc2) (rn:=nxtRn2).
    eauto. eauto.
Qed.

Lemma mathNatZero :
  forall a b,
    (a + b = 0) ->
    a = 0 /\ b = 0.
Proof.
  intros.
  omega.
Qed.

Lemma mathBasic1 :
  forall A B C D,
    (B < D) ->
    (C <= A) ->
    A * B + C <= A * D + 0 - 1.
  intros.
Admitted.

Lemma mathBasic2 :
  forall A B C D E,
    B <= D ->
    C < E ->
    A * B + C <= A * D + E - 1.
Admitted.

Lemma mathBasic3 :
  forall A B C,
    (A > 0) ->
    (A * B + C) = 0 ->
    (C = 0 /\ B = 0).
Proof.
  intros.
  split.
  induction C. eauto. 
  apply mathNatZero in H0.
  induction A. inversion H.
  apply IHA. inversion H.
Admitted.

Lemma step_args_smaller :
  forall st prog dt net e a st' p' d' n' e' a' rn mp act n2s
  rn' mp' act' n2s',
    checkState st = true ->
    st = state prog dt net e a ->
    st' = state p' d' n' e' a' ->
    e = exprl rn mp act n2s ->
    e' = exprl rn' mp' act' n2s' ->
    interpr_step st = st' ->
    ((n2s = 0 /\ (getNPrefix a' < getNPrefix a))
     \/
     (n2s' < n2s /\ (getNPrefix a' <= getNPrefix a))).
  intros
    st prog dt net e a st' p' d' n' e' a' rn mp act n2s
    rn' mp' act' n2s'.
  intros Hck Hst Hst' He He' Hstep.
  assert (Hshrink := Hst).
  (* apply labeled_prog_args_shrink_step with *)
  (*   (rn:=rn) (mp:=mp) (act:=act) (n:=n2s)in Hshrink. *)
  (* Focus 2. eauto. *)
  rewrite He in Hst.
  (* destruct e as [rn mp act n2s] eqn:Hexpr. *)
  rewrite Hst in Hstep.
  unfold interpr_step in Hstep.
  destruct (isMatch (getName dt) mp) as [b indexed] eqn:HisMatch.
  destruct b.
  
  + (* isMatch = true Case *)
    destruct (argTest indexed a) eqn:HargTest.
    - (* argTest true Case *)
      destruct act as [rc | rc1 rc2 | anchorStr ] eqn:HeqAct.
      * (* act = actRc rc Case*)
        destruct rc as [nxtRn nxtPl] eqn:HeqRc.
        apply labeled_prog_args_shrink_rc with
        (rn:=rn) (mp:=mp) (act:=act) (n:=n2s)
                 (nxtRn:=nxtRn) (nxtPl:=nxtPl) in Hshrink.
        (* solving trivial goals *)
        Focus 2. eauto.
        Focus 2. eauto. rewrite <- HeqAct in He. eauto.
        Focus 2. eauto.
        destruct (genArgs indexed nxtPl) eqn:HeqGenArgs.
        ++
          (* genArgs indexed nxtPl = (true, l) *)
        rewrite Hst' in Hstep.
        inversion Hshrink as [Hn2s0 | Hn2sS].
          -- left. inversion Hn2s0. split. eauto.
             apply argTest_le in HargTest. (* ! *)
             apply genArgs_lt_if_prefix in HeqGenArgs.
             inversion Hstep.
             rewrite H6 in HeqGenArgs.
             omega.
             rewrite HeqAct in H0.
             apply hasPrefixOrAnchor_on_nxtPl in H0.
             eauto.
          -- right. split.
             apply Hn2sS with
             (e':=e') (rn':=rn')
                      (mp':=mp') (act':=act').
             eauto. inversion Hstep. eauto. eauto.
             inversion Hstep.
             rewrite <- H4.
             apply argTest_le in HargTest.
             apply genArgs_le in HeqGenArgs.
             omega.
        ++ (* genArgs indexed nxtPl = None *)
          rewrite Hst' in Hstep.
          inversion Hstep.
      * (* act = act = actOrAnchor rc1 rc2*)
        destruct rc1 as [nxtRn1 nxtPl1] eqn:Heqrc1.
        destruct rc2 as [nxtRn2 nxtPl2] eqn:Heqrc2.
        apply labeled_prog_args_shrink_or with
        (rn:=rn) (mp:=mp) (act:=act) (n:=n2s)
                 (nxtRn1:=nxtRn1) (nxtPl1:=nxtPl1)
                 (nxtRn2:=nxtRn2) (nxtPl2:=nxtPl2)  in Hshrink;eauto.
        Focus 2. rewrite <- HeqAct in He. eauto.
        (* Focus 2. eauto. *)
        destruct (genArgs indexed nxtPl1) eqn:HeqGenArgs.
        ++ (* genArgs indexed nxtPl1 = (true, l) *)
          eauto.
          inversion Hshrink as [Hn2s0 | Hn2sS].
          -- left. inversion Hn2s0. split. eauto.
             apply argTest_le in HargTest. (* ! *)
             apply genArgs_lt_if_prefix in HeqGenArgs.
             rewrite Hst' in Hstep.
             inversion Hstep.
             rewrite H6 in HeqGenArgs.
             omega.
             rewrite HeqAct in H0.
             apply hasPrefixOrAnchor_on_all_nxtPl in H0.
             inversion H0.
             eauto.
          -- right.
             split.
             apply Hn2sS with
             (e':=e') (rn':=rn')
                      (mp':=mp') (act':=act').
             eauto. inversion Hstep. eauto. eauto.
             left.
             rewrite Hst' in Hstep.
             inversion Hstep.
             eauto.
             apply argTest_le in HargTest.
             apply genArgs_le in HeqGenArgs.
             rewrite Hst' in Hstep.
             inversion Hstep.
             rewrite <- H4.
             omega.
        ++ (* genArgs indexed nxtPl1 = (false, l) *)
          eauto.
          destruct (genArgs indexed nxtPl2) eqn:HeqGenArgs2.
          -- (* genArgs2 = some l*)
          rewrite Hst' in Hstep.
          inversion Hshrink as [Hn2s0 | Hn2sS].
            ** left. inversion Hn2s0. split. eauto.
             apply argTest_le in HargTest. (* ! *)
             apply genArgs_lt_if_prefix in HeqGenArgs2.
             inversion Hstep.
             rewrite <- H6.
             omega.
             rewrite HeqAct in H0.
             apply hasPrefixOrAnchor_on_all_nxtPl in H0.
             inversion H0.
             eauto.
            ** right.
               split.
               apply Hn2sS with
               (e':=e') (rn':=rn')
                        (mp':=mp') (act':=act').
               eauto. right. inversion Hstep. eauto. 
               apply argTest_le in HargTest.
               apply genArgs_le in HeqGenArgs2.
               inversion Hstep.
               rewrite <- H4.
               omega.
          -- (* genArgs2 None *)
            rewrite Hst' in Hstep. inversion Hstep.
      * rewrite Hst' in Hstep.
        destruct (beq_string anchorStr (nameToString (getKeyLocator dt))).
        ++ inversion Hstep.
        ++ inversion Hstep.
    - rewrite Hst' in Hstep.
      inversion Hstep.
  + (* isMatch false *)
    rewrite Hst' in Hstep.
    inversion Hstep.
Qed.

Lemma step_cont_le :
  forall st prog dt net e a st' p' d' n' e' a',
    checkState st = true ->
    st = state prog dt net e a ->
    st' = state p' d' n' e' a' ->
    interpr_step st = st' ->
    F st' <= F st - 1.
Proof.
  intros st prog dt net e a st' p' d' n' e' a'.
  intros Hck Hst Hst' Hstep.
  rewrite Hst.
  rewrite Hst'.
  unfold F.
  destruct e as [rn mp act n2s] eqn:HeqE.
  destruct e' as [rn' mp' act' n2s'] eqn:HeqE'.
  (* this rewrite earase the p' = prog *)
  asserts_rewrite (prog = p').
  apply step_prog_equal with
  (st:=st) (prog:=prog)
  (dt:=dt) (net:=net) (e:=e) (a:=a) (st':=st') (p':=p')
  (d':=d') (n':=n') (e':=e') (a':=a'). rewrite <- HeqE in Hst.
  jauto. rewrite <- HeqE' in Hst'. jauto. jauto.
  (* end of introducing p = p' *)
  remember (length p') as pl.
  (* the Main goal, others are trivial eauto cases *)
  assert (Hsmaller := Hstep).
  + eapply step_args_smaller with
    (st:=st) (prog:=prog) (dt:=dt)
             (net:=net) (e:=e) (a:=a) (rn:=rn)
             (mp:=mp) (act:=act) (n2s:=n2s) (rn':=rn')
             (mp':=mp') (act':=act') (n2s':=n2s') (p':=p')
             (d':=d') (n':=n') (e':=e') (a':=a')
      in Hsmaller.
    inversion Hsmaller as [HsOnPrefix | HsOnNat].
  (* HsOnPrefix *)
  - inversion HsOnPrefix as [Hn2s0 Hprefixlt].
    rewrite Hn2s0.
    apply mathBasic1. eauto. rewrite Heqpl.
    apply labelLtProgLength with
        (st:=st') (dt:=d')
             (net:=n') (e:=e') (a:=a') (rn:=rn')
             (mp:=mp') (act:=act').
    rewrite <- HeqE' in Hst'. eauto.
    eauto.
  - inversion HsOnNat.
    apply mathBasic2.
    eauto. eauto.
  - rewrite <- HeqE in Hst. eauto.
  - rewrite <- HeqE in Hst. eauto. 
  - rewrite <- HeqE' in Hst'. eauto.
  - eauto.
  - eauto.
Qed.

Lemma step_result : forall st prog dt net e args st',
    checkState st = true ->
    (st = state prog dt net e args) ->
    (interpr_step st = st') ->
    (
      (exists rtn, st' = state_finished rtn)
      \/
      (forall prog' dt' net' e' args', st' = (state prog' dt' net' e' args') -> F st' <= F st - 1)
    ).
Proof.
  intros st prog dt net e args st'.
  intros Hst.
  intros Hstep.
  destruct (interpr_step st) as [p' d' n' e' a' | r'] eqn:HeqRtn.
  + symmetry in Hstep. right. intros.
    apply step_cont_le with
    (prog:=prog) (dt:=dt) (net:=net) (e:=e) (a:=args)
    (p':=p') (d':=d') (n':=n') (e':=e') (a':=a').
    repeat eauto. rewrite <- Hstep in HeqRtn. eauto.
    eauto. rewrite H in HeqRtn. eauto.
  + left. eauto.
Qed.

Lemma FzeroTerminate : forall st,
    checkState st = true ->
    F st = 0 -> (exists rtn, interpr_step st = state_finished rtn).
  intros st Hck Hfst0.
  destruct st as [prog data net expr args | rt] eqn:HeqSt.
  +
    unfold F in Hfst0.
    destruct expr as [rn mp act] eqn:HeqExpr.
    apply mathBasic3 in Hfst0.
    Focus 2. apply progLengthLt0 with (st:=st)
    (dt:=data) (net:=net) (e:=expr) (args:=args).
    eapply checkStateImplyCheckProg.
    eauto. rewrite <- HeqSt in Hck. eauto. 
    rewrite <- HeqExpr in HeqSt. eauto.
    inversion Hfst0.
    rewrite <- HeqExpr in HeqSt.
    rewrite <- HeqExpr.
    rewrite <- HeqSt.
    apply prefixZeroTerminate with (st:=st) (prog:=prog)
             (dt:=data) (net:=net) (e:=expr) (args:=args).
    eauto. eauto.
  + simpl. eauto.
Qed.

(* Compute interpr_follow sampleProgram6 9 blogNet dataAdmin (getExpr sampleProgram6 (ruleName "admin")) []. *)

(* Compute isMatch (getName dataKey) [(mc_indexed (mc_sequence_wild "blog"));(mc_exact "blog");(mc_exact "KEY");(mc_wild)]. *)

(* isMatch examples *)

(* this kind of definition of regular expression cut off the backtracking part of
   usuall regular expression. In another word, there is only one way that a string
   could be match.
   This result is very intuitive, since it only run a one-way pass alone the way, instead of
   doing a backtracking search that might have server cases. *)