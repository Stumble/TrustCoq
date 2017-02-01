
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition beq_char (a:ascii) (b:ascii) : bool :=
  beq_nat (nat_of_ascii a) (nat_of_ascii b).

Fixpoint beq_string (str1:string) (str2:string) : bool :=
  match str1,str2 with
  | String h1 t1, String h2 t2 => if beq_char h1 h2 then beq_string t1 t2 else false
  | EmptyString, EmptyString => true
  | _, _ => false
  end.

Example beg_string_test1 : (beq_string "123123" "123123") = true.
Proof.
  simpl. reflexivity.
Qed.

Example beg_string_test2 : (beq_string "123123" "abcabc") = false.
Proof.
  simpl. reflexivity.
Qed.
 
