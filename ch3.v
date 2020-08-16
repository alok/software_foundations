Require  Coq.Unicode.Utf8_core.
Inductive day: Type :=
  | mon: day
  | tue: day
  | wed: day
  | thu: day
  | fri: day
  | sat: day
  | sun: day.

Definition next_weekday (d: day): day :=
  match d with
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => mon
  | sat => mon
  | sun=> mon
  end.

Compute (next_weekday fri).
Compute (next_weekday (next_weekday sat)).

Example test_next_weekday:
  (next_weekday (next_weekday sat)) = tue.

Proof. cbn. reflexivity. Qed.

Inductive bool: Type:=
  |true:bool
  | false: bool.

Definition neg b : bool :=
  match b with
  |true  => false
  |false => true
  end.

Compute (neg true).

Definition and (b b_: bool)  : bool :=
  match b with
  |true => b_
  |false => false
  end.

Definition or (b b': bool)  : bool:=
  match b with
  |true => true
  |false => b'
  end.

Example test_or_tf: (or true false) = true.
Proof. cbn. reflexivity.  Qed.

(* order matters  *)
Example test_orb2: (or false false) = false.
Proof. cbn. reflexivity. Qed.
Example test_orb3: (or false true) = true.
Proof. cbn. reflexivity. Qed.
Example test_orb4: (or true true) = true.
Proof. cbn. reflexivity. Qed.

Infix "&&" := and.
Infix "||" := or.

Example test_orb5: false || false || true = true.
Proof. cbn. reflexivity. Qed.

Definition nand (b b':bool)  : bool :=
  match (b,b') with
  |(true,true) => false
  |(false,false) => true
  |(true,false) => true
  |(false,true) => true
  end.

Infix "^" := nand.

Example test_nand1: (nand true false) = true.
Proof. tauto. Qed.
Example test_nand2: (nand false false) = true.
Proof. tauto. Qed.
Example test_nand3: (nand false true) = true.
Proof. tauto. Qed.
Example test_nand4: (nand true true) = false.
Proof. tauto. Qed.

Definition and3 (b b' b'':bool)  : bool :=
  match (b,b',b'') with
  | (false, _, _) => false
  | (_, false, _) => false
  | (_, _, false) => false
  | (true, true, true) => true
  end.

Example test_and31: (and3 true true true) = true.
Proof. tauto. Qed.
Example test_and32: (and3 false true true) = false.
Proof. tauto. Qed.
Example test_and33: (and3 true false true) = false.
Proof. tauto. Qed.
Example test_and34: (and3 true true false) = false.
Proof. tauto. Qed.

Inductive rgb: Type:=
  | red
  | green
  | blue.

Inductive  color: Type:=
  | white
  | black
  | primary (p: rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | primary q  =>  false
  | _ => true
  end.

Inductive bit: Type:=
  |B0
  |B1.

Inductive nybble: Type:=
  |bits (b0 b1 b2 b3: bit).

Check (bits B1 B1 B1 B1).

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Module Nat.

Inductive nat: Type:=
  |O
  |S (n : nat).

Compute (S (S O)).

Definition succ (n:nat):nat:=
  S n.
Definition pred (n:nat):nat:=
  match n with
  | O => O (*not true, but i guess totality is an issue*)
  | S n  => n
  end.

Compute (succ O).

Check (S O).
Check (S (S (S (S O)))).


Fixpoint is_odd (n: nat): bool:=
  match n with
  | O  => false
  | S O => true
  | S (S n') => is_odd n'
  end.

Definition is_even (n:nat):bool  := neg ( is_odd n).


Fixpoint plus (a b :nat):nat:=
  match (a,b) with
  | (O,_) => b
  | (_,O) => a
  | (S n, S m) => S ( S (plus n m)) (*this is where the `Fixpoint` comes in. Typing `Definition fails. *)
  end.
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O  =>  O
    | S n'  =>  plus m (mult n' m)
  end.

Fixpoint factorial (n:nat):nat:=
  match n with
  |O => S O
  | S p  => mult n (factorial p)
  end.


(* Notation "f | g" := (compose f g). *)
(* Definition compose (f g x):= f(g(x)). *)

Example test_factorial1: (factorial (S(S(S(O))))) =  S(S( S( S( S (S O))))).
Proof. tauto. Qed.


End Nat.

Theorem plus_example:forall n m: nat,
  n= m -> n+n=m+m.

Proof.
  intros n m.
  intros H.
(* the direction of the arrow is which side to apply the rewrite rule to. in
* this case doesn't matter. *)
  rewrite -> H.
  tauto.
  Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m  ->  m = o  ->  n + m = m + o.

(* Proof. *)
(*   intros n m o. *)
(*   intros H. *)
(*   rewrite -> H. *)
(*   intros H'. *)
(*   rewrite <- H'. *)
(*   tauto. *)
(* Qed. *)

Proof.
  intros n m o.
  intros H.
  intros H'.
  replace o with m.
  rewrite <- H.
  trivial.
Qed.

(* Make this a bit easier. *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' '[ ' ∀ x .. y ']' , '/' P ']'") : type_scope.

Theorem mult_S_1 : forall n m : nat,
  m = S n  -> m * (1 + n) = m * m.
Proof.
  intros m n.
  intros H.
  rewrite  -> H.
  reflexivity.
Qed.





Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O =>  match m with
         | O  =>  true
         | S m'  =>  false
         end
  | S n'  =>  match m with
            | O  =>  false
            | S m'  =>  eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O  =>  true
  | S n'  =>
      match m with
      | O  =>  false
      | S m'  =>  leb n' m'
      end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1) =? 0 = false.

Proof.
  intros n. destruct n as [|n'] eqn:E.
  - simpl. reflexivity.
  - reflexivity.
Qed.

Theorem neg_inversion: forall b: bool, neg (neg b) = b.
Proof.
  destruct b.
  - trivial.
  - trivial.
Qed.

Theorem plus_O_n' : ∀n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem false_annihilates: forall a :bool, false && a = a && false.
Proof.
  intros a.
  destruct a.
  - trivial.
  - trivial.
Qed.


Theorem and_commutative: forall a b: bool, a && b = b && a.
Proof.
  intros n m.  destruct n.
  - destruct m.
    + reflexivity.
    + reflexivity.
  - rewrite -> false_annihilates.
    reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat  ->  natlist  ->  natlist.

Notation "x :: l" := (cons x l)
(at level 60, right associativity).
Notation "[ ]" := nil.
(* Notation "[]" := nil. *)

(* Notation "[ x ; .. ; y]" := (cons x .. (cons y [])..). *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
