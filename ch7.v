
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat  ->  natlist  ->  natlist.

Notation "x :: l" := (cons x l)
(at level 60, right associativity).
Notation "[ ]" := nil.
(* Notation "[]" := nil. *)

(* Notation "[ x ; .. ; y]" := (cons x .. (cons y [])..). *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
(* Inductive natlist : Type := *)
(*   | nil : natlist *)
(*   | cons : nat  ->  natlist  ->  natlist. *)
(*  *)
(* Notation "x :: l" := (cons x l) *)
(* (at level 60, right associativity). *)
(* Notation "[ ]" := nil. *)
(* (* Notation "[]" := nil. *) *)
(*  *)
(* Notation "[x ; .. ; y]" := (cons x .. (cons y [])..). *)
Theorem silly2 : forall (n m o p : nat),
  n = m  ->
  (forall (q r : nat), q = r  -> 
  [ q;o ] = [r;p])  ->
  [n;o] = [m;p].
Proof.
  intros n m. intros o p. intros eq1. intros eq2.
  apply eq2. apply eq1. Qed.


Fixpoint odd o:=
  match o with
  | 0 => false
  | 1 => true
  | S (S n)   =>  odd n
  end.
Fixpoint even e:=
  match e with
  | 0 => true
  | 1 => false
  | S(S e)   =>  even e
  end.

Theorem silly_ex :
  (forall n, even n = true  ->  odd (S n) = true)  -> 
  odd 3 = true  -> 
     even 4 = true.
Proof.
  intros eq1 eq2 eq3. 
