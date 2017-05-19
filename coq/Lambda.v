Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Ascii.
Require Import String.
Local Open Scope string_scope.

Inductive term : Type := 
  Var  : string -> term
| Free : string -> term
| Abs  : string -> term -> term 
| App  : term -> term -> term.

Definition a (x : string) : term := 
  match x with
  | EmptyString => Free x
  | String h t => 
     if andb (leb (Ascii.nat_of_ascii "A") (Ascii.nat_of_ascii h)) 
             (leb (Ascii.nat_of_ascii h) (Ascii.nat_of_ascii "Z")) 
        then Free x 
        else Var x
  end.

Notation "\ x , .. , z --> t" := (Abs x .. (Abs z t) .. ) (at level 38, no associativity).
Notation "m @ n"              := (App m n) (at level 39, left associativity).

Definition id    := \"x" --> a"x".
Definition apply := \"f", "x" --> (a"f" @ a"x").
Definition z     := \"f", "x" --> a"x".
Definition s     := \"n", "f", "x" --> (a"f" @ (a"n" @ a"f" @ a"x")).
Definition add   := \"n", "m", "f", "x" --> (a"m" @ a"f" @ (a"n" @ a"f" @ a"x")).
Definition mul   := \"n", "m", "f", "x" --> (a"m" @ (a"n" @ a"f") @ a"x").




