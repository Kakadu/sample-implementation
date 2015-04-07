(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', 
     id >> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Hint Constructors st_binds.
  
  Fixpoint update (st : state) (id : id) (a : A) : state := 
    match st with
    | [] => [(id, a)]
    | (id', a')::st' =>
      if eq_id_dec id' id 
      then (id, a)::st' 
      else if le_gt_id_dec id' id 
           then (id', a') :: update st' id a
           else (id, a) :: st
    end.

  Notation "st [ x <- y ]" := (update st x y) (at level 0).

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof.
    admit.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof.
    admit.
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m = st[x2 <- n2] / x1 => m.
  Proof.
    admit.
  Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof.
    admit.
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m = 
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    admit.
  Qed.  

End S.