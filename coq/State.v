(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof.
    intros st x n m H1 H2. induction st. inversion H1.
      inversion H1. inversion H2; congruence.
                    inversion H2. congruence. apply IHst; assumption. 
  Qed.    

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof.
    intros st x n. unfold update. constructor.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof.
    intros st x2 x1 n m H1 H2. unfold update. apply st_binds_tl; auto.
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof.
    intros st x1 x2 n1 n2 m H. unfold update in *. set (id_eq_dec x2 x1). inversion_clear s.
      rewrite H0 in *. inversion H. constructor. unfold not in H6. exfalso. auto.
      inversion H. constructor. apply st_binds_tl. assumption. inversion H7. exfalso. auto. assumption.
  Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof.
    intros st x1 x2 n1 m H1 H2. unfold update. set (id_eq_dec x1 x2). inversion_clear s.
      rewrite H in *. apply (state_deterministic st x2 n1 m) in H1. rewrite H1. constructor. assumption.
        apply st_binds_tl. congruence. assumption.    
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros st x1 x2 x3 n1 n2 m H1 H2. unfold update in *.
    inversion H2. apply st_binds_tl. rewrite <-H5. congruence. apply st_binds_hd.
    inversion H7. apply st_binds_hd. apply st_binds_tl. assumption. 
      apply st_binds_tl; assumption.       
  Qed.  

End S.