(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Ltac prove_with th :=
  intros; 
  repeat (match goal with H: id |- _ => destruct H end); 
  match goal with n: nat, m: nat |- _ => set (th n m) end;
  repeat match goal with H: _ + {_} |- _ => inversion_clear H end;
  try match goal with H: {_} + {_} |- _ => inversion_clear H end;
  repeat
    match goal with 
      H: ?n <  ?m |-  _                + {Id ?n << Id ?m}  => right
    | H: ?n <  ?m |-  _                + {_}               => left
    | H: ?n >  ?m |-  _                + {Id ?n >> Id ?m}  => right
    | H: ?n >  ?m |-  _                + {_}               => left
    | H: ?n <  ?m |- {_}               + {Id ?n << Id ?m}  => right
    | H: ?n <  ?m |- {Id ?n << Id ?m}  + {_}               => left
    | H: ?n >  ?m |- {_}               + {Id ?n >> Id ?m}  => right
    | H: ?n >  ?m |- {Id ?n >> Id ?m}  + {_}               => left
    | H: ?n =  ?m |-  _                + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |-  _                + {_}               => left
    | H: ?n =  ?m |- {_}               + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |- {Id ?n =  Id ?m}  + {_}               => left
    | H: ?n <> ?m |-  _                + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |-  _                + {_}               => left
    | H: ?n <> ?m |- {_}               + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |- {Id ?n <> Id ?m}  + {_}               => left

    | H: ?n <= ?m |-  _                + {Id ?n <<= Id ?m} => right
    | H: ?n <= ?m |-  _                + {_}               => left
    | H: ?n <= ?m |- {_}               + {Id ?n <<= Id ?m} => right
    | H: ?n <= ?m |- {Id ?n <<= Id ?m} + {_}               => left
    end;
  try (constructor; assumption); congruence.

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof. prove_with lt_eq_lt_dec. Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. prove_with gt_eq_gt_dec. Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. prove_with le_gt_dec. Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros. set (eq_nat_is_eq n m). inversion i. set (eq_nat_decide n m). inversion s. 
    apply H in H1. left. assumption. right. auto.
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. prove_with eq_dec. Qed. 

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p. 
Proof.
  intros. destruct (id_eq_dec x x). reflexivity. exfalso; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q. 
Proof.
 intros. destruct (id_eq_dec x y). contradiction. reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
  id1 >> id2 -> id2 >> id1 -> False.
Proof.
  intros id1 id2 H1 H2. 
  inversion H1. inversion H2. 
  rewrite <-H5 in H3. rewrite <-H6 in H0. 
  inversion H3. inversion H0. omega.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
  id2 <<= id1 -> id2 >> id1 -> False.
Proof.
  intros id1 id2 H1 H2. 
  inversion H1. inversion H2. 
  rewrite <-H5 in H0. rewrite <-H6 in H3. 
  inversion H3. inversion H0. omega.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
  id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.
  intros id1 id2 H. remember (gt_eq_gt_id_dec id1 id2). inversion s. inversion H0. 
    apply (lt_gt_id_false id1 id2) in H1. contradiction. 
      inversion H1. inversion H. rewrite <- H3 in H6. rewrite <-H4 in H7. inversion H6. inversion H7. omega.
      left. assumption.
      right. assumption.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
  id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof.
  intros id1 id2 H. unfold not in H. remember (le_gt_id_dec id1 id2). 
    inversion s. apply le_lt_eq_id_dec in H0. inversion H0. contradiction. 
       right. assumption. left. assumption.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
  id1 = id2 -> id1 >> id2 -> False.
Proof.
  intros id1 id2 H1 H2. 
  inversion H2. rewrite <-H3 in H1. rewrite <-H0 in H1. inversion H1. omega.
Qed.

