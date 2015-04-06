(** Borrowed from Pierce's "Software Foundations" *)

Require Export Arith Arith.EqNat.

Inductive id : Type :=
  Id : nat -> id.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros id1 id2.
  destruct id1 as [n1]. destruct id2 as [n2].
  destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
    left. rewrite Heq. reflexivity.
    right. intros contra. inversion contra. auto. 
Qed. 

Lemma eq_id : forall (T:Type) x (p q:T), 
              (if eq_id_dec x x then p else q) = p. 
Proof.
  intros. 
  destruct (eq_id_dec x x). 
    reflexivity.
    exfalso; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> 
               (if eq_id_dec x y then p else q) = q. 
Proof.
 intros.
 destruct (eq_id_dec x y). contradiction. reflexivity.
Qed.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Hint Constructors le_id gt_id.

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof.
  intros id1 id2. destruct id1 as [n1]. destruct id2 as [n2].
  destruct (le_gt_dec n1 n2). left. auto. right. auto.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
  id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof.
  intros id1 id2 H. destruct id1 as [n1]. destruct id2 as [n2].
  assert (A: n1 <= n2). inversion H. assumption.
  destruct (le_lt_eq_dec n1 n2). assumption. right. auto. left. auto.
Qed.
  



