(** Borrowed from Pierce's "Software Foundations" *)
Require Export Bool List.
Export ListNotations.
Require Export Arith Arith.EqNat.
Require Export Id.

Definition state (A : Set) := list (id * A).

Definition empty_state {A : Set} : state A := [].

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

(** For proofs involving states, we'll need several simple properties
    of [update]. *)

(** **** Exercise: 1 star (update_eq) *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  intros. unfold update. apply eq_id.
Qed.

(** **** Exercise: 1 star (update_neq) *)
Theorem update_neq : forall x2 x1 n st,
  x2 <> x1 ->                        
  (update st x2 n) x1 = (st x1).
Proof.
  intros. unfold update. apply neq_id. assumption.
Qed.

(** **** Exercise: 1 star (update_example) *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros. unfold update. simpl. unfold empty_state. reflexivity.
Qed.

(** **** Exercise: 1 star (update_shadow) *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros. unfold update. destruct (eq_id_dec x2 x1) eqn:D.
    reflexivity.
    reflexivity.
Qed.

(** **** Exercise: 2 stars (update_same) *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2). rewrite <- e. symmetry. assumption.
  reflexivity.
Qed.

(** **** Exercise: 3 stars (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  x2 <> x1 -> 
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros. unfold update. 
  destruct (eq_id_dec x1 x3) eqn: D1. rewrite e in H. 
    destruct (eq_id_dec x2 x3) eqn: D2. contradiction. reflexivity.
    reflexivity.
Qed.  

