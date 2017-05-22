Require Import String.
Local Open Scope string_scope.
Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Lambda.

Inductive term : Type :=
| Index : nat -> term
| Free  : string -> term
| App   : term -> term -> term
| Abs   : term -> term.

Inductive wfg : nat -> term -> Prop :=
| wfg_Free  : forall (s   : string) (l : nat), wfg l (Free s)
| wfg_App   : forall (m n : term  ) (l : nat), wfg l m -> wfg l n -> wfg l (App m n) 
| wfg_Abs   : forall (m   : term  ) (l : nat), wfg (l+1) m -> wfg l (Abs m) 
| wfg_Index : forall (m l : nat), m < l -> wfg l (Index m).

Hint Constructors wfg.

Lemma wfg_monotone: forall n m k, wfg m n -> k > m -> wfg k n.
Proof.
  intro. induction n; intros; inversion H; constructor. 
   omega. 
   apply IHn1 with m. auto. omega. apply IHn2 with m. auto. omega.
   apply IHn with (m+1); auto. omega.
Qed.

Definition wf : term -> Prop := wfg 0.

Fixpoint lookup s env := 
  match env with
  | []      => None
  | h :: tl => 
    if string_dec h s 
    then Some 0 
    else match lookup s tl with
         | None   => None
         | Some i => Some (i+1)
         end
  end.

Lemma lookup_length: 
  forall s env i, lookup s env = Some i -> i < length env.
Proof.
  intros s env.
  induction env; intros; simpl in H.
    inversion H.
    destruct (string_dec a s) eqn:D.
      inversion H. simpl. apply lt_0_Sn.
      destruct (lookup s env) eqn:D1; inversion H.
        rewrite plus_comm. simpl. apply lt_n_S. auto.
Qed.

Fixpoint import' t env := 
  match t with
  | Lambda.Free s   => Some (Free s)
  | Lambda.Abs  x m => 
      match import' m (x::env) with
      | None    => None
      | Some m' => Some (Abs m')
      end
  | Lambda.Var x => 
      match lookup x env with
      | Some n => Some (Index n)
      | None   => None
      end
  | Lambda.App m n => 
      match (import' m env, import' n env) with
      | (Some m', Some n') => Some (App m' n')
      | _                  => None
      end
  end.

Lemma import'_wf: 
  forall t t' env l, length env = l -> import' t env = Some t' -> wfg l t'.
Proof.
  intro.
  induction t; intros; simpl in H0.
    destruct (lookup s env) eqn:D; inversion H0.
      constructor. rewrite <-H. apply lookup_length with s. assumption.

    inversion H0. constructor.

    destruct (import' t (s :: env)) eqn:D; inversion H0. 
      constructor. 
      apply IHt with (s::env); auto.
        simpl. rewrite plus_comm. auto. 

    destruct (import' t1 env) eqn:D1.
    destruct (import' t2 env) eqn:D2; inversion H0.
    constructor. 
      apply IHt1 with env; auto. 
      apply IHt2 with env; auto.
    inversion H0.
Qed.

Definition import t := import' t [].

Lemma import_wf: 
  forall (t : Lambda.term) (t' : term), import t = Some t' -> wf t'.
Proof.
  intros. 
  unfold wf. 
  unfold import in H. 
  apply import'_wf with (t)([]); auto.
Qed.

Fixpoint lift l n := 
  match n with
  | Index i => if leb l i then Index (i+1) else n
  | App m n => App (lift l m) (lift l n)
  | Abs m   => Abs (lift (l+1) m)
  | _ => n
  end.

Reserved Notation "m [ x <- n ]" (at level 0).

Fixpoint subst (m : term) (i : nat) (n : term) :=
  match m with
  | Index i'  => if beq_nat i' i then n else m
  | App   p q => App (p [i <- n]) (q [i <- n])
  | Abs   p   => Abs (p [i+1 <- lift 0 n])
  | _         => m
  end
where "m [ x <- n ]" := (subst m x n).
    
Lemma lift_lemma_g: forall n k, wfg k n -> wfg (k+1) (lift k n).
Proof.
  intro. induction n; intros; inversion H; simpl.
    destruct (leb k n); constructor; omega.
    constructor.
    constructor; auto.
    constructor. auto.
Qed.
    
Lemma lift_lemma: forall n l, wfg l n -> wfg (l+1) (lift 0 n).
Proof. admit. 
(*
  intros.   
  rewrite plus_n_O with (n:=1). 
  rewrite (plus_comm 1). 
  apply lift_lemma_g.  
  assumption.  *)
Qed.

Hint Resolve lift_lemma.

Lemma subst_lemma: 
  forall m l i n, wfg l n -> wfg l m -> wfg l (m [i <- n]).
Proof.
  intro. induction m; intros; simpl; auto; inversion H0; auto.
    destruct (beq_nat n i) eqn:D; auto.
Qed.

Hint Resolve subst_lemma.

Lemma subst_wfg: 
  forall m l i n, i < l -> wfg l m -> wfg l n -> wfg l (m [i <- n]).
Proof.
  intro. 
  induction m; intros; simpl; auto; inversion H0; try constructor; auto.
    unfold subst. destruct (beq_nat n i) eqn:D; assumption. 
Qed.