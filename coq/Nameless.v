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
    destruct (import' t2 env) eqn:D2;
    inversion H0.
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
    
  
