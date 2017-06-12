Require Import List.
Import ListNotations.
Require Import Omega.

Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf), c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                     [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                     (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
                     [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
                     c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                     [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                     [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
                     [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                        (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
                     [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big step equivalence *)
Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

(* Loops with equivalent bodies are equivalent *)
Lemma while_eq: forall (e : expr) (s1 s2 : stmt), s1 ~~~ s2 -> WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  intros. inversion_clear H. constructor. intros. split; (
    intro; 
      match goal with 
        _: _ == WHILE ?e DO ?s END ==> _ |- _ => remember (WHILE e DO s END) as While 
      end;
      induction H; try (inversion HeqWhile; subst e0; subst s); [
        apply bs_While_True with c'; [ assumption | apply H0; assumption | apply IHbs_int2; reflexivity]
      | apply bs_While_False; assumption]).
Qed.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence: forall (e : expr) (s s1 s2 : stmt), s1 ~~~ s2 ->
                       ((s  ;; s1) ~~~ (s  ;; s2)) /\
                       ((s1 ;; s ) ~~~ (s2 ;; s )) /\
                       (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
                       (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
                       (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  intros. inversion_clear H.
    split. constructor. intros. split; (intro; inversion H; apply bs_Seq with c'0; try apply H0; assumption).
    split. constructor. intros. split; (intro; inversion H; apply bs_Seq with c'0; try apply H0; assumption).
    split. constructor. intros. split; (
      intro; inversion H; solve [ apply bs_If_True ; solve [assumption | apply H0; assumption]
                                | apply bs_If_False; solve [assumption | apply H0; assumption]
                                ]).
    split. constructor. intros. split; (
      intro; inversion H; solve [ apply bs_If_True ; solve [assumption | apply H0; assumption]
                                | apply bs_If_False; solve [assumption | apply H0; assumption]
                                ]).
    apply bs_eq_intro in H0. apply while_eq. assumption.      
Qed.

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

(* Associativity of sequential composition *)
Lemma seq_assoc : forall (s1 s2 s3 : stmt), 
                      ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
Proof.
  intros s1 s2 s3. constructor. intros c0 c'0. split;
    intro H; repeat seq_inversion; seq_apply.
Qed.

(* One-step unfolding *)
Lemma while_unfolds : forall (e : expr) (s : stmt),
                        (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
Proof.
  intros e s. constructor. intros c0 c'0. split.
    intro H. inversion_clear H; [ 
      constructor; [
        assumption 
      | apply bs_Seq with (c':=c'); assumption
      ]
      | apply bs_If_False; [ assumption | constructor]
    ].
    intro H. inversion_clear H; [ 
      inversion_clear H1; apply bs_While_True with (c':=c'); assumption
    | destruct c'0; destruct p; inversion H1; apply bs_While_False; subst s0; assumption
    ].
Qed.      

(* Terminating loop invariant *)
Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                      c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
Proof.
  intros. remember (st, i, o). remember (WHILE e DO s END). induction H; solve [
    inversion Heqs0
  | inversion Heqs0; subst e0; subst s0; apply IHbs_int2; [assumption | reflexivity]
  | inversion Heqs0; subst e0; inversion Heqp; subst st0; assumption
  ].
Qed.

(* Big-step semantics does not distinguish non-termination from stuckness *)
Lemma loop_eq_undefined : (WHILE (Nat 1) DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
Proof.    
  apply bs_eq_intro. 
  intros c c'. 
  split.
    intro H. destruct c' eqn:C. destruct p eqn:P. 
      apply (while_false (Nat 1) SKIP s l0 l c) in H. inversion H.
    intro H. inversion H; inversion H5.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_bs_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (bs_eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof. 
  intros c c1 c2 s H. revert c2. induction H.
    intros c2 H1. inversion H1. reflexivity.
    intros c2 H1. inversion H1. by_bs_eval_deterministic.
    intros c2 H1. inversion H1. reflexivity.
    intros c2 H1. inversion H1. by_bs_eval_deterministic.
    intros c2 H1. inversion H1. apply IHbs_int1 in H4. subst c'0. apply IHbs_int2 in H7. assumption.
    intros c2 H1. inversion H1. apply IHbs_int in H10. assumption. apply bs_eval_deterministic with (z1 := Z.zero) in H. inversion H. assumption.
    intros c2 H1. inversion H1. apply bs_eval_deterministic with (z1 := Z.one) in H. inversion H. assumption.
      apply IHbs_int in H10. assumption.
    intros c2 H2. inversion H2. apply IHbs_int1 in H10. subst c'0. apply IHbs_int2 in H11. assumption.
      apply bs_eval_deterministic with (z2 := Z.one) in H9. inversion H9. assumption.
    intros c2 H1. inversion H1. apply bs_eval_deterministic with (z1 := Z.one) in H. inversion H. assumption.
      reflexivity.
Qed.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
                (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

(* Contextual equivalence is equivalent to the semantic one *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.
    
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  intros. split.
    intro H. constructor. intro. induction C; solve [ 
      unfold plug; assumption
    | simpl; by_eq_congruence (Nat 0) s (C <~ s1) (C <~ s2) IHC
    | simpl; by_eq_congruence e s (C <~ s1) (C <~ s2) IHC
    | simpl; apply while_eq; assumption
    ].
    intro H. inversion H. remember (H0 Hole) as C. unfold plug in C. assumption.
Qed.

(* CPS semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont), 
                      KEmpty |- c -- k --> c' -> 
                      k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (e : expr) (n : Z),
                      [| e |] s => n ->
                      KEmpty |- (s [x <- n], i, o) -- k --> c' ->
                      k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (z : Z),
                      KEmpty |- (s [x <- z], i, o) -- k --> c' ->
                      k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (z : Z),
                      [| e |] s => z ->
                      KEmpty |- (s, i, z::o) -- k --> c' ->
                      k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt), 
                      !s2 @ k |- c -- !s1 --> c' ->
                      k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.one ->
                      k |- (s, i, o) -- !s1 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.zero ->
                      k |- (s, i, o) -- !s2 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.one ->
                      !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.zero ->
                      KEmpty |- (st, i, o) -- k --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

    
Lemma cps_bs_gen: forall (S : stmt) (c c' : conf) (S1 k : cont),
                k |- c -- S1 --> c' -> !S = S1 @ k -> c == S ==> c'.
Proof.
  intros. generalize dependent S. 
  induction H. 
    intros. inversion H0.
    intros. 
      destruct k eqn:K. 
        unfold Kapp in *. inversion H. inversion H0. constructor.
        unfold Kapp in *. inversion H0. apply bs_Seq with c. constructor. apply IHcps_int. reflexivity.
    intros.
      destruct k eqn:K.
        unfold Kapp in *. inversion H1. inversion H0. apply bs_Assign. assumption.
        unfold Kapp in *. inversion H1. apply bs_Seq with (s[x<-n], i, o). apply bs_Assign. assumption.
          apply IHcps_int. reflexivity.    
    intros.
      destruct k eqn:K.
        unfold Kapp in *. inversion H0. inversion H. constructor.
        unfold Kapp in *. inversion H0. apply bs_Seq with (s[x<-z], i, o). constructor.
          apply IHcps_int. reflexivity.
    intros.
      destruct k eqn:K.
        unfold Kapp in *. inversion H1. inversion H0. constructor. assumption.
        unfold Kapp in *. inversion H1. apply bs_Seq with (s, i, z::o). constructor. assumption.
          apply IHcps_int. reflexivity.
    intros. 
      destruct k eqn:K. 
        unfold Kapp in *. inversion H0. apply IHcps_int. reflexivity. 
        unfold Kapp in *. inversion H0. remember (seq_assoc s1 s2 s) as Hassoc.
          inversion Hassoc. apply H1. apply IHcps_int. reflexivity.
    intros. 
      destruct k eqn:K. 
        unfold Kapp in *. inversion H1. apply bs_If_True. assumption.
          apply IHcps_int. reflexivity.
        unfold Kapp in *. inversion H1. 
          assert (A: forall (s : state Z) (i o : list Z) (e : expr) (s1 s2 s0 : stmt),
                      [| e |] s => Z.one -> (s, i, o) == s1;;s0 ==> c' -> (s, i, o) == (COND e THEN s1 ELSE s2 END);; s0 ==> c').
            intros. inversion H4. apply bs_Seq with c'0. apply bs_If_True; assumption. assumption.
          apply A. assumption. apply IHcps_int. reflexivity.
    intros. 
      destruct k eqn:K. unfold Kapp in *. inversion H1. apply bs_If_False. assumption.
        apply IHcps_int. reflexivity.
        unfold Kapp in *. inversion H1. 
          assert (A: forall (s : state Z) (i o : list Z) (e : expr) (s1 s2 s0 : stmt),
                      [| e |] s => Z.zero -> (s, i, o) == s2;;s0 ==> c' -> (s, i, o) == (COND e THEN s1 ELSE s2 END);; s0 ==> c').
            intros. inversion H4. apply bs_Seq with c'0. apply bs_If_False; assumption. assumption.
          apply A. assumption. apply IHcps_int. reflexivity.
    intros. 
      destruct k eqn:K. 
        unfold Kapp in *. inversion H1. remember (while_unfolds e s) as Hunfold.
          inversion Hunfold. apply H2. apply bs_If_True. assumption. apply IHcps_int. reflexivity.
        unfold Kapp in *. inversion H1. 
          assert (A: forall (e : expr) (s s0 : stmt) (st : state Z) (i o : list Z) (c' : conf),
                       [| e |] st => Z.one ->
                       (st, i, o) == s;; WHILE e DO s END;; s0 ==> c' ->
                       (st, i, o) == (WHILE e DO s END);; s0 ==> c').
            intros. inversion H4. inversion H10. apply bs_Seq with c'2. apply bs_While_True with c'1.
              assumption. assumption. assumption. assumption. 
          apply A. assumption. apply IHcps_int. reflexivity.
    intros. 
      destruct k eqn:K. 
        unfold Kapp in *. inversion H1. inversion H0. apply bs_While_False. assumption.
        unfold Kapp in *. inversion H1. 
          assert (A: forall (e : expr) (s s0 : stmt) (st : state Z) (i o : list Z) (c' : conf),
                       [| e |] st => Z.zero ->
                       (st, i, o) == s0 ==> c' ->
                       (st, i, o) == WHILE e DO s END;; s0 ==> c').
            intros. apply bs_Seq with (st0, i0, o0). apply bs_While_False. assumption. assumption.
          apply A. assumption. apply IHcps_int. reflexivity.
Qed.

Lemma cps_bs: forall (s1 s2 : stmt) (c c' : conf), !s2 |- c -- !s1 --> c' -> c == s1;; s2 ==> c'.
Proof.
  intros. remember (s1;;s2) as S. apply cps_bs_gen with (S1:=!s1) (k:=!s2). assumption. 
    unfold Kapp. rewrite HeqS. reflexivity.
Qed.

Lemma cps_int_to_bs_int_gen: forall (c c' : conf) (s : stmt) (K S : cont),
  K |- c -- S --> c' -> S = !(s) -> K = KEmpty -> c == s ==> c'.
Proof. 
  intros. generalize dependent s. 
  induction H. 
    intros. inversion H0.
    intros. inversion H0. rewrite H1 in H. inversion H. constructor.
    intros. inversion H2. rewrite H1 in H0. inversion H0. constructor. assumption.
    intros. inversion H0. rewrite H1 in H. inversion H. constructor.
    intros. inversion H2. rewrite H1 in H0. inversion H0. constructor. assumption.
    intros. inversion H0. rewrite H1 in *. unfold Kapp in *. apply cps_bs. assumption.
    intros. inversion H2. apply bs_If_True. assumption. rewrite H1 in *. apply IHcps_int; reflexivity.
    intros. inversion H2. apply bs_If_False. assumption. rewrite H1 in *. apply IHcps_int; reflexivity.
    intros. inversion H2. rewrite H1 in *. unfold Kapp in *. apply cps_bs in H0.
      inversion H0. apply bs_While_True with c'0; assumption.
    intros. inversion H2. rewrite H1 in H0. inversion H0. apply bs_While_False; assumption.
Qed.

Lemma cps_int_to_bs_int: forall (c c' : conf) (s : stmt),
                           KEmpty |- c -- !s --> c' -> c == s ==> c'.
Proof. 
  intros. apply cps_int_to_bs_int_gen with (K:=KEmpty) (S:=!s); auto.
Qed.

Lemma cps_seq_gen: forall (E k S1 : cont) (s1 s2 : stmt) (c c' c'' : conf),
                 k |- c -- S1 --> c' -> S1 = !s1 -> KEmpty |- c' -- !s2 --> c'' -> k @ !s2 |- c -- S1 --> c''.
Proof. admit.
Qed.

Lemma cps_seq: forall (k : cont) (s1 s2 : stmt) (c c' c'' : conf),
                 k |- c -- !s1 --> c' -> KEmpty |- c' -- !s2 --> c'' -> k @ !s2 |- c -- !s1 --> c''.
Proof.
  intros. remember !s1 as S1. apply cps_seq_gen with (s1:=s1)(c':=c'); assumption.
Qed.

Lemma bs_int_to_cps_int: forall (c c' : conf) (s : stmt),
  c == s ==> c' -> KEmpty |- c -- !s --> c'.
Proof.
  assert (A: forall (s : stmt), !s = KEmpty @ !s). unfold Kapp. auto.
  intros. induction H. 
    constructor.
    constructor.
    apply cps_Assign with z. assumption. constructor.
    admit. 
    admit. 
    constructor. unfold Kapp. 
      rewrite (A s2). apply cps_seq with c'; assumption.
    apply cps_If_True; assumption.
    apply cps_If_False; assumption.
    apply cps_While_True. assumption. unfold Kapp.
      rewrite (A (WHILE e DO s END)). apply cps_seq with c'; assumption.
    apply cps_While_False. assumption. constructor.
Qed.

    

  