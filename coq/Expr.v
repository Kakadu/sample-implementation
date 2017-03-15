Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
  | Nat : nat  -> expr
  | Var : id   -> expr              
  | Add : expr -> expr -> expr
  | Sub : expr -> expr -> expr
  | Mul : expr -> expr -> expr
  | Div : expr -> expr -> expr
  | Mod : expr -> expr -> expr
  | Le  : expr -> expr -> expr
  | Lt  : expr -> expr -> expr
  | Ge  : expr -> expr -> expr
  | Gt  : expr -> expr -> expr
  | Eq  : expr -> expr -> expr
  | Ne  : expr -> expr -> expr
  | And : expr -> expr -> expr
  | Or  : expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Or  x y) (at level 38, left associativity).

Hint Constructors expr.

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always : 
    forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
  Proof. intros n s. apply bs_Nat. Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof. 
    intros s e z H. 
      inversion H. inversion H5. 
        assert (A: (za * Z.of_nat 2)%Z = (za + za)%Z). simpl. omega.
      rewrite A. apply bs_Add; assumption.
  Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof.
  intros e s z id Heval Hdef.
  generalize dependent z.
  induction e;
    (* solves cases with binary operations Z->Z->Z *)
    try solve [
          intros z Hact;     
          inversion_clear Hdef;
          inversion_clear Hact;
          inversion_clear H as [Hl | Hr];
          [ exact (IHe1 Hl za H0) |
            exact (IHe2 Hr zb H1) ]
        ];
    (* solves cases with binary operations Z->Z->bool *)
    try solve [
          intros z Hact;
          inversion_clear Hdef;
          inversion_clear Hact;
          [
            inversion_clear H as [Hl | Hr]; [
              exact (IHe1 Hl za H0) |
              exact (IHe2 Hr zb H1) ] |
            inversion_clear H as [Hl | Hr]; [
                exact (IHe1 Hl za H0) |
                exact (IHe2 Hr zb H1)] ]
        ].  
  (* e = Nat n*)
  inversion Hdef.
  (* e = Var i*)
  induction s.
     (* base *)
     intros z Heval. inversion Heval. inversion H0.
     (* step *)
     intros z Hdef_new. inversion Hdef_new. inversion Hdef.
     subst i i0 id0. exists z. assumption. 
  Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof.
  intros e s id Hvar Hundef z.
  unfold not; intro Heval.
  pose proof (defined_expression e s z id Heval Hvar) as Hex.
  inversion Hex as [x Hdef].
  contradiction (Hundef x).
Qed.

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof.
  intros e s z1 z2 H1 H2.
  generalize dependent z1.
  generalize dependent z2.
  induction e;
    try (intros z2 H2 z1 H1; inversion H1; inversion H2; reflexivity);
    try (intros z2 H2 z1 H1; 
           inversion H1; 
           inversion H2; 
           rewrite <-(state_deterministic Z s i z1 z2); auto);
    try (intros z2 H2 z1 H1; 
           inversion H1; 
           inversion H2; 
           apply (IHe1 za0) in H3; 
           apply (IHe2 zb0) in H6; congruence; assumption);
    try (intros z2 H2 z1 H1;
           inversion H1; 
             (inversion H2; 
                try reflexivity;
                apply (IHe1 za0) in H3; [
                  subst za;
                  apply (IHe2 zb0) in H4; [
                    subst zb; contradiction 
                  | assumption ] 
                | assumption]; 
                try reflexivity
             ));
    try (intros z2 H2 z1 H1;
           inversion H1;
             (inversion H2; 
                apply (IHe1 za0) in H3; [
                  subst za; 
                  apply (IHe2 zb0) in H4; [
                    subst zb; reflexivity 
                  | assumption] 
                | assumption]
             )).
Qed.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Ltac apply_bs_constructor :=
  match goal with 
    H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[<=]?e2|]?s => Z.one => 
      apply (bs_Le_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[<=]?e2|]?s => Z.zero => 
      apply (bs_Le_F s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[<]?e2|]?s => Z.one => 
      apply (bs_Lt_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[<]?e2|]?s => Z.zero => 
      apply (bs_Lt_F s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[>=]?e2|]?s => Z.one => 
      apply (bs_Ge_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[>=]?e2|]?s => Z.zero => 
      apply (bs_Ge_F s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[>]?e2|]?s => Z.one => 
      apply (bs_Gt_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[>]?e2|]?s => Z.zero => 
      apply (bs_Gt_F s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[==]?e2|]?s => Z.one => 
      apply (bs_Eq_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[==]?e2|]?s => Z.zero => 
      apply (bs_Eq_F s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[/=]?e2|]?s => Z.one => 
      apply (bs_Ne_T s e1 e2 za zb)
  | H1: [|?e1|]?s => ?za, H2: [|?e2|]?s => ?zb |- [|?e1[/=]?e2|]?s => Z.zero => 
      apply (bs_Ne_F s e1 e2 za zb)
  end.

Lemma equivalent_states: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id) (z : Z), id ? e -> s1 / id => z -> s2 / id => z) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof. 
  intros e s1 s2 z H1 H2. 
  generalize dependent s1.
  generalize dependent s2.
  generalize dependent z.
  induction e.
    try (intros z s2 s1 H1 H2; inversion H2; constructor).
    try (intros z s2 s1 H1 H2; inversion H2; apply (H1 i z) in H0; [constructor; assumption | constructor]).
    try (intros z s1 s2 H1 H2;
           inversion H2;
             apply (IHe1 za s1 s2) in H3; [        
               apply (IHe2 zb s1 s2) in H6; [
                 constructor; assumption
               | intros id z0 HVar HVal; 
                 apply (H1 id z0); [
                   constructor; right; assumption
                 | assumption
                 ]
               ]
             | intros id z0 HVar HVal; 
               apply (H1 id z0); [
                 constructor; left; assumption 
               | assumption
               ]
             ]).

    try (intros z s1 s2 H1 H2;
           inversion H2;
             apply (IHe1 za s1 s2) in H3; [        
               apply (IHe2 zb s1 s2) in H6; [
                 constructor; assumption
               | intros id z0 HVar HVal; 
                 apply (H1 id z0); [
                   constructor; right; assumption
                 | assumption
                 ]
               ]
             | intros id z0 HVar HVal; 
               apply (H1 id z0); [
                 constructor; left; assumption 
               | assumption
               ]
             ]).
    try (intros z s1 s2 H1 H2;
           inversion H2;
             apply (IHe1 za s1 s2) in H3; [        
               apply (IHe2 zb s1 s2) in H6; [
                 constructor; assumption
               | intros id z0 HVar HVal; 
                 apply (H1 id z0); [
                   constructor; right; assumption
                 | assumption
                 ]
               ]
             | intros id z0 HVar HVal; 
               apply (H1 id z0); [
                 constructor; left; assumption 
               | assumption
               ]
             ]).
    try (intros z s1 s2 H1 H2;
           inversion H2;
             apply (IHe1 za s1 s2) in H3; [        
               apply (IHe2 zb s1 s2) in H6; [
                 constructor; assumption
               | intros id z0 HVar HVal; 
                 apply (H1 id z0); [
                   constructor; right; assumption
                 | assumption
                 ]
               ]
             | intros id z0 HVar HVal; 
               apply (H1 id z0); [
                 constructor; left; assumption 
               | assumption
               ]
             ]).
    try (intros z s1 s2 H1 H2;
           inversion H2;
             apply (IHe1 za s1 s2) in H3; [        
               apply (IHe2 zb s1 s2) in H6; [
                 constructor; assumption
               | intros id z0 HVar HVal; 
                 apply (H1 id z0); [
                   constructor; right; assumption
                 | assumption
                 ]
               ]
             | intros id z0 HVar HVal; 
               apply (H1 id z0); [
                 constructor; left; assumption 
               | assumption
               ]
             ]).

    (* <= *)
    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).

    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).

    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).

    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).

    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).

    try (intros z s1 s2 H1 H2;
           inversion H2;        
             (apply (IHe1 za s1 s2) in H3; [
               apply (IHe2 zb s1 s2) in H4; [
                 apply_bs_constructor; assumption 
               | intros id z0 HVar HVal;
                 apply (H1 id z0); [constructor; right; assumption | assumption]
               ]
             | intros id z0 HVar HVal;
               apply (H1 id z0); [constructor; left; assumption | assumption]
             ])).






              
             






Qed.

 


  