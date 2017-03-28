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

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

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

Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id) (z : Z), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof. 
  unfold equivalent_states.
  intros e s1 s2 z H1 H2. 
  generalize dependent s1.
  generalize dependent s2.
  generalize dependent z.
  induction e; 
    solve [
      (* constant *)
      intros z s2 s1 H1 H2; inversion H2; constructor 
      (* variable *)
    | intros z s2 s1 H1 H2; inversion H2; apply (H1 i z) in H0; [constructor; assumption | constructor]
      (* arithmetics *)
    | intros z s1 s2 H1 H2;
        inversion H2;
          apply (IHe1 za s1 s2) in H3; 
            apply (IHe2 zb s1 s2) in H6; 
              try (constructor; assumption);
              (intros id z0 HVar; 
                 split; (
                   intro HVal;
                     apply (H1 id z0); [
                       solve [
                         constructor; right; assumption 
                       | constructor; left; assumption ]
                     | assumption ]
                 )
              )
      (* relations *)
    | intros z s1 s2 H1 H2;
        inversion H2;
          (apply (IHe1 za s1 s2) in H3; [
             apply (IHe2 zb s1 s2) in H4; [
               apply_bs_constructor; assumption 
             | intros id z0 HVar; 
                 split; [
                   intro HVal; apply (H1 id z0); [ 
                     constructor; right; assumption
                   | assumption]
                 | intro HVal; apply (H1 id z0) in HVal; [ 
                     assumption 
                   | constructor; right; assumption ]
                 ]
             ] 
           | intros id z0 HVar;
               split; [
                 intro HVal; apply (H1 id z0); [ 
                   constructor; left; assumption 
                 | assumption] 
               | intro HVal; apply (H1 id z0) in HVal; [ 
                   assumption 
               | constructor; left; assumption ]
               ]
           ]
          )
      (* booleans *)
    | intros z s1 s2 H1 H2;
        inversion H2;
          constructor; 
            try assumption;
            try apply (IHe1 za s1 s2); 
            try apply (IHe2 zb s1 s2); (
              try assumption;
              intros id z0 HVar;
              split; (
                intro HVal; apply (H1 id z0); [ 
                  solve [ constructor; left; assumption | constructor; right; assumption ]
                | assumption ]
              )
            )
    ].
Qed.

Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

Lemma eq_refl: forall (e : expr), e ~~ e.
Proof.
  intro e. constructor. intros n s. split; auto.    
Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof.
  intros e1 e2 H. inversion_clear H. constructor. intros n s. split;
    (intro HVal; apply H0; assumption).
Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof.
  intros e1 e2 e3 H1 H2.
  inversion_clear H1. inversion_clear H2. constructor.
  intros n s. split; [
    intro HVal; apply H0; apply H; assumption
  | intro HVal; apply H; apply H0; assumption].     
Qed.
 
Inductive Context : Type :=
  | Hole : Context
  | AddL : Context -> expr -> Context
  | SubL : Context -> expr -> Context
  | MulL : Context -> expr -> Context
  | DivL : Context -> expr -> Context
  | ModL : Context -> expr -> Context
  | LeL  : Context -> expr -> Context
  | LtL  : Context -> expr -> Context
  | GeL  : Context -> expr -> Context
  | GtL  : Context -> expr -> Context
  | EqL  : Context -> expr -> Context
  | NeL  : Context -> expr -> Context
  | AndL : Context -> expr -> Context
  | OrL  : Context -> expr -> Context
  | AddR : expr -> Context -> Context
  | SubR : expr -> Context -> Context
  | MulR : expr -> Context -> Context
  | DivR : expr -> Context -> Context
  | ModR : expr -> Context -> Context
  | LeR  : expr -> Context -> Context
  | LtR  : expr -> Context -> Context
  | GeR  : expr -> Context -> Context
  | GtR  : expr -> Context -> Context
  | EqR  : expr -> Context -> Context
  | NeR  : expr -> Context -> Context
  | AndR : expr -> Context -> Context
  | OrR  : expr -> Context -> Context.

Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | AddL C e1 => Add (plug C e) e1
  | SubL C e1 => Sub (plug C e) e1
  | MulL C e1 => Mul (plug C e) e1
  | DivL C e1 => Div (plug C e) e1
  | ModL C e1 => Mod (plug C e) e1
  | LeL  C e1 => Le  (plug C e) e1
  | LtL  C e1 => Lt  (plug C e) e1
  | GeL  C e1 => Ge  (plug C e) e1
  | GtL  C e1 => Gt  (plug C e) e1
  | EqL  C e1 => Eq  (plug C e) e1
  | NeL  C e1 => Ne  (plug C e) e1
  | AndL C e1 => And (plug C e) e1
  | OrL  C e1 => Or  (plug C e) e1
  | AddR e1 C => Add e1 (plug C e)
  | SubR e1 C => Sub e1 (plug C e)
  | MulR e1 C => Mul e1 (plug C e)
  | DivR e1 C => Div e1 (plug C e)
  | ModR e1 C => Mod e1 (plug C e)
  | LeR  e1 C => Le  e1 (plug C e)
  | LtR  e1 C => Lt  e1 (plug C e)
  | GeR  e1 C => Ge  e1 (plug C e)
  | GtR  e1 C => Gt  e1 (plug C e)
  | EqR  e1 C => Eq  e1 (plug C e)
  | NeR  e1 C => Ne  e1 (plug C e)
  | AndR e1 C => And e1 (plug C e)
  | OrR  e1 C => Or  e1 (plug C e)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  intros e1 e2. split.
    intro H. constructor. intro C.
      induction C; solve [
        simpl; assumption
      | simpl; constructor; intros;
          split;
            (intro; inversion_clear H0; inversion IHC; try (apply H0 in H1); try (apply H0 in H2);
              constructor; assumption; assumption)
      | simpl; constructor; intros;
          split;
            (intro; inversion_clear H0; inversion IHC; try (apply H0 in H1); try (apply H0 in H2);
              apply_bs_constructor; assumption; assumption; assumption)
      ].
    intro H. inversion H. remember (H0 Hole). simpl in e. assumption.
Qed.




























     
  
      
 