Require Export BigZ.
Require Export Id.
Require Export State.

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

Hint Constructors expr.

Definition zbool (x : Z) : Prop := x = Z.of_nat 1 \/ x = Z.of_nat 0.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.of_nat 1 else Z.of_nat 0.

Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| Add a b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| Sub a b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| Mul a b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| Div a b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| Mod a b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| Le a b |] s => (Z.of_nat 1)
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| Le a b |] s => (Z.of_nat 0)

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| Lt a b |] s => (Z.of_nat 1)
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| Lt a b |] s => (Z.of_nat 0)

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| Ge a b |] s => (Z.of_nat 1)
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| Ge a b |] s => (Z.of_nat 0)

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| Gt a b |] s => (Z.of_nat 1)
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| Gt a b |] s => (Z.of_nat 0)

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| Eq a b |] s => (Z.of_nat 1)
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| Eq a b |] s => (Z.of_nat 0)

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| Ne a b |] s => (Z.of_nat 1)
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| Ne a b |] s => (Z.of_nat 0)

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| And a b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| Or a b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Lemma nat_always : forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
Proof. intros n s. apply bs_Nat. Qed.