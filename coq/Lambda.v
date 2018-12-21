Require Import List.
Import ListNotations.
Require Import Omega.
Require Import Arith.
Require Import Id.

Inductive term : Type := 
  Var  : id -> term
| Abs  : id -> term -> term 
| App  : term -> term -> term.

Notation "\ x , .. , z --> t" := (Abs x .. (Abs z t) .. ) (at level 38, no associativity).
Notation "m @ n"              := (App m n) (at level 39, left associativity).

Definition f := Id 0.
Definition g := Id 1.
Definition h := Id 2.

Definition x := Id 3.
Definition y := Id 4.

Definition m := Id 5.
Definition n := Id 6.

Definition v i := Var i.
           
Definition i     := \ x --> v x.
Definition apply := \ f, x --> (v f @ v x).
Definition z     := \ f, x --> v x.
Definition s     := \ n, f, x --> (v f @ (v n @ v f @ v x)).
Definition add   := \ n, m, f, x --> (v m @ v f @ (v n @ v f @ v x)).
Definition mul   := \ n, m, f, x --> (v m @ (v n @ v f) @ v x).

Inductive fv : id -> term -> Prop :=
  fv_Var : forall x,  fv x (v x)
| fv_Abs : forall x y t,  fv y t -> x <> y -> fv y (\ x --> t)
| fv_App : forall x a b,  (fv x a) \/ (fv x b) -> fv x (a @ b).

Lemma fv_var: forall x y, fv x (v y) -> x = y.
Proof. intros x y H. inversion H. auto. Qed.
(*
Reserved Notation "m [[ x <~ y ]] n" (at level 40, left associativity).

Inductive cas : term -> id -> id -> term -> Prop :=
  cas_Var     : forall x y           , (v x) [[x <~ y]] (v y)
| cas_Var_neq : forall x y z         , x <> z -> (v z) [[x <~ y]] (v z)
| cas_App     : forall m n m' n' x y , m [[ x <~ y ]] m' -> n [[ x <~ y ]] n' -> (m @ n) [[ x<~ y ]] (m' @ n')
| cas_Lam     : forall m x y         , (\ x --> m) [[ x <~ y ]] (\x --> m)
| cas_Lam_neq : forall m m' x y z    , z <> x -> z <> y -> m [[ x<~ y ]] m' -> (\ z --> m) [[ x <~ y ]] (\z --> m')
| cas_Lam_ren : forall m m' m'' x y z, ~ fv z m -> m [[ y <~ z ]] m' -> m' [[ x <~ y ]] m'' -> (\y --> m) [[ x <~ y ]] (\ z --> m'')
where "m [[ x <~ y ]] n" := (cas m x y n).

Hint Constructors cas.

Lemma cas_reflexive: forall s x, s [[ x <~ x ]] s.
Proof.
  intros s x. induction s.
  * remember (id_eq_dec i0 x) as Cases. inversion_clear Cases.
    + subst i0. auto.
    + auto.
  * remember (id_eq_dec i0 x) as Cases. inversion_clear Cases.
    + subst i0. auto.
    + auto.
  * auto.
Qed.

Lemma cas_preserves: forall x y z s s',  z <> x -> z <> y -> s [[x <~ y ]] s' -> fv z s' -> fv z s.
Proof.
  intros. induction s0.

Lemma cas_renames_free: forall s s' x y,  x <> y -> s [[ x <~ y ]] s' -> ~fv x s'.
Proof.
  induction s0.
  * intros. remember (id_eq_dec i0 x) as Cases. inversion_clear Cases.
    + subst i0. intro. inversion H0; subst s'; inversion H1; auto.
    + inversion H0. intro. inversion H6. auto. intro. inversion H7. auto.
  * intros. inversion_clear H0.
    + intro. inversion_clear H0. auto.
    + intro. inversion_clear H0. apply IHs0 in H3; auto.
    + remember (id_eq_dec x0 z0) as Cases. inversion_clear Cases.
      - subst z0. intro. inversion H0. auto.
      - intro. inversion_clear H4. apply cas_preserves with (x:=y0)(y:=z0)(s:=m') in H5.
  * intros. inversion_clear H0. intro. inversion_clear H0. inversion_clear H3.
    + apply IHs0_1 in H1; auto.
    + apply IHs0_2 in H2; auto.    
Admitted.
 *)

Reserved Notation "m [[ x <~ y ]]" (at level 37, left associativity).

Fixpoint rename t x y :=
  match t with
  | Var z     => if id_eq_dec z x then v y else t
  | \ z --> m => if id_eq_dec z x then t else \ z --> m [[x <~ y]]
  | m @ n     => m [[x <~ y]] @ n [[x <~ y]]
  end
where "m [[ x <~ y ]]" := (rename m x y).

(*
Lemma rename_idempotent: forall s x y, ~fv y s \/ x = y -> rename (rename s x y) y x = s. (* Not true! *)
Proof. admit. Admitted.

Lemma rename_composition: forall s x y z, ~fv y s -> ~fv z s -> rename (rename s x y) y z = rename s x z. (* Not true! *)
Proof. admit. Admitted.

Hint Resolve rename_renames_free.
Hint Resolve rename_idempotent.
Hint Resolve rename_composition.

Reserved Notation "m ~~> n" (at level 38, no associativity).
         
Inductive alpha_convertable : term -> term -> Prop :=
  ac_Intro : forall x y m n, ~fv y m \/ x = y -> n = rename m x y -> (\ x --> m) ~~> (\ y --> n)
where "m ~~> n" := (alpha_convertable m n).

Lemma alpha_conversion_reflexive: forall x m, alpha_convertable (\ x --> m) (\x --> m).
Proof.
  intros x m. constructor.
  * right. reflexivity.
  * induction m.
    + simpl. destruct (id_eq_dec i0 x); try subst i0; auto. 
    + simpl. destruct (id_eq_dec i0 x); try rewrite <- IHm; auto.
    + simpl. rewrite <- IHm1. rewrite <- IHm2. auto.
Qed.

Lemma alpha_conversion_symmetric: forall m n, alpha_convertable m n -> alpha_convertable n m.
Proof. admit. Admitted.
(*
  intros m n H. inversion_clear H. subst n0. constructor.
  * inversion_clear H0; [left; auto | right; auto].
  * symmetry. auto.
Qed.
*)
Lemma alpha_conversion_transitive: forall m n p, alpha_convertable m n -> alpha_convertable n p -> alpha_convertable m p.
Proof. admit. Admitted.
(*
  intros m n p H1 H2. generalize dependent m. generalize dependent n. induction p.
  * intros. inversion H2.
  * intros. inversion H2. subst n0. inversion H1. subst m0. constructor.
    + inversion_clear H8.
      - left.  subst p. subst m1. auto.
  * intros. inversion H2.
Qed.*)

Hint Resolve alpha_conversion_reflexive.
Hint Resolve alpha_conversion_symmetric.
Hint Resolve alpha_conversion_transitive.

Reserved Notation "m <~~> n" (at level 38, no associativity).

Inductive alpha_equivalent : term -> term -> Prop :=
  ae_Base : forall m n      , m ~~> n -> m <~~> n
| ae_Var  : forall x        , (v x) <~~> (v x)                                    
| ae_App  : forall m n m' n', m <~~> m' -> n <~~> n' -> (m @ n) <~~> (m' @ n')
| ae_Lam  : forall x m m'   , m <~~> m' -> \x --> m <~~> \x --> m'
where "m <~~> n" := (alpha_equivalent m n).

Hint Constructors alpha_equivalent.
     
Lemma alpha_equivalence_reflexive: forall m, m <~~> m.
Proof. intro m. induction m; auto. Qed.

Lemma alpha_equivalence_symmetric: forall m n, m <~~> n -> n <~~> m.
Proof. intros m n H. induction H; auto. Qed.

Lemma alpha_equivalence_transitive: forall p m n, m <~~> n -> n <~~> p -> m <~~> p.
Proof.
  intros p. induction p.
  * intros. inversion H0.
    + inversion H1.
    + subst n0. inversion H0.
       - inversion H1.
       - inversion H. inversion H1. auto.
  * intros. inversion H0.
    + inversion H1. subst n0. subst m1. inversion H.
       - apply ae_Base. apply alpha_conversion_transitive with (\ x0 --> m2); auto.
       - subst x0. subst m0. apply ae_Base. constructor. inversion_clear H7. left. 
  * intros. inversion H0. inversion H1. subst n0. inversion H. inversion H3.
    apply ae_App.
    + apply IHp1 with (m:=m2)(n:=m1); auto.
    + apply IHp2 with (m:=n0)(n:=n1); auto.
Admitted.
 *)

Inductive safe : term -> id -> id -> Prop :=
  safe_Var   : forall x y z  , x <> z -> safe (Var x) y z
| safe_App   : forall m n x y, safe m x y -> safe n x y -> safe (m @ n) x y
| safe_Lam_1 : forall m z y  , safe (\ z --> m) z y
| safe_Lam_2 : forall m x y z, y <> z -> x <> z -> safe m x y -> safe (\ z --> m) x y
| safe_Lam_3 : forall m x z  , x <> z -> ~ fv x m -> safe (\ z --> m) x z.

Lemma safe_reverse : forall m x y, safe m x y -> safe (m [[x <~ y]]) y x.
Proof.
  intros m x y H. induction m.
  * simpl. destruct (id_eq_dec i0 x).
    + subst i0. inversion H. constructor. auto.
    + inversion H. constructor. auto.
  * inversion H.
    + simpl. destruct (id_eq_dec x x). subst x.     
  * inversion H. simpl. constructor; auto.
Admitted.
  
  * simpl. destruct (id_eq_dec x0 y0).
    + constructor. subst x0. intro. symmetry in H0. contradiction.
    + constructor. auto.
  * simpl. constructor; auto.
  * 
   
  

Hint Resolve safe_reverse.

Lemma rename_reverse : forall m x y, safe m x y -> (m [[x <~ y]]) [[y <~ x]] = m.
Proof. admit. Admitted.

Hint Resolve rename_reverse.

Reserved Notation "m <~~> n" (at level 38, no associativity).

Inductive alpha_equivalent : term -> term -> Prop :=
  ae_Var  : forall x, v x <~~> v x
| ae_App  : forall m n m' n', m <~~> m' -> n <~~> n' -> (m @ n) <~~> (m' @ n')
| ae_Lam  : forall x m m'   , m <~~> m' -> (\x --> m) <~~> (\x --> m')
| ae_Conv : forall x y m m' , m <~~> m' -> safe m' x y -> (\x --> m) <~~> (\y --> m' [[x <~ y]])
where "m <~~> n" := (alpha_equivalent m n).

Hint Constructors alpha_equivalent.

Lemma alpha_reflexive: forall m, m <~~> m.
Proof. intro m. induction m; auto. Qed.

Hint Resolve alpha_reflexive.

Lemma alpha_transitive: forall m n p,  m <~~> n -> n <~~> p -> m <~~> p.
Proof. admit. Admitted.

Lemma alpha_symmetric: forall m n, m <~~> n -> n <~~> m.
Proof.
  intros m n H. induction H.
  * auto.
  * auto.
  * auto.
  * assert (M'M0: \ x0 --> m' <~~> \ x0 --> m0). constructor. auto.
    assert (M0M': \ x0 --> m0 <~~> \ x0 --> m'). constructor. auto.
    assert (Revr: (m' [[x0 <~ y0]]) [[y0 <~ x0]] = m'). auto.
    assert (A: \ y0 --> m' [[x0 <~ y0]] <~~> \ x0 --> m'). rewrite <-Revr at 2. constructor; auto.
    apply alpha_transitive with (\ x0 --> m'); auto. 
Qed.