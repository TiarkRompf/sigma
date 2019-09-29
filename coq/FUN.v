Add LoadPath "/home/greg/Research/closedforms/coq".

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import NewImp.


Module Translation.
Import IMPEval.

Inductive gxp : Type :=
  | GNum : nat -> gxp
  | GLoc: loc -> gxp
  | GObj: (total_map nat (option gxp)) -> gxp
  | GMap : (total_map loc (option gxp)) -> gxp
  | GHasField: gxp -> gxp -> gxp
  | GGet : gxp -> gxp -> gxp
  | GPut : gxp -> gxp -> gxp -> gxp

  | GPlus : gxp -> gxp -> gxp
  | GMinus : gxp -> gxp -> gxp
  | GMult : gxp -> gxp -> gxp

  | GBool : bool -> gxp
  | GEq : gxp -> gxp -> gxp
  | GLt : gxp -> gxp -> gxp
  | GNot : gxp -> gxp

  | GIf : gxp -> gxp -> gxp -> gxp
  | GFixIndex : nat -> id -> gxp -> gxp.

Definition fvalid : gxp := GLoc (LId (Id 0)). (* "$valid" *)
Definition fdata :  gxp := GLoc (LId (Id 1)). (* "$data"  *)
Definition ftpe :   gxp := GNum 0. (* "$tpe"   *)
Definition fval :   gxp := GNum 1. (* "$val"   *)

Hint Unfold fdata.

Definition tnat :   gxp := GNum 0.
Definition tbool :  gxp := GNum 1.
Definition tloc :   gxp := GNum 2.

Definition empty_store := fun k =>
                           match k with
                           | LId x => Some (GObj (t_empty None))
                           | LNew p => None
                           end.
Definition GEmpty : gxp := GMap empty_store.

Definition OEmpty : gxp := GObj(t_empty None).

Definition GNone :  gxp := GPut GEmpty fvalid (GBool false).
 (* GMap (t_update beq_loc (t_empty None)
   (LId (Id 0)) (Some (GBool false))). *)

Definition GSome a : gxp := GPut (GPut GEmpty fvalid (GBool true)) fdata a.

Definition GMatch (scrutinee: gxp) (none: gxp) (some: gxp -> gxp): gxp :=
  GIf (GGet scrutinee fvalid) (some (GGet scrutinee fdata)) none.

Definition GVSelect (addr: gxp) (field: gxp): gxp :=
  GIf (GHasField addr field) (GSome (GGet addr field)) GNone.

Definition GVNum (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tnat) fval a.

Definition GVNumR (a: gxp): gxp :=
  GObj (t_update Nat.eqb (t_update Nat.eqb (t_empty None) 0 (Some tnat)) 1 (Some a)).

Definition GVBool (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tbool) fval a.

Definition GVBoolR (a: gxp): gxp :=
  GObj (t_update Nat.eqb (t_update Nat.eqb (t_empty None) 0 (Some tbool)) 1 (Some a)).

Definition GVLoc (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tloc) fval a.

Definition GVLocR (a: gxp): gxp :=
  GObj (t_update Nat.eqb (t_update Nat.eqb (t_empty None) 0 (Some tloc)) 1 (Some a)).

Definition sym_store := total_map (option gxp).

Definition toNatG (v:gxp): gxp :=
  GIf (GEq (GGet v ftpe) tnat) (GSome (GGet v fval)) GNone.

Definition toBoolG (v:gxp): gxp :=
  GIf (GEq (GGet v ftpe) tbool) (GSome (GGet v fval)) GNone.

Definition toLocG (v:gxp): gxp :=
  GIf (GEq (GGet v ftpe) tloc) (GSome (GGet v fval)) GNone.

Notation "'LETG' x <-- e1 'IN' e2"
   := (GMatch e1 GNone (fun x => e2))
   (right associativity, at level 60).
(* Notation "'LETG' x <--- e1 'IN' e2"
   := (match e1 with
         | Some (Some x) => e2
         | Some None => Some None
         | None => None
       end)
   (right associativity, at level 60). *)

Notation "e1 '>>g=' e2"
   := (GMatch e1 GNone e2)
   (right associativity, at level 80).

(* ---------- translation (exp only for now) --------- *)
Fixpoint trans_exp (e: exp) (sto: gxp): gxp :=
  match e with
  (* | AId x => GGet sto x (* fixme: check error *) *)
  | ELoc id => GSome (GVLoc (GLoc (LId id)))
  | ENum n => GSome (GVNum (GNum n))
  | EPlus a b =>  LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GPlus a b))
  | EMinus a b => LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GMinus a b))
  | EMult a b =>  LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GMult a b))
  | EBool b =>    GSome (GVBool (GBool b))
  | EEq a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GEq a b))
  | ELt a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GLt a b))
  | EAnd a b =>   LETG a <-- trans_exp a sto >>g= toBoolG IN
                  LETG b <-- trans_exp b sto >>g= toBoolG IN
                  GSome (GVBool (GIf a b (GBool false)))
  | ENeg a =>     LETG a <-- trans_exp a sto >>g= toBoolG IN
                  GSome (GVBool (GNot a))
  | EFieldRead s n =>
                  LETG s' <-- trans_exp s sto >>g= toLocG IN
                  LETG n' <-- trans_exp n sto >>g= toNatG IN
                  LETG o <-- GVSelect sto s' IN
                  GVSelect o n'
  end.


Fixpoint trans_loop (e: exp) (s: stmt) (sto: gxp) (c: path) (n: nat) (* How to use GFixIndex? *)
    (evstmt : gxp -> path -> gxp) : gxp:=
  match n with
  | O => GSome sto
  | S n' =>
    LETG b <-- trans_exp e sto >>g= toBoolG IN
    LETG sto' <-- trans_loop e s sto c n' evstmt IN 
    GIf b (evstmt sto' (PWhile c n')) GNone
  end.

Fixpoint trans_stmts (s: stmt) (sto: gxp) (c: path) { struct s }: gxp :=
  match s with
  | x ::= ALLOC =>
    GPut (GPut sto (GLoc (LNew c)) OEmpty) (GLoc (LId x)) (GPut OEmpty (GLoc (LId (Id 0))) (GLoc (LNew c)))
  | e1[[e2]] ::= e3 =>
    LETG l <-- trans_exp e1 sto >>g= toLocG IN
    LETG n <-- trans_exp e2 sto >>g= toNatG IN
    LETG v <-- trans_exp e3 sto IN
    LETG o <-- GVSelect sto l IN
    GPut sto l (GPut o n v)
  | IF e THEN s1 ELSE s2 FI =>
    LETG b <-- trans_exp e sto >>g= toBoolG IN
    GIf b (trans_stmts s1 sto (PThen c)) (trans_stmts s2 sto (PElse c))
  | WHILE cnd DO s END =>
      trans_loop cnd s sto c 3 (fun sto' c' => trans_stmts s sto' c')
  | s1 ;; s2 =>
      LETG sto' <-- trans_stmts s1 sto (PFst c) IN
      trans_stmts s2 sto' (PSnd c)
  | SKIP => GSome sto
  | SAbort => GNone
  end.

(* ---------- small-step rules for FUN ---------- *)

Inductive value : gxp -> Prop :=
| v_num : forall n, value (GNum n)
| v_loc : forall l, value (GLoc l)
| v_bool : forall b, value (GBool b)
| v_obj: forall m, (forall x y, m x = Some y -> value y) -> value (GObj m)
| v_sto: forall m, (forall x y, m x = Some y -> value y) -> value (GMap m).

Hint Constructors value.

Reserved Notation " t '==>' t' " (at level 40).

Fixpoint subst (x : id) (s : gxp) (t : gxp) : gxp :=
  match t with
  | GNum n => GNum n
  | GBool b => GBool b
  | GLoc (LId i) => if beq_id i x then s else t
  | GLoc l => GLoc l
  | GObj m => GObj m
  | GMap m => GMap m
  
  | GHasField m i => GHasField (subst x s m) (subst x s i)
  | GGet m i => GGet (subst x s m) (subst x s i)
  | GPut m i v => GPut (subst x s m) (subst x s i) (subst x s v)

  | GPlus a b => GPlus (subst x s a) (subst x s b)
  | GMinus a b => GMinus (subst x s a) (subst x s b)
  | GMult a b => GMult (subst x s a) (subst x s b)

  | GEq a b => GEq (subst x s a) (subst x s b)
  | GLt a b => GLt (subst x s a) (subst x s b)
  | GNot a => GNot (subst x s a)

  | GIf c a b => GIf (subst x s c) (subst x s a) (subst x s b)
  | GFixIndex i l b => if beq_id x l then t else GFixIndex i l (subst x s b)
  end.

Inductive step : gxp -> gxp -> Prop :=
  (* GPlus *)
  | ST_PlusConstConst : forall n1 n2,
          GPlus (GNum n1) (GNum n2)
      ==> GNum (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GPlus t1 t2 ==> GPlus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        GPlus v1 t2 ==> GPlus v1 t2'
  (* GMinus *)
  | ST_MinusConstConst : forall n1 n2,
          GMinus (GNum n1) (GNum n2)
      ==> GNum (n1 - n2)
  | ST_Minus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GMinus t1 t2 ==> GMinus t1' t2
  | ST_Minus2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        GMinus v1 t2 ==> GMinus v1 t2'
  (* GMult *)
  | ST_MultConstConst : forall n1 n2,
          GMult (GNum n1) (GNum n2)
      ==> GNum (n1 * n2)
  | ST_Mult1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GMult t1 t2 ==> GMult t1' t2
  | ST_Mult2 : forall v1 t2 t2',
        value v1 -> 
        t2 ==> t2' ->
        GMult v1 t2 ==> GMult v1 t2'

  (* GEq *)
  | ST_EqNumConstConst : forall n1 n2,
          GEq (GNum n1) (GNum n2)
      ==> GBool (n1 =? n2)
  | ST_EqLocConstConst : forall l1 l2,
          GEq (GLoc l1) (GLoc l2)
      ==> GBool (beq_loc l1 l2)
  | ST_Eq1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GEq t1 t2 ==> GEq t1' t2
  | ST_Eq2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        GEq v1 t2 ==> GEq v1 t2'

  (* GLt *)
  | ST_LtConstConst : forall n1 n2,
          GLt (GNum n1) (GNum n2)
      ==> GBool (n1 <? n2)
  | ST_Lt1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GLt t1 t2 ==> GLt t1' t2
  | ST_Lt2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        GLt v1 t2 ==> GLt v1 t2'
  
  (* GNot *)
  | ST_NotConst : forall b1,
          GNot (GBool b1)
      ==> GBool (negb b1)
  | ST_Not : forall t1 t1',
        t1 ==> t1' ->
        GNot t1 ==> GNot t1'

  (* GIf *)
  | ST_IfTrue : forall t2 t3,
       GIf (GBool true) t2 t3 ==> t2
  | ST_IfFalse : forall t2 t3,
       GIf (GBool false) t2 t3 ==> t3
  | ST_IfCond : forall t1 t1' t2 t3,
       t1 ==> t1' ->
       GIf t1 t2 t3 ==> GIf t1' t2 t3
  

  (* GFixIndex*)
  | ST_FixIndex : forall i l t,
       GFixIndex (i + 1) l t ==> GIf (subst l (GNum i) t) (GNum i) (GFixIndex (i + 1) l t)

  (* GHasField *)
  | ST_ObjHasFieldTrue : forall n m,
       m n <> None ->
       GHasField (GObj m) (GNum n) ==> GBool true
  | ST_ObjHasFieldFalse : forall n m,
       m n = None ->
       GHasField (GObj m)(GNum n)  ==> GBool false
  | ST_StHasFieldTrue : forall l m,
       m l <> None ->
       GHasField (GMap m) (GLoc l) ==> GBool true
  | ST_StoHasFieldFalse : forall l m,
       m l = None ->
       GHasField (GMap m) (GLoc l) ==> GBool false
  | ST_HasFieldKey : forall t1 t2 t2',
       t2 ==> t2' ->
       GHasField t1 t2 ==> GHasField t1 t2'
  | ST_HasFieldMap : forall t1 t1' v2,
       value v2 ->
       t1 ==> t1' ->
       GHasField t1 v2 ==> GHasField t1' v2
  (* GGet *)
  | ST_ObjGet : forall n m v,
       m n = Some v ->
       GGet (GObj m) (GNum n) ==> v
  | ST_StoreGet : forall l m v,
       m l = Some v ->
       GGet (GMap m) (GLoc l) ==> v
  | ST_GetKey : forall t1 t2 t2',
       t2 ==> t2' ->
       GGet t1 t2 ==> GGet t1 t2'
  | ST_GetMap : forall t1 t1' v2,
       value v2 -> 
       t1 ==> t1' ->
       GGet t1 v2 ==> GGet t1' v2
  (* GPut *)
  | ST_ObjPut : forall n m v3,
       value (GObj m) ->
       value v3 ->
       GPut (GObj m) (GNum n) v3 ==> GObj (t_update beq_nat m n (Some v3))
  | ST_StorePut : forall l m v3,
       value (GMap m) ->
       value v3 ->
       GPut (GMap m) (GLoc l) v3 ==> GMap (t_update beq_loc m l (Some v3))
  | ST_PutKey : forall t1 t2 t2' t3,
       t2 ==> t2' ->
       GPut t1 t2 t3 ==> GPut t1 t2' t3
  | ST_PutMap : forall t1 t1' v2 t3,
       value v2 ->
       t1 ==> t1' ->
       GPut t1 v2 t3 ==> GPut t1' v2 t3
  | ST_PutValue : forall v1 v2 t3 t3',
       value v1 ->
       value v2 ->
       t3 ==> t3' ->
       GPut v1 v2 t3 ==> GPut v1 v2 t3'
  where " t '==>' t' " := (step t t').

Definition relation (X: Type) := X->X->Prop.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '==>*' t' " := (multi step t t') (at level 40).

Lemma multi_trans : forall e1 e2 e3, e1 ==>* e2 -> e2 ==>* e3 -> e1 ==>* e3.
Proof.
  intros e1 e2 e3 H.
  induction H; [ eauto | intros; econstructor; eauto].
Qed.

(* ----- equivalence between IMP and FUN ----- *)

Inductive veq : val -> gxp -> Prop :=
| VEQ_Num : forall n,
    veq (VNum n) (GVNumR (GNum n))
| VEQ_Bool : forall n,
    veq (VBool n) (GVBoolR (GBool n))
| VEQ_Loc : forall l,
    veq (VLoc l) (GVLocR (GLoc l)).

Definition GSomeR a : gxp := GMap (t_update beq_loc
   (t_update beq_loc empty_store
      (LId (Id 0)) (Some (GBool true)))
      (LId (Id 1)) (Some a)).

Inductive oeq {X:Type} (peq: X -> gxp -> Prop): option X -> gxp -> Prop :=
| REQ_Some : forall v g,
    peq v g ->
    oeq peq (Some v) (GSomeR g)
| REQ_None :
    oeq peq None GNone.

Hint Constructors veq.
Hint Constructors oeq.

Lemma LId_neq : forall (n m : nat), 
  n <> m -> LId (Id n) <> LId (Id m).
Proof. intros. intro contra. inversion contra. omega. Qed.

Hint Resolve LId_neq.

Lemma fdata_value : value fdata. Proof. constructor. Qed.
Lemma fval_value : value fval. Proof. constructor. Qed.
Lemma ftpe_value : value ftpe. Proof. constructor. Qed.
Lemma fvalid_value : value fvalid. Proof. constructor. Qed.

(* not sure why this is needed... auto do not prove value fdata otherwise *)
Hint Resolve fval_value fdata_value ftpe_value fvalid_value. 

Lemma OEmpty_value : value OEmpty.
Proof.
  apply v_obj.
  intros x y Hsome.
  inversion Hsome.
Qed.

Lemma GEmpty_value : value GEmpty.
Proof.
  apply v_sto.
  intros x y Hsome.
  destruct x; inversion Hsome.
  apply OEmpty_value.
Qed.

Lemma value_conservation : forall m x y,
  value y ->
  value (GMap m) ->
  value (GMap (t_update beq_loc m x (Some y))).
Proof.
  intros. constructor.
  intros. destruct (loc_dec x x0); subst.
  - erewrite t_update_eq in H1. inversion H1; subst. assumption.
  - erewrite t_update_neq in H1; auto. inversion H0; subst. eapply H4. eassumption.
Qed.

Lemma nat_dec : forall (n1 n2 : nat), n1 = n2 \/ n1 <> n2.
Proof. intros. omega. Qed.

Lemma obj_value_conservation : forall m x y,
  value y ->
  value (GObj m) ->
  value (GObj (t_update Nat.eqb m x (Some y))).
Proof.
  intros. constructor.
  intros. destruct (nat_dec x x0); subst.
  - erewrite t_update_eq in H1. inversion H1; subst. assumption.
  - erewrite t_update_neq in H1; auto. inversion H0; subst. eapply H4. eassumption.
Qed.

Hint Resolve value_conservation obj_value_conservation.

Lemma GVNumR_value : forall n, value (GVNumR (GNum n)).
Proof.
  intro n.
  constructor.
  intros.
  destruct x.
  - (* x = 0 *)
    rewrite t_update_neq in H; auto.
    rewrite t_update_eq in H.
    inversion H; subst; constructor.
  - (* x > 0 *) destruct x.
  * (* x = 1 *) rewrite t_update_eq in H. inversion H; subst; constructor.
  * repeat (rewrite t_update_neq in H; auto); inversion H.
Qed.

Lemma GVBoolR_value : forall n, value (GVBoolR (GBool n)).
Proof.
  intro n.
  constructor.
  intros.
  destruct x.
  - (* x = 0 *)
    rewrite t_update_neq in H; auto.
    rewrite t_update_eq in H.
    inversion H; subst; constructor.
  - (* x > 0 *) destruct x.
  * (* x = 1 *) rewrite t_update_eq in H. inversion H; subst; constructor.
  * repeat (rewrite t_update_neq in H; auto); inversion H.
Qed.

Lemma GVLocR_value : forall n, value (GVLocR (GLoc n)).
Proof.
  intro n.
  constructor.
  intros.
  destruct x.
  - (* x = 0 *)
    rewrite t_update_neq in H; auto.
    rewrite t_update_eq in H.
    inversion H; subst; constructor.
  - (* x > 0 *) destruct x.
  * (* x = 1 *) rewrite t_update_eq in H. inversion H; subst; constructor.
  * repeat (rewrite t_update_neq in H; auto); inversion H.
Qed.

Hint Resolve GVNumR_value GVBoolR_value GVLocR_value GEmpty_value OEmpty_value.

(* Lemma about None values *)
Lemma LetG_val_None : forall e1 e2,
  e1 ==>* GNone ->
  (LETG a <-- e1 IN e2) ==>* GNone.
Proof. Admitted.

Lemma LetG_body_None : forall e1 e2,
  e2 ==>* GNone ->
  (LETG a <-- e1 IN e2) ==>* GNone.
Proof. Admitted.

Lemma GMatch_left_None : forall e1 e2,
  e1 ==>* GNone ->
  (e1 >>g= e2) ==>* GNone.
Proof. Admitted.

Lemma toNatG_GVBool_None : forall e1 b, (* more generic? *)
  e1 ==>* GSomeR (GVBool b) ->
  (e1 >>g= toNatG) ==>* GNone.
Proof. Admitted.

Lemma toNatG_GVLoc_None : forall e1 b, (* more generic? *)
  e1 ==>* GSomeR (GVLoc b) ->
  (e1 >>g= toNatG) ==>* GNone.
Proof. Admitted.

Lemma LetImp_body_None : forall T U (e1 : option T),
  x ← e1 IN @None U = @None U.
Proof. Admitted.

(* Reduction *)
Lemma GGet_fdata_SomeR : forall v, 
  GGet (GSomeR v) fdata ==>* v.
Proof. econstructor. constructor. apply t_update_eq. constructor. Qed.

Lemma GGet_fvalid_SomeR : forall v, 
  GGet (GSomeR v) fvalid ==> GBool true.
Proof. constructor. rewrite t_update_neq; auto. Qed.

Lemma GGet_fval_GVNumR : forall n,
  value n ->
  GGet (GVNumR n) fval ==>* n.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. apply t_update_eq. constructor.
Qed.

Lemma GSomeR_value : forall v,
  value v ->
  value (GSomeR v).
Proof.
  intros v Hv.
  constructor.
  intros.
  destruct x.
  - (* LId i *) destruct i.
    (* Id n *) destruct n.
    * (* n = 0 *)
      rewrite t_update_neq in H; auto.
      rewrite t_update_eq in H.
      inversion H; subst; constructor.
    * (* n > 0 *) destruct n.
    ** (* n = 1 *) rewrite t_update_eq in H. inversion H; subst; assumption.
    ** repeat (rewrite t_update_neq in H; auto); inversion H; auto.
  - repeat (rewrite t_update_neq in H; try (intro L; inversion L)); inversion H.
Qed.

Hint Resolve GSomeR_value.


(* Congruences *)
Lemma LetG_val_C : forall e1 e1' e2 v,
  e1 ==>* e1' ->
  value v ->
  (LETG a <-- e1' IN e2) ==>* v ->
  (LETG a <-- e1 IN e2) ==>* v.
Proof. Admitted.

Lemma LetG_body_C : forall e1 e2 e2' v,
  e2 ==>* e2' ->
  value v ->
  (LETG a <-- e1 IN e2') ==>* v ->
  (LETG a <-- e1 IN e2) ==>* v.
Proof. Admitted.

Lemma GMatch_C : forall e1 e1' some v,
  e1 ==>* e1' ->
  value v ->
  (e1' >>g= some) ==>* v ->
  (e1 >>g= some) ==>* v.
Proof. Admitted.

Lemma GIf_Cond_R : forall e1 e1' e2 e3,
  e1 ==>* e1' ->
  GIf e1 e2 e3 ==>* GIf e1' e2 e3.
Proof. Admitted.

Lemma GIf_Then_C : forall e1 e2 e2' e3 v,
  e2 ==>* e2' ->
  value v ->
  GIf e1 e2' e3 ==>* v ->
  GIf e1 e2 e3 ==>* v. 
Proof. Admitted.

Lemma GGet_Map_C : forall e1 e1' e2 v,
  e1 ==>* e1' ->
  value v ->
  GGet e1' e2 ==>* v ->
  GGet e1 e2 ==>* v. 
Proof. Admitted.


Lemma GSome_value_R : forall e1 v,
  e1 ==>* v ->
  value v ->
  GSome e1 ==>* GSomeR v.
Proof.
  intros e1 v He1 Hv.
  econstructor. apply ST_PutMap; [ constructor | apply ST_StorePut; auto ].
  induction He1.
  - econstructor; [ apply ST_StorePut; eauto | constructor ].
  - econstructor; try apply ST_PutValue; eauto.
Qed.

Lemma GVNum_value_R : forall e1 v,
  e1 ==>* v ->
  value v ->
  GVNum e1 ==>* GVNumR v.
Proof.
  intros e1 v He1 Hv.
  econstructor. unfold GVNum. apply ST_PutMap; auto; apply ST_ObjPut; auto.
  induction He1.
  - econstructor; [ apply ST_ObjPut; auto | constructor]. 
  - econstructor; try apply ST_PutValue; eauto.
Qed.

Hint Resolve GVNum_value_R.

Lemma tpe_GVNum_nat : forall n e1,
  e1 ==>* GSomeR (GVNumR (GNum n)) ->
  GEq (GGet (GGet e1 fdata) ftpe) tnat ==>* GBool true.
Proof.
  intros n e1 He1.
  (* econstructor. constructor. apply ST_GetMap. constructor.
  apply t_update_eq.
  repeat (apply value_conservation; auto).
  econstructor. constructor. apply ST_ObjGet.
  rewrite t_update_neq; try omega. apply t_update_eq.
  econstructor. apply ST_EqNumConstConst.
  replace (0 =? 0) with true. constructor. reflexivity. *)
Admitted.


(* Lemma about Some value *)
Lemma toNatG_GVNum_C : forall e1 n, (* more generic? *)
  e1 ==>* GSomeR (GVNumR (GNum n)) ->
  (e1 >>g= toNatG) ==>* GSomeR (GNum n).
Proof.
  intros.
  eapply multi_trans. apply GIf_Cond_R.
  - (* cond reduce to true*) eapply GGet_Map_C with (e1' := GSomeR (GVNumR (GNum n))) (v := GBool true); eauto.
    econstructor. apply GGet_fvalid_SomeR. constructor.
  - econstructor. constructor. unfold toNatG.
    eapply multi_trans. apply GIf_Cond_R. eapply tpe_GVNum_nat; eauto.
    econstructor. constructor. apply GSome_value_R; auto.
    eapply GGet_Map_C. eapply GGet_Map_C with (v := GVNumR (GNum n)); eauto.
    apply GGet_fdata_SomeR. auto. apply GGet_fval_GVNumR; auto.
Qed.

Hint Resolve toNatG_GVNum_C.

Definition req := oeq veq.

Hint Unfold req.

(* Theorem soundness1: forall e,
    exists g, (trans_exp e (GEmpty)) ==> g \/ (value g /\ req (evalExp e (σ0)) g).
Proof.
  intro e.
  induction e.
  - try (eexists; right; split; [ apply GSome_value; apply GVNum_value | constructor; constructor ]).
  - try (eexists; right; split; [ apply GSome_value; apply GVBool_value | constructor; constructor ]).
  - try (eexists; right; split; [ apply GSome_value; apply GVLoc_value | constructor; constructor ]).
  - inversion IHe1 as [ e1' IHe1' ]. inversion IHe1'; clear IHe1'.
    + (* step *) simpl.
      exists (((e1' >>g= toNatG) >>g=
         (fun a : gxp => (trans_exp e2 GEmpty >>g= toNatG) >>g= (fun b : gxp => GSome (GVNum (GPlus a b)))))).
      left. unfold GMatch. eapply LetG_C.
    + (* value *) *)

Theorem soundness1: forall e,
    exists g, (trans_exp e (GEmpty)) ==>* g /\ req (evalExp e (σ0)) g.
Proof with eauto.
  intro e.
  induction e; try (eexists; split; [ apply GSome_value_R; [ constructor; auto | auto ] | constructor; constructor]).
  eexists. split. simpl.
    apply GSome_value_R. apply GVNum_value_R; auto. constructor. auto. auto. [ constructor; auto | auto ]; auto.
  - inversion IHe1 as [te1 [Hs1 Heq1] ]; clear IHe1.
    inversion IHe2 as [te2 [Hs2 Heq2] ]; clear IHe2.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst.
    + (* e1 is Some *) inversion Hveq1; subst.
      * (* e1 is Nat *) inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst.
        -- (* e2 is Some *) inversion Hveq2; subst.
         ++ (* e2 is Nat *) exists (GSomeR (GVNum (GNum (n + n0)))). split.
          ** simpl. eapply LetG_val_C...
             apply GMatch_GSomeR_R...
             eapply GMatch_C... apply GMatch_GSomeR_R...
             eapply GSome_value_R...
              unfold GSome. admit.
          ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
         ++ (* e2 is Bool *) exists GNone; split; [ apply LetG_body_None; apply LetG_val_None; eapply toNatG_GVBool_None; eassumption | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]. 
         ++ (* e2 is Loc *) exists GNone; split; [ apply LetG_body_None; apply LetG_val_None; eapply toNatG_GVLoc_None; eassumption | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ].
        -- (* e2 is None *) exists GNone; split; [ apply LetG_body_None; apply LetG_val_None; apply GMatch_left_None; assumption | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
      * (* e1 is Bool *) exists GNone; split; [ apply LetG_val_None; eapply toNatG_GVBool_None; eassumption | simpl; rewrite <- Hval1; constructor].
      * (* e1 is Loc *) exists GNone; split; [ apply LetG_val_None; eapply toNatG_GVLoc_None; eassumption | simpl; rewrite <- Hval1; constructor].
    + (* e1 is None *) exists GNone; split; [ apply LetG_val_None; apply GMatch_left_None; assumption | simpl; rewrite <- Hval; constructor].
  -





inversion IHe1 as [ e1' IHe1' ]. inversion IHe1'; clear IHe1'.
    + (* step *) simpl.
      exists (((e1' >>g= toNatG) >>g=
         (fun a : gxp => (trans_exp e2 GEmpty >>g= toNatG) >>g= (fun b : gxp => GSome (GVNum (GPlus a b)))))).
      left. unfold GMatch. eapply LetG_C.
    + (* value *)

End Translation.