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
Import Adequacy.

Inductive gxp : Type :=
  | GSLoc : path -> gxp
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
  | GFixIndex : nat -> (nat -> gxp) -> gxp
  | GRepeat : nat -> gxp -> path -> (nat -> gxp) -> gxp -> gxp.

Definition fvalid : gxp := GLoc (LId (Id 0)). (* "$valid" *)
Definition fdata :  gxp := GLoc (LId (Id 1)). (* "$data"  *)
Definition ftpe :   gxp := GNum 0. (* "$tpe"   *)
Definition fval :   gxp := GNum 1. (* "$val"   *)

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

Definition GSomeR a : gxp := GMap (t_update beq_loc
   (t_update beq_loc empty_store
      (LId (Id 0)) (Some (GBool true)))
      (LId (Id 1)) (Some a)).

Definition GNoneR :=
 GMap (t_update beq_loc empty_store
   (LId (Id 0)) (Some (GBool false))).

Fixpoint trans_stmts (s: stmt) (sto: gxp) (c: path) { struct s }: gxp :=
  match s with
  | x ::= ALLOC =>
    GSome (GPut (GPut sto (GLoc (LNew c)) OEmpty) (GLoc (LId x)) (GPut OEmpty (GNum 0) (GVLoc (GLoc (LNew c)))))
  | e1[[e2]] ::= e3 =>
    LETG l <-- trans_exp e1 sto >>g= toLocG IN
    LETG n <-- trans_exp e2 sto >>g= toNatG IN
    LETG v <-- trans_exp e3 sto IN
    LETG o <-- GVSelect sto l IN
    GSome (GPut sto l (GPut o n v))
  | IF e THEN s1 ELSE s2 FI =>
    LETG b <-- trans_exp e sto >>g= toBoolG IN
    GIf b (trans_stmts s1 sto (PThen c)) (trans_stmts s2 sto (PElse c))
  | WHILE cnd DO s END =>
      LETG n <-- (GFixIndex 0
                   (fun (nstep : nat) =>
                     LETG nsto <-- GRepeat 0
                       (GNum nstep) c (fun (it: nat) => trans_stmts s (GSLoc c) (PWhile c it)) (GSome sto) IN
                         trans_exp cnd nsto
                   )) >>g= toNatG IN
      GRepeat 0 n c (fun (it: nat) => trans_stmts s (GSLoc c) (PWhile c it)) (GSome sto)
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

Inductive obj_value : gxp -> Prop :=
  | obj_none : obj_value GNoneR
  | obj_some : forall m, value (GObj m) -> obj_value (GSomeR (GObj m)).

Inductive store_value : gxp -> Prop :=
  | store_none : store_value GNoneR
  | store_some : forall m, value (GMap m) -> store_value (GSomeR (GMap m)).

Hint Constructors value store_value obj_value.

Reserved Notation " t '==>' t' " (at level 40).

Fixpoint bsub_path (p1 p2 : path) := match p2 with
  | PRoot => false
  | PFst p2' => beq_path p1 p2' || bsub_path p1 p2'
  | PSnd p2' => beq_path p1 p2' || bsub_path p1 p2'
  | PThen p2' => beq_path p1 p2' || bsub_path p1 p2'
  | PElse p2' => beq_path p1 p2' || bsub_path p1 p2'
  | PWhile p2' _ => beq_path p1 p2' || bsub_path p1 p2'
end.

Fixpoint subst (x : path) (s : gxp) (t : gxp) : gxp :=
  match t with
  | GSLoc i => if beq_path i x then s else t
  | GNum n => GNum n
  | GBool b => GBool b
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
  | GFixIndex i b => GFixIndex i (fun n => (subst x s (b n)))
  | GRepeat n i l b sto =>
      if beq_path l x then
        GRepeat n (subst x s i) l b (subst x s sto)
      else
        GRepeat n (subst x s i) l (fun n => subst x s (b n)) (subst x s sto)
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
  | ST_EqTrue : forall v1 v2,
          value v1 -> value v2 ->
          v1 = v2 ->
          GEq v1 v2
      ==> GBool true
  | ST_EqFalse : forall v1 v2,
          value v1 -> value v2 ->
          v1 <> v2 ->
          GEq v1 v2
      ==> GBool false
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
  | ST_FixIndexStep : forall i ob,
       GFixIndex i ob ==>
         LETG cnd <-- (ob i) IN
           GIf cnd
             (GFixIndex (i + 1) ob)
             (GSomeR (GVNumR (GNum i)))
  
  (* GRepeat *)
  | ST_RepeatNumIt : forall n n' l ob sto,
       n ==> n' ->
       GRepeat 0 n l ob sto ==> GRepeat 0 n' l ob sto
  | ST_RepeatStop : forall n l ob sto,
       GRepeat n (GNum 0) l ob sto ==> sto
  | ST_RepeatStep : forall n i l ob sto,
       GRepeat n (GNum (S i)) l ob sto ==>
         LETG osto <-- sto IN
           LETG nsto <-- (subst l osto (ob n)) IN
              GRepeat (n + 1) (GNum i) l ob nsto

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
       (* value (GObj m) -> *)
       value v3 ->
       GPut (GObj m) (GNum n) v3 ==> GObj (t_update beq_nat m n (Some v3))
  | ST_StorePut : forall l m v3,
       (* value (GMap m) -> *)
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

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Theorem step_deterministic : forall t t1 t2,
  t ==> t1 -> t ==> t2 -> t1 = t2.
Proof.
  (* intros t t1 t2 Ht1 Ht2.
  generalize dependent t2.
  induction Ht1; intros; inversion Ht2; subst;
     try (reflexivity); try (solve_by_inverts 2). *)
    




(* try (try(inversion Ht2; [ reflexivity | inversion H2 | inversion H3 ]) ;
                              try(inversion Ht2; subst; [inversion Ht1 | apply IHHt1 in H2; subst; reflexivity | inversion H1; subst; inversion Ht1]);
                              try(inversion Ht2; subst; [inversion Ht1 | inversion H; subst; inversion H3 | apply IHHt1 in H4; subst; reflexivity])).
  - inversion Ht2; subst. reflexivity. apply False_rec; auto. inversion H; subst; inversion H5. inversion H4; subst; inversion H6.
  - inversion Ht2; subst. apply False_rec; auto. reflexivity. inversion H; subst; inversion H5. inversion H0; subst; inversion H6.
  - inversion Ht2; subst; try(inversion H1; subst; inversion Ht1). apply IHHt1 in H2; subst; reflexivity. *)
Admitted.

Definition stuck (g : gxp): Prop :=
  (exists g', g ==> g') -> False.

Lemma value_stuck : forall v,
  value v -> stuck v.
Proof.
  intros. intro.
  destruct H0.
  inversion H; subst; inversion H0.
Qed.

Hint Resolve value_stuck.

Theorem multi_deterministic : forall t t1 t2,
  t ==>* t1 -> stuck t1 -> t ==>* t2 -> stuck t2 ->
  t1 = t2.
Proof. Admitted.
 
Lemma multi_trans : forall e1 e2 e3, e1 ==>* e2 -> e2 ==>* e3 -> e1 ==>* e3.
Proof.
  intros e1 e2 e3 H.
  induction H; [ eauto | intros; econstructor; eauto].
Qed.

Lemma multi_split_stuck : forall a b c,
  stuck c ->
  a ==>* b -> a ==>* c -> b ==>* c.
Proof. Admitted.

Lemma multi_split : forall a b c,
  a ==>* b -> a ==>* c -> (b ==>* c \/ c ==>* b).
Proof. Admitted.

(* ----- equivalence between IMP and FUN ----- *)

Inductive veq : val -> gxp -> Prop :=
| VEQ_Num : forall n,
    veq (VNum n) (GVNumR (GNum n))
| VEQ_Bool : forall n,
    veq (VBool n) (GVBoolR (GBool n))
| VEQ_Loc : forall l,
    veq (VLoc l) (GVLocR (GLoc l)).

Inductive oeq {X:Type} (peq: X -> gxp -> Prop): option X -> gxp -> Prop :=
| REQ_Some : forall v g,
    peq v g ->
    oeq peq (Some v) (GSomeR g)
| REQ_None :
    oeq peq None GNoneR.

Definition neq (n1: nat) (n2: gxp) := n2 ==>* GNum n1.
Definition leq (n1: loc) (n2: gxp) := n2 ==>* GLoc n1.


Definition objeq (o1 : obj) (o2 : gxp): Prop :=
  forall n1 n2, neq n1 n2 -> exists v, (GVSelect o2 n2) ==>* v /\ value v /\ oeq veq (o1 n1) v.

Definition seq (s1 : store) (s2 : gxp): Prop := 
  forall l1 l2, leq l1 l2 -> exists v, (GVSelect s2 l2) ==>* v /\ obj_value v /\ oeq objeq (s1 l1) v.

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
Lemma tloc_value : value tloc. Proof. constructor. Qed.

(* not sure why this is needed... auto do not prove value fdata otherwise *)
Hint Resolve fval_value fdata_value ftpe_value fvalid_value tloc_value.

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

Lemma value_preservation : forall m x y,
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

Lemma obj_value_preservation : forall m x y,
  value y ->
  value (GObj m) ->
  value (GObj (t_update Nat.eqb m x (Some y))).
Proof.
  intros. constructor.
  intros. destruct (nat_dec x x0); subst.
  - erewrite t_update_eq in H1. inversion H1; subst. assumption.
  - erewrite t_update_neq in H1; auto. inversion H0; subst. eapply H4. eassumption.
Qed.

Hint Resolve value_preservation obj_value_preservation OEmpty_value GEmpty_value.

Lemma GVNumR_value : forall n, value (GVNumR (GNum n)).
Proof.
  intro n.
  repeat (apply obj_value_preservation; auto).
Qed.

Lemma GVBoolR_value : forall n, value (GVBoolR (GBool n)).
Proof.
  intro n.
  repeat (apply obj_value_preservation; auto).
Qed.

Lemma GVLocR_value : forall n, value (GVLocR (GLoc n)).
Proof.
  intro n.
  repeat (apply obj_value_preservation; auto).
Qed.

Lemma GSomeR_value : forall v,
  value v -> value (GSomeR v).
Proof. intros. apply value_preservation; auto. Qed.

Lemma value_GSomeR : forall v,
  value (GSomeR v) -> value v.
Proof.
  intros v H.
  inversion H; subst. apply (H1 (LId (Id 1)) v).
  apply t_update_eq; auto.
Qed.

Lemma GNoneR_value : value GNoneR.
Proof. apply value_preservation; auto. Qed.

Hint Resolve GVNumR_value GVBoolR_value GVLocR_value GSomeR_value value_GSomeR GNoneR_value.

(* Reduction *)

Lemma GGet_Map_R : forall e1 e1' v,
  e1 ==>* e1' ->
  value v ->
  GGet e1 v ==>* GGet e1' v. 
Proof. intros.
  induction H.
  - constructor.
  - econstructor. apply ST_GetMap; eauto. assumption.
Qed.

Lemma GEq_left_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GEq e1 e2 ==>* GEq e1' e2.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. apply ST_Eq1. eassumption. assumption.
Qed. 

Lemma GGet_fdata_GSomeR_R : forall v,
  GGet (GSomeR v) fdata ==>* v.
Proof. econstructor. constructor. apply t_update_eq. constructor. Qed.

Lemma GGet_fdata_GSomeR_RR : forall e1 v,
  e1 ==>* GSomeR v ->
  GGet e1 fdata ==>* v.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
Qed.

Lemma GGet_fvalid_GSomeR_R : forall v, 
  GGet (GSomeR v) fvalid ==>* GBool true.
Proof. econstructor; constructor. rewrite t_update_neq; auto. Qed.

Lemma GGet_fvalid_GSomeR_RR : forall e1 v,
  e1 ==>* GSomeR v ->
  GGet e1 fvalid ==>* GBool true.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fvalid_GSomeR_R.
Qed.

Lemma GGet_fvalid_GNoneR_R : GGet GNoneR fvalid ==>* GBool false.
Proof. econstructor; constructor. apply t_update_eq; auto. Qed.

Lemma GGet_fvalid_GNoneR_RR : forall e1,
  e1 ==>* GNoneR ->
  GGet e1 fvalid ==>* GBool false.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fvalid_GNoneR_R.
Qed.

Lemma GGet_fval_GVNumR_R : forall n,
  GGet (GVNumR n) fval ==>* n.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_fval_GVNumR_RR : forall n e1,
  e1 ==>* GVNumR n ->
  GGet e1 fval ==>* n.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fval_GVNumR_R.
Qed.

Lemma GGet_fval_GVBoolR_R : forall n,
  GGet (GVBoolR n) fval ==>* n.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_fval_GVBoolR_RR : forall n e1,
  e1 ==>* GVBoolR n ->
  GGet e1 fval ==>* n.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fval_GVBoolR_R.
Qed.

Lemma GGet_fval_GVLocR_R : forall n,
  GGet (GVLocR n) fval ==>* n.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_fval_GVLocR_RR : forall n e1,
  e1 ==>* GVLocR n ->
  GGet e1 fval ==>* n.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fval_GVLocR_R.
Qed.

Lemma GGet_ftpe_GVNumR_R : forall n,
  GGet (GVNumR n) ftpe ==>* tnat.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. rewrite t_update_neq; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_ftpe_GVNumR_RR : forall n e1,
  e1 ==>* GVNumR n ->
  GGet e1 ftpe ==>* tnat.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_ftpe_GVNumR_R.
Qed.

Lemma GGet_ftpe_GVBoolR_R : forall b,
  GGet (GVBoolR b) ftpe ==>* tbool.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. rewrite t_update_neq; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_ftpe_GVBoolR_RR : forall n e1,
  e1 ==>* GVBoolR n ->
  GGet e1 ftpe ==>* tbool.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_ftpe_GVBoolR_R.
Qed.

Lemma GGet_ftpe_GVLocR_R : forall b,
  GGet (GVLocR b) ftpe ==>* tloc.
Proof.
  intros.
  econstructor. apply ST_ObjGet; auto. rewrite t_update_neq; auto. apply t_update_eq. constructor.
Qed.

Lemma GGet_ftpe_GVLocR_RR : forall n e1,
  e1 ==>* GVLocR n ->
  GGet e1 ftpe ==>* tloc.
Proof.
  intros.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_ftpe_GVLocR_R.
Qed.

Lemma GIf_Cond_R : forall e1 e1' e2 e3,
  e1 ==>* e1' ->
  GIf e1 e2 e3 ==>* GIf e1' e2 e3.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GIf_Cond_C : forall e1 e1' e2 e3 v,
  e1 ==>* e1' ->
  GIf e1' e2 e3 ==>* v ->
  GIf e1 e2 e3 ==>* v.
Proof.
  intros. eapply multi_trans; eauto. apply GIf_Cond_R; auto. 
Qed.

Lemma GIf_CondTrue_R : forall e1 e2 e2' e3,
  e1 ==>* GBool true ->
  e2 ==>* e2' ->
  GIf e1 e2 e3 ==>* e2'.
Proof.
  intros.
  eapply GIf_Cond_C; eauto.
  econstructor. constructor. assumption.
Qed.

Lemma GIf_CondFalse_R : forall e1 e2 e3 e3',
  e1 ==>* GBool false ->
  e3 ==>* e3' ->
  GIf e1 e2 e3 ==>* e3'.
Proof.
  intros.
  eapply GIf_Cond_C; eauto.
  econstructor. constructor. assumption.
Qed.

Lemma GNone_R : GNone ==>* GNoneR.
Proof.
  econstructor; [ apply ST_StorePut; auto | constructor].
Qed.

Hint Resolve GNone_R.

Lemma GSome_R : forall e1 v,
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

Lemma GVNum_R : forall e1 v,
  e1 ==>* v ->
  value v ->
  GVNum e1 ==>* GVNumR v.
Proof.
  intros e1 v He1 Hv.
  econstructor. apply ST_PutMap; auto; apply ST_ObjPut; auto.
  induction He1.
  - econstructor; [ apply ST_ObjPut; auto | constructor]. 
  - econstructor; try apply ST_PutValue; eauto.
Qed.

Lemma GVBool_R : forall e1 v,
  e1 ==>* v ->
  value v ->
  GVBool e1 ==>* GVBoolR v.
Proof.
  intros e1 v He1 Hv.
  econstructor. apply ST_PutMap; auto; apply ST_ObjPut; auto.
  induction He1.
  - econstructor; [ apply ST_ObjPut; auto | constructor]. 
  - econstructor; try apply ST_PutValue; eauto.
Qed.

Lemma GVLoc_R : forall e1 v,
  e1 ==>* v ->
  value v ->
  GVLoc e1 ==>* GVLocR v.
Proof.
  intros e1 v He1 Hv.
  econstructor. apply ST_PutMap; auto; apply ST_ObjPut; auto.
  induction He1.
  - econstructor; [ apply ST_ObjPut; auto | constructor]. 
  - econstructor; try apply ST_PutValue; eauto.
Qed.

Lemma GMatch_GSomeR_R : forall e1 e1' f v,
  e1 ==>* GSomeR e1' ->
  f (GGet e1 fdata) ==>* v ->
  (e1 >>g= f) ==>* v.
Proof. 
  intros.
  eapply GIf_CondTrue_R. eapply GGet_fvalid_GSomeR_RR; eauto. assumption.
Qed.

Lemma GMatch_GNoneR_R : forall e1 e2,
  e1 ==>* GNoneR ->
  (e1 >>g= e2) ==>* GNoneR.
Proof.
  intros.
  eapply GIf_CondFalse_R; auto. eapply GGet_fvalid_GNoneR_RR; eauto.
Qed.

Lemma GGet_GVBoolR_tpe_True_R : forall b e1,
  e1 ==>* GSomeR (GVBoolR b) ->
  GEq (GGet (GGet e1 fdata) ftpe) tbool ==>* GBool true.
Proof.
  intros n e1 He1.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVBoolR_R.
  econstructor. constructor; auto.
  constructor.
Qed.

Lemma GGet_GVBoolR_tpe_False_R : forall b e1 tpe,
  e1 ==>* GSomeR (GVBoolR b) ->
  value tpe ->
  tpe <> tbool ->
  GEq (GGet (GGet e1 fdata) ftpe) tpe ==>* GBool false.
Proof.
  intros n e1 tpe He1 Hv Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVBoolR_R.
  econstructor.
  inversion Hv; subst; apply ST_EqFalse; auto.
  constructor.
Qed.

Lemma toNatG_GVBoolR_None : forall e1 b, (* more generic? *)
  e1 ==>* GSomeR (GVBoolR b) ->
  (e1 >>g= toNatG) ==>* GNoneR.
Proof.
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVBoolR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma GGet_GVLocR_tpe_True_R : forall b e1,
  e1 ==>* GSomeR (GVLocR b) ->
  GEq (GGet (GGet e1 fdata) ftpe) tloc ==>* GBool true.
Proof.
  intros n e1 He1.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVLocR_R.
  econstructor. constructor; auto.
  constructor.
Qed.

Lemma GGet_GVLocR_tpe_False_R : forall b e1 tpe,
  e1 ==>* GSomeR (GVLocR b) ->
  value tpe ->
  tpe <> tloc ->
  GEq (GGet (GGet e1 fdata) ftpe) tpe ==>* GBool false.
Proof.
  intros n e1 tpe He1 Hv Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVLocR_R.
  econstructor.
  inversion Hv; subst; apply ST_EqFalse; auto.
  constructor.
Qed.

Lemma toNatG_GVLocR_None : forall e1 b,
  e1 ==>* GSomeR (GVLocR b) ->
  (e1 >>g= toNatG) ==>* GNoneR.
Proof. 
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVLocR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma GGet_GVNumR_tpe_True_R : forall n e1,
  e1 ==>* GSomeR (GVNumR (GNum n)) ->
  GEq (GGet (GGet e1 fdata) ftpe) tnat ==>* GBool true.
Proof.
  intros n e1 He1.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVNumR_R.
  econstructor. constructor; auto.
  constructor.
Qed.

Lemma GGet_GVNumR_tpe_False_R : forall b e1 tpe,
  e1 ==>* GSomeR (GVNumR b) ->
  value tpe ->
  tpe <> tnat ->
  GEq (GGet (GGet e1 fdata) ftpe) tpe ==>* GBool false.
Proof.
  intros n e1 tpe He1 Hv Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVNumR_R.
  econstructor.
  inversion Hv; subst; apply ST_EqFalse; auto.
  constructor.
Qed.

Lemma toNatG_GVNum_R : forall e1 n, 
  e1 ==>* GSomeR (GVNumR (GNum n)) ->
  (e1 >>g= toNatG) ==>* GSomeR (GNum n).
Proof.
  intros.
  eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondTrue_R; auto.
  eapply GGet_GVNumR_tpe_True_R; eassumption.
  apply GSome_R; auto. apply GGet_fval_GVNumR_RR.
  apply GGet_fdata_GSomeR_RR; auto.
Qed.

Lemma toLocG_GVNumR_None : forall e1 b,
  e1 ==>* GSomeR (GVNumR b) ->
  (e1 >>g= toLocG) ==>* GNoneR.
Proof. 
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVNumR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma toLocG_GVBoolR_None : forall e1 b,
  e1 ==>* GSomeR (GVBoolR b) ->
  (e1 >>g= toLocG) ==>* GNoneR.
Proof. 
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVBoolR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma toLocG_GVLoc_R : forall e1 l, 
  e1 ==>* GSomeR (GVLocR (GLoc l)) ->
  (e1 >>g= toLocG) ==>* GSomeR (GLoc l).
Proof.
  intros.
  eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondTrue_R; auto.
  eapply GGet_GVLocR_tpe_True_R; eassumption.
  apply GSome_R; auto. apply GGet_fval_GVLocR_RR.
  apply GGet_fdata_GSomeR_RR; auto.
Qed.

Lemma toBoolG_GVNumR_None : forall e1 b,
  e1 ==>* GSomeR (GVNumR b) ->
  (e1 >>g= toBoolG) ==>* GNoneR.
Proof. 
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVNumR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma toBoolG_GVLocR_None : forall e1 b,
  e1 ==>* GSomeR (GVLocR b) ->
  (e1 >>g= toBoolG) ==>* GNoneR.
Proof. 
  intros. eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondFalse_R; auto.
  eapply GGet_GVLocR_tpe_False_R; auto. eassumption.
  intro contra. inversion contra.
Qed.

Lemma toBoolG_GVBool_R : forall e1 b,
  e1 ==>* GSomeR (GVBoolR (GBool b)) ->
  (e1 >>g= toBoolG) ==>* GSomeR (GBool b).
Proof.
  intros.
  eapply GMatch_GSomeR_R; eauto.
  apply GIf_CondTrue_R; auto.
  eapply GGet_GVBoolR_tpe_True_R; eassumption.
  apply GSome_R; auto. apply GGet_fval_GVBoolR_RR.
  apply GGet_fdata_GSomeR_RR; auto.
Qed.

Hint Resolve toNatG_GVBoolR_None toNatG_GVLocR_None toLocG_GVNumR_None
             toLocG_GVBoolR_None toBoolG_GVNumR_None toBoolG_GVLocR_None toBoolG_GVBool_R.

Lemma LetImp_body_None : forall T U (e1 : option T),
  x ← e1 IN @None U = @None U.
Proof. intros. destruct e1; reflexivity. Qed.

Lemma LetG_body_GNoneR : forall e1 e2 v,
  e1 ==>* GNoneR \/ e1 ==>* GSomeR v -> 
  e2 ==>* GNoneR ->
  (LETG a <-- e1 IN e2) ==>* GNoneR.
Proof.
  intros.
  destruct H as [ Hn | Hs ].
  - apply GMatch_GNoneR_R; auto.
  - eapply GMatch_GSomeR_R; eauto.
Qed.


Lemma GPlus_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GPlus e1 e2 ==>* GPlus e1' e2.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GPlus_right_R : forall e2 e2' v,
  value v ->
  e2 ==>* e2' ->
  GPlus v e2 ==>*  GPlus v e2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor. apply ST_Plus2; eauto. assumption.
Qed.

Lemma GMinus_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GMinus e1 e2 ==>* GMinus e1' e2.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GMinus_right_R : forall e2 e2' v,
  value v ->
  e2 ==>* e2' ->
  GMinus v e2 ==>*  GMinus v e2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor. apply ST_Minus2; eauto. assumption.
Qed.

Lemma GMult_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GMult e1 e2 ==>* GMult e1' e2.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GMult_right_R : forall e2 e2' v,
  value v ->
  e2 ==>* e2' ->
  GMult v e2 ==>*  GMult v e2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor. apply ST_Mult2; eauto. assumption.
Qed.

Lemma GLt_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GLt e1 e2 ==>* GLt e1' e2.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GLt_right_R : forall e2 e2' v,
  value v ->
  e2 ==>* e2' ->
  GLt v e2 ==>*  GLt v e2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor. apply ST_Lt2; eauto. assumption.
Qed.

Lemma GHasField_Key_R : forall e1 e2 e2',
  e2 ==>* e2' ->
  GHasField e1 e2 ==>* GHasField e1 e2'.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. apply ST_HasFieldKey; eauto. assumption.
Qed.

Lemma GHasField_Map_R : forall e1 e1' v2,
  e1 ==>* e1' ->
  value v2 ->
  GHasField e1 v2 ==>* GHasField e1' v2.
Proof.
  intros e1 e1' v2 H Hv.
  induction H.
  - constructor.
  - econstructor. apply ST_HasFieldMap; eauto. assumption.
Qed.

Lemma GVSelect_OEmpty_R : forall e2 n2,
  e2 ==>* GNum n2 ->
  GVSelect OEmpty e2 ==>* GNoneR.
Proof.
  intros.
  eapply GIf_CondFalse_R.
  eapply multi_trans. eapply GHasField_Key_R. eassumption.
  econstructor. apply ST_ObjHasFieldFalse. reflexivity. constructor.
  auto.
Qed.

Lemma empty_objeq : objeq mt_obj OEmpty.
Proof.
  unfold objeq. intros.
  exists GNoneR.
  split. eapply GVSelect_OEmpty_R; eauto.
  split; auto.
  constructor.
Qed.

Hint Resolve empty_objeq.

Lemma GGet_Key_R : forall e1 e2 e2',
  e2 ==>* e2' ->
  GGet e1 e2 ==>* GGet e1 e2'.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. apply ST_GetKey; eauto. assumption.
Qed.

Lemma GPut_Key_R : forall e1 e2 e2' e3,
  e2 ==>* e2' ->
  GPut e1 e2 e3 ==>* GPut e1 e2' e3.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. apply ST_PutKey; eauto. assumption.
Qed.

Lemma GPut_Map_R : forall e1 e1' k2 e3,
  e1 ==>* e1' ->
  value k2 ->
  GPut e1 k2 e3 ==>* GPut e1' k2 e3.
Proof.
  intros.
  induction H.
  - constructor.
  - econstructor. apply ST_PutMap; eauto. assumption.
Qed.

Lemma GPut_Value_R : forall m1 k2 e3 e3',
  value m1 ->
  value k2 ->
  e3 ==>* e3' ->
  GPut m1 k2 e3 ==>* GPut m1 k2 e3'.
Proof.
  intros.
  induction H1.
  - constructor.
  - econstructor. apply ST_PutValue; eauto. assumption.
Qed.

Lemma GRepeat_NumIt_R : forall n n' a b c,
  n ==>* n' ->
  GRepeat 0 n a b c ==>* GRepeat 0 n' a b c.
Proof.
  intros n n' a b c H.
  induction H.
  - constructor.
  - econstructor. apply ST_RepeatNumIt; eauto. assumption.
Qed.

Lemma GIf_value : forall e1 e2 e3 v,
  value v ->
  GIf e1 e2 e3 ==>* v ->
  (e1 ==>* GBool true /\ e2 ==>* v) \/ (e1 ==>* GBool false /\ e3 ==>* v).
Proof.
  intros.
  inversion H0; subst.
Admitted. 

Lemma GIf_C : forall e1 e1' e2 e2' e3 e3' v,
  e1 ==>* e1' ->
  e2 ==>* e2' ->
  e3 ==>* e3' ->
  value v ->
  GIf e1' e2' e3' ==>* v ->
  GIf e1 e2 e3 ==>* v.
Proof.
  intros.
  assert ((e1' ==>* GBool true /\ e2' ==>* v) \/ (e1' ==>* GBool false /\ e3' ==>* v)) as Hcond. apply GIf_value; auto.
  destruct Hcond as [ [ Ht Hthen] | [ Hf Helse ] ].
  - eapply multi_trans. eapply GIf_Cond_R. eapply multi_trans; eauto.
    econstructor. constructor. eapply multi_trans; eauto.
  - eapply multi_trans. eapply GIf_Cond_R. eapply multi_trans; eauto.
    econstructor. constructor. eapply multi_trans; eauto.
Qed.

Lemma GHasField_C : forall e1 e1' e2 e2' v,
  e1 ==>* e1' ->
  e2 ==>* e2' ->
  value v ->
  GHasField e1' e2' ==>* v ->
  GHasField e1 e2 ==>* v.
Proof. Admitted.

Lemma GGet_C : forall e1 e1' e2 e2' v,
  e1 ==>* e1' ->
  e2 ==>* e2' ->
  value v ->
  GGet e1' e2' ==>* v ->
  GGet e1 e2 ==>* v.
Proof. Admitted.

Lemma func_eq_value_eq : forall { X Y : Type } (f g : X -> Y) (v : X),
  f = g -> (f v) = (g v).
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma GSome_GNoneR_contra : forall e1,
  (* value e1 -> *)
  GSome e1 ==>* GNoneR -> False.
Proof.
  (* intros.
  assert (GSome e1 ==>* GSomeR e1). apply GSome_R; auto. constructor.
  assert (GNoneR = GSomeR e1). eapply multi_deterministic; eauto.
  unfold stuck. intro contra. destruct contra. inversion H2.
  unfold stuck. intro contra. destruct contra. inversion H2.
  inversion H2.
  apply func_eq_value_eq with (v := LId (Id 0)) in H4.
  inversion H4.
Qed. *)
Admitted.

Lemma GVSelect_C_GNoneR : forall e1 e1' e2 e2',
   e1 ==>* e1' ->
   e2 ==>* e2' ->
   GVSelect e1' e2' ==>* GNoneR ->
   GVSelect e1 e2 ==>* GNoneR.
Proof.
  intros.
  assert (((GHasField e1' e2') ==>* GBool true /\ (GSome (GGet e1' e2')) ==>* GNoneR) \/
          ((GHasField e1' e2') ==>* GBool false /\ GNone ==>* GNoneR)) as Hcond.
  apply GIf_value; auto.
  destruct Hcond as [ [ Ht Hthen] | [ Hf Helse ] ].
  - apply False_rec. eapply  GSome_GNoneR_contra. eassumption.
  - eapply GIf_C; eauto. eapply GHasField_C with (v := GBool false); eauto. constructor.
    econstructor. constructor. constructor.
Qed.

Lemma GSome_C_GSomeR : forall e1 e1' v,
  e1 ==>* e1' ->
  GSome e1' ==>* GSomeR v->
  GSome e1 ==>* GSomeR v.
Proof.
  unfold GSome.
  intros e1 e1' v Hse1 Hs.
Admitted.

Lemma GVSelect_C_GSomeR : forall e1 e1' e2 e2' v,
   e1 ==>* e1' ->
   e2 ==>* e2' ->
   GVSelect e1' e2' ==>* GSomeR v ->
   GVSelect e1 e2 ==>* GSomeR v.
Proof.


Admitted.

Lemma GMatch_C : forall e1 e1' f v,
  e1 ==>* e1' ->
  (e1' >>g= f) ==>* v ->
  (e1 >>g= f) ==>* v.
Proof. Admitted.

Lemma trans_stmts_C : forall s c sto sto' v,
  store_value v ->
  sto ==>* sto' ->
  trans_stmts s sto' c ==>* v ->
  trans_stmts s sto' c ==>* v.
Proof. Admitted.

Lemma GNoneR_R : forall a,
  GNoneR ==>* a -> a = GNoneR.
Proof.
  intros. inversion H; subst; auto. inversion H0.
Qed.

Lemma value_deterministic : forall a b,
  a ==>* b -> store_value a -> a = b.
Proof.
  intros. inversion H; subst; auto. 
  inversion H0; subst. inversion H1. inversion H1.
Qed.

Lemma GRepeat_GNoneR_R : forall n i b c,
   GRepeat n (GNum i) c b GNoneR ==>* GNoneR.
Proof.
   intros. destruct i.
   - econstructor. constructor. constructor. 
   - econstructor. apply ST_RepeatStep. eapply GMatch_GNoneR_R; eauto. constructor.
Qed.

Hint Resolve value_deterministic GRepeat_GNoneR_R.  

(* Lemma GRepeat_C : forall n m c s sto sto' v,
  store_value v ->
  sto ==>* sto' ->
  store_value sto' ->
  GRepeat n (GNum m) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) sto' ==>* v ->
  GRepeat n (GNum m) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) sto ==>* v.
Proof.
  intros.
  destruct m.
  - apply multi_split with (b:= sto') in H2.
    destruct H2.
    + econstructor. constructor. eapply multi_trans; eassumption.
    + eapply value_deterministic in H; eauto. subst.
      econstructor. constructor. eassumption.
    + econstructor. constructor. constructor.
  - econstructor. constructor.
    apply multi_split with (b:= (sto >>g=
     (fun osto : gxp =>
       subst c osto ((fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) n) >>g=
         (fun nsto : gxp => GRepeat (n + 1) (GNum m) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) nsto)))) in H2.
    destruct H2.
    + inversion H; inversion H1; subst.
      * eapply GMatch_GNoneR_R. assumption.
      * eapply GMatch_GSomeR_R. eassumption.
        apply multi_split with (b:= (subst c (GGet sto fdata) (b n) >>g= (fun nsto : gxp => GRepeat (n + 1) (GNum m) c b nsto))) in H2.
        destruct H2; auto. apply GNoneR_R in H2. rewrite H2. constructor.
        eapply GMatch_GSomeR_R. constructor. *)

Lemma seq_C : forall st1 st2 st2',
  st2 ==>* st2' ->
  seq st1 st2' ->
  seq st1 st2.
Proof.
  intros st1 st2 st2' Hstep Hseq.
  intros l1 l2 Hleq.
  destruct (Hseq l1 l2) as [ obj [ Hsel [ Hv Hoeq ] ] ]; auto.
  exists obj.
  inversion Hoeq as [ no ng Hobjeq Hgsome | Hnone ]; subst; clear Hoeq.
  - split. 
    + eapply GVSelect_C_GSomeR. eauto. econstructor. auto.
    + split; auto.
  - split. 
    + eapply GVSelect_C_GNoneR. eauto. econstructor. auto.
    + split; auto.
Qed.

Definition req := oeq veq.

Theorem soundness_exp: forall e s1 s2,
    (* store_value (GSomeR s2) ->  *)
    seq s1 s2 ->
    exists g, (trans_exp e s2) ==>* g /\ req (evalExp e s1) g.
Proof.
  intros e s1 s2 Hseq.
  induction e.
  - eexists; split. apply GSome_R. apply GVNum_R. constructor. constructor. auto. constructor. constructor.
  - eexists; split. apply GSome_R. apply GVBool_R. constructor. constructor. auto. constructor. constructor.
  - eexists; split. apply GSome_R. apply GVLoc_R. constructor. constructor. auto. constructor. constructor.
  - inversion IHe1 as [te1 [Hs1 Heq1] ]; clear IHe1.
    inversion IHe2 as [te2 [Hs2 Heq2] ]; clear IHe2.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst.
    + (* e1 is Some *) inversion Hveq1; subst; try (
          exists GNoneR; split; [ eapply GMatch_GNoneR_R; eauto | simpl; rewrite <- Hval1; constructor]).
      (* e1 is Nat *) assert ((trans_exp e1 s2 >>g= toNatG) ==>* GSomeR (GNum n)) as Hre1. { apply toNatG_GVNum_R; eauto. }
         inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst.
      * (* e2 is Some *) inversion Hveq2; subst; try (exists GNoneR; split;
           [ eapply GMatch_GSomeR_R; [ apply toNatG_GVNum_R; eauto | eapply GMatch_GNoneR_R; eauto]
           | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]).
         (* e2 is Nat *) exists (GSomeR (GVNumR (GNum (n + n0)))). split.
          -- simpl.
           assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n0)) as Hre2. { apply toNatG_GVNum_R; eauto. }
           repeat (eapply GMatch_GSomeR_R; eauto).
           eapply GSome_R; eauto. apply GVNum_R; eauto.
           eapply multi_trans. eapply GPlus_R. apply GGet_fdata_GSomeR_RR; eauto.
           eapply multi_trans; auto. eapply GPlus_right_R; auto. apply GGet_fdata_GSomeR_RR; eauto.
           econstructor; constructor.
          -- simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat apply GMatch_GNoneR_R; auto | simpl; rewrite <- Hval; constructor].
  - inversion IHe1 as [te1 [Hs1 Heq1] ]; clear IHe1.
    inversion IHe2 as [te2 [Hs2 Heq2] ]; clear IHe2.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst.
    + (* e1 is Some *) inversion Hveq1; subst; try (
          exists GNoneR; split; [ eapply GMatch_GNoneR_R; eauto | simpl; rewrite <- Hval1; constructor]).
      (* e1 is Nat *) assert ((trans_exp e1 s2 >>g= toNatG) ==>* GSomeR (GNum n)) as Hre1. { apply toNatG_GVNum_R; eauto. }
         inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst.
      * (* e2 is Some *) inversion Hveq2; subst; try (exists GNoneR; split;
           [ eapply GMatch_GSomeR_R; [ apply toNatG_GVNum_R; eauto | eapply GMatch_GNoneR_R; eauto]
           | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]).
         (* e2 is Nat *) exists (GSomeR (GVNumR (GNum (n - n0)))). split.
          -- simpl.
           assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n0)) as Hre2. { apply toNatG_GVNum_R; eauto. }
           repeat (eapply GMatch_GSomeR_R; eauto).
           eapply GSome_R; eauto. apply GVNum_R; eauto.
           eapply multi_trans. eapply GMinus_R. apply GGet_fdata_GSomeR_RR; eauto.
           eapply multi_trans; auto. eapply GMinus_right_R; auto. apply GGet_fdata_GSomeR_RR; eauto.
           econstructor; constructor.
          -- simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat apply GMatch_GNoneR_R; auto | simpl; rewrite <- Hval; constructor].
  - inversion IHe1 as [te1 [Hs1 Heq1] ]; clear IHe1.
    inversion IHe2 as [te2 [Hs2 Heq2] ]; clear IHe2.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst.
    + (* e1 is Some *) inversion Hveq1; subst; try (
          exists GNoneR; split; [ eapply GMatch_GNoneR_R; eauto | simpl; rewrite <- Hval1; constructor]).
      (* e1 is Nat *) assert ((trans_exp e1 s2 >>g= toNatG) ==>* GSomeR (GNum n)) as Hre1. { apply toNatG_GVNum_R; eauto. }
         inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst.
      * (* e2 is Some *) inversion Hveq2; subst; try (exists GNoneR; split;
           [ eapply GMatch_GSomeR_R; [ apply toNatG_GVNum_R; eauto | eapply GMatch_GNoneR_R; eauto]
           | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]).
         (* e2 is Nat *) exists (GSomeR (GVNumR (GNum (n * n0)))). split.
          -- simpl.
           assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n0)) as Hre2. { apply toNatG_GVNum_R; eauto. }
           repeat (eapply GMatch_GSomeR_R; eauto).
           eapply GSome_R; eauto. apply GVNum_R; eauto.
           eapply multi_trans. eapply GMult_R. apply GGet_fdata_GSomeR_RR; eauto.
           eapply multi_trans; auto. eapply GMult_right_R; auto. apply GGet_fdata_GSomeR_RR; eauto.
           econstructor; constructor.
          -- simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat apply GMatch_GNoneR_R; auto | simpl; rewrite <- Hval; constructor].
  - admit (* same as above *).
  - admit (* same as above *).
  - admit (* same as above *).
  - admit (* same as above *).
  - inversion IHe1 as [te1 [Hs1 Heq1] ]; clear IHe1.
    inversion IHe2 as [te2 [Hs2 Heq2] ]; clear IHe2.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst; clear Heq1.
    + (* e1 is Some *) inversion Hveq1; subst; clear Hveq1; try (
          exists GNoneR; split; [ eapply GMatch_GNoneR_R; eauto | simpl; rewrite <- Hval1; constructor]).
      (* e1 is Loc *) assert ((trans_exp e1 s2 >>g= toLocG) ==>* GSomeR (GLoc l)) as Hre1. { apply toLocG_GVLoc_R; eauto. }
         inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst; clear Heq2.
      * (* e2 is Some *) inversion Hveq2; subst; clear Hveq2; try (exists GNoneR; split;
           [ eapply GMatch_GSomeR_R; [ apply toLocG_GVLoc_R; eauto | eapply GMatch_GNoneR_R; eauto]
           | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]).
         (* e2 is Nat *) simpl.
         assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n)) as Hre2. { apply toNatG_GVNum_R; eauto. }
         (* extract object witness from store *)
         destruct (Hseq l (GGet (trans_exp e1 s2 >>g= toLocG) fdata)) as [ obj_w [Hs_store [ Hv_obj Hveq ] ] ]; auto. {
           eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
         } 
         (* obj_w is some or none *)
         inversion Hveq as [ no ng Hobjeq Hoeq Hgsome | Hnone ]; subst; clear Hveq.
         -- (* object exists *)
           destruct (Hobjeq n (GGet (trans_exp e2 s2 >>g= toNatG) fdata)) as [ val_v [ Hs_obj [ Hv_v Hveq ] ] ]; subst; auto.  {
             eapply multi_trans. eapply GGet_Map_R. eassumption. constructor. apply GGet_fdata_GSomeR_R.
           }
           exists val_v. split.
           ** eapply GMatch_GSomeR_R. eassumption. eapply GMatch_GSomeR_R. eassumption.
              eapply GMatch_GSomeR_R. eassumption.
              inversion Hveq; subst.
              eapply GVSelect_C_GSomeR; eauto.
              eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. constructor.
              eapply GVSelect_C_GNoneR; eauto.
              eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. constructor.
           ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. rewrite <- Hoeq. auto.
         -- (* object does NOT exists *) 
           exists GNoneR. split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
              eapply GMatch_GNoneR_R; eauto.
           ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. rewrite <- Hnone. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat (apply GMatch_GNoneR_R; auto) | simpl; rewrite <- Hval; constructor].
Admitted.

Definition gstore_update (st : loc -> option gxp) (x : loc) (v : gxp) :=
  t_update beq_loc st x (Some v).

Definition gobj_update (st : nat -> option gxp) (x : nat) (v : gxp) :=
  t_update beq_nat st x (Some v).

Lemma obj_value_value : forall v,
  obj_value v -> value v.
Proof.
  intros v H. inversion H; auto.
Qed.

Lemma obj_value_obj : forall v,
  obj_value (GSomeR v) -> exists m, v = GObj m.
Proof.
  intros v Hov.
  inversion Hov; subst.
  - apply func_eq_value_eq with (v0 := LId (Id 0)) in H0. inversion H0.
  - apply func_eq_value_eq with (v0 := LId (Id 1)) in H. inversion H; subst.
    exists m; auto.
Qed.

Lemma oeq_seq_seq : forall s1 s2,
  oeq seq (Some s1) (GSomeR s2) -> seq s1 s2.
Proof.
  intros s1 s2 H. inversion H; subst.
  apply func_eq_value_eq with (v := LId (Id 1)) in H1.
  inversion H1; subst. assumption.
Qed.

Lemma veq_value : forall v1 v2, veq v1 v2 -> value v2.
Proof.
  intros v1 v2 H.
  inversion H; auto.
Qed.

Hint Resolve obj_value_value veq_value oeq_seq_seq.

Lemma GHasField_True_Some : forall o n,
  GHasField (GObj o) (GNum n) ==>* GBool true -> exists v, (o n) = Some v.
Proof.
  intros o n H.
  inversion H; subst. inversion H0; subst.
  - destruct (o n) as [ o' | ]. exists o'; auto. apply False_rec; auto.
  - inversion H1; subst. inversion H2.
  - inversion H5.
  - inversion H6.
Qed.

Lemma GHasField_True_preservation : forall e1 o n n1 n2 v,
  e1 ==>* GObj (gobj_update o n1 v) ->
  n ==>* (GNum n2) ->
  (GHasField (GObj o) (GNum n2) ==>* GBool true \/ n1 = n2) ->
  GHasField e1 n ==>* GBool true.
Proof.
  intros e1 o n n1 n2 v He1 Hn H.
  eapply multi_trans. eapply GHasField_Key_R; eauto.
  eapply multi_trans. eapply GHasField_Map_R; eauto.
  destruct H as [ Hstep | Heq ]; subst.
  - apply GHasField_True_Some in Hstep.
    econstructor. constructor. unfold gobj_update.
    destruct (nat_dec n1 n2); subst.
    rewrite t_update_eq. intro contra; inversion contra.
    rewrite t_update_neq; auto. inversion Hstep as [ w Hsome ].
    rewrite Hsome. intro contra; inversion contra.
    constructor.
  - econstructor. constructor. unfold gobj_update.
    rewrite t_update_eq. intro contra; inversion contra.
    constructor.
Qed.

Lemma GGet_eq : forall e1 o n1 n v,
  n1 ==>* GNum n ->
  e1 ==>* GObj (gobj_update o n v) ->
  GGet e1 n1 ==>* v.
Proof.
  intros e1 o n1 n v Hnr Her.
  eapply multi_trans. eapply GGet_Key_R; eauto.
  eapply multi_trans. eapply GGet_Map_R; eauto.
  econstructor. constructor. unfold gobj_update. apply t_update_eq.
  constructor.
Qed.

(* Lemma GVSelect_GSomeR_GHasField_True : forall e1 e2 v,
  GVSelect e1 e2 ==>* GSomeR v ->
  GHasField e1 e2 ==>* GBool true /\ (
    (exists o, exists n, e1 ==>* GObj o /\ e2 ==>* GNum n /\ o n = Some v) \/
    (exists m, exists l, e1 ==>* GMap m /\ e2 ==>* GLoc l /\ m l = Some v)
  ).
Proof. Admitted. *)
 
Lemma objeq_preservation : forall n o1 o2 v1 v2,
  objeq o1 (GObj o2) ->
  veq v1 v2 ->
  objeq (obj_update o1 n v1) (GObj (gobj_update o2 n v2)).
Proof.
  (* intros.
  intros n1 n2 Hneq.
  destruct (nat_dec n n1); subst.
  - (* n = n1 *) exists (GSomeR v2); split.
    eapply multi_trans. apply GIf_CondTrue_R.
    eapply multi_trans. eapply GHasField_Key_R; eauto.
    eapply multi_trans.
    eapply GHasField_True_conservation with (n2 := n1) (n1 := n1); auto; try constructor.
    constructor.
    eapply GSome_R with (v := v2); eauto.
    eapply GGet_eq; eauto. constructor. constructor.
    split. apply GSomeR_value; eauto.
    unfold obj_update. rewrite t_update_eq. constructor. auto.
  - (* n <> n1 *) destruct (H n1 n2) as [ obj [ Hstep [ Hobjv Hoeq ] ] ]; auto.
    inversion Hoeq; subst; clear Hoeq.
    + apply GVSelect_GSomeR_GHasField_True in Hstep. 
      exists (GSomeR g); split.
      * eapply multi_trans. apply GIf_CondTrue_R.
        eapply multi_trans. eapply GHasField_Key_R; eauto.
        eapply GHasField_True_conservation with (n1 := n) (n2 := n1); eauto; try constructor.
        admit.
        constructor. eapply GSome_R with (v := g); eauto.
        eapply multi_trans. eapply GGet_Key_R; eauto.
        eapply multi_step. constructor. 
        
    
    exists obj. split.
    eapply multi_trans. apply GIf_CondTrue_R.
    eapply multi_trans. eapply GHasField_Key_R; eauto.
    econstructor. constructor. unfold gobj_update. rewrite t_update_eq.
    intro contra; inversion contra.
    constructor.
    eapply GSome_R with (v := v2); eauto.
    eapply multi_trans. eapply GGet_Key_R; eauto.
    eapply multi_step. constructor. unfold gobj_update. apply t_update_eq.
    constructor. constructor.
    split. apply GSomeR_value; eauto.
    unfold obj_update. rewrite t_update_eq. constructor. auto. *)
Admitted.

Lemma objeq_obj_value : forall o1 o2,
  value o2 ->
  objeq o1 o2 -> obj_value (GSomeR o2).
Proof.
  intros o1 o2 Hv Heq.
  inversion Hv; subst.
  - destruct (Heq 0 (GNum 0)) as [ w [ Hstep [ Hvx _ ] ] ]. constructor.
    inversion Hstep; subst. inversion Hvx.
    inversion H; subst. inversion H5; subst; [ inversion H4 | inversion H6].
  - destruct (Heq 0 (GNum 0)) as [ w [ Hstep [ Hvx _ ] ] ]. constructor.
    inversion Hstep; subst. inversion Hvx.
    inversion H; subst. inversion H5; subst; [ inversion H4 | inversion H6].
  - destruct (Heq 0 (GNum 0)) as [ w [ Hstep [ Hvx _ ] ] ]. constructor.
    inversion Hstep; subst. inversion Hvx.
    inversion H; subst. inversion H5; subst; [ inversion H4 | inversion H6].
  - constructor. auto.
  - destruct (Heq 0 (GNum 0)) as [ w [ Hstep [ Hvx _ ] ] ]. constructor.
    inversion Hstep; subst. inversion Hvx.
    inversion H0; subst. inversion H6; subst; [ inversion H5 | inversion H7].
Qed.

Lemma seq_preservation : forall l o1 o2 s1 s2,
  seq s1 (GMap s2) ->
  value o2 ->
  objeq o1 o2 ->
  seq (store_update s1 l o1) (GMap (gstore_update s2 l o2)).
Proof.
  intros.
  intros l1 l2 Hleq.
  destruct (loc_dec l l1); subst.
  - (* l = l1 *)
    assert (obj_value (GSomeR o2)). { eapply objeq_obj_value; eauto. }
    exists (GSomeR o2). split.
    eapply multi_trans. apply GIf_CondTrue_R.
    eapply multi_trans. eapply GHasField_Key_R; eauto.
    econstructor. constructor. unfold gstore_update. rewrite t_update_eq.
    intro contra; inversion contra.
    constructor.
    eapply GSome_R.
    eapply multi_trans. eapply GGet_Key_R; eauto.
    eapply multi_step. constructor. unfold gstore_update. apply t_update_eq.
    constructor. auto. constructor.
    split; auto.
    unfold store_update. rewrite t_update_eq. constructor; auto.
  - (* l != l1 *) admit.
Admitted.

Hint Resolve seq_preservation objeq_preservation.

Lemma store_value_value : forall v,
  store_value v -> value v.
Proof.
  intros v H. inversion H; auto.
Qed.

Hint Resolve store_value_value.

Lemma store_value_map : forall v,
  store_value (GSomeR v) -> exists m, v = GMap m.
Proof.
  intros v Hsv.
  inversion Hsv; subst.
  - apply func_eq_value_eq with (v0 := LId (Id 0)) in H0. inversion H0.
  - apply func_eq_value_eq with (v0 := LId (Id 1)) in H. inversion H; subst.
    exists m; auto.
Qed.

Lemma oeq_falso : forall e,
  oeq seq (Some e) GNoneR -> False.
Proof.
  intros e contra. inversion contra; subst.
  apply func_eq_value_eq with (v := LId (Id 0)) in H0. inversion H0.
Qed.

Lemma alloc_R : forall st2 m2 c i,
  st2 ==>* (GMap m2) ->
  value (GMap m2) ->
  GSome (GPut (GPut st2 (GLoc (LNew c)) OEmpty) (GLoc (LId i)) (GPut OEmpty (GNum 0) (GVLoc (GLoc (LNew c))))) ==>*
  GSomeR (GMap
     (t_update beq_loc (t_update beq_loc m2 (LNew c) (Some OEmpty)) (LId i)
        (Some (GObj (t_update Nat.eqb (t_empty None) 0 (Some (GVLocR (GLoc (LNew c))))))))).
Proof.
  intros.
  apply GSome_R; auto.
  eapply multi_trans. apply GPut_Map_R; auto.
  eapply multi_trans. apply GPut_Map_R; eauto.
  eapply multi_step. apply ST_StorePut; auto. constructor.
  eapply multi_trans. apply GPut_Value_R; auto.
  eapply multi_trans. apply GPut_Value_R; auto.
  apply GVLoc_R. constructor. auto.
  eapply multi_step. apply ST_ObjPut; auto. constructor.
  eapply multi_step. apply ST_StorePut; auto. constructor.
Qed.

(* Lemma idx1_soundness_GSomeR : forall k m n e s st1 st2 st2' m2 p,
  k <= n ->
  idx1 (n - k) m (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some (Some n) ->
  st2 ==>* (GMap m2) ->
  seq st1 (GMap m2) ->
  store_value (GSomeR st2') ->
  GRepeat 0 (GNum (n - k)) p (fun it : nat => LETG sto <-- trans_stmts s (GSLoc (PWhile p it)) (PWhile p it) IN sto) st2 ==> st2' ->
  ((GFixIndex (n - k) p (trans_exp e (GSLoc p))
     (fun nstep : nat => GRepeat 0 (GNum nstep) p (fun it : nat => LETG sto <-- trans_stmts s (GSLoc (PWhile p it)) (PWhile p it) IN sto) st2) st2) >>g= toNatG)
        ==>* GSomeR (GNum n).
Proof.
  induction k; intros.
  - admit.
  - eapply GMatch_GSomeR_R.
    eapply multi_trans. apply GFixIndex_Body_R; eauto.
    econstructor. apply ST_FixIndexStep; auto. *)

Lemma idx_soundness_GSomeR : forall e s st1 st2 m2 p m n,
  idx m (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some (Some n) ->
   st2 ==>* (GSomeR (GMap m2)) ->
   seq st1 (GMap m2) ->
   (GFixIndex 0 (fun nstep : nat =>
     GRepeat 0 (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) st2 >>g= (fun nsto : gxp => trans_exp e nsto)) >>g= toNatG)
        ==>* GSomeR (GNum n).
Proof. Admitted.

(* Lemma idx1_soundness_GNoneR : forall e s st1 st2 m2 p k m n,
  k <= n ->
  idx1 (n - k) m (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some (Some n) ->
   st2 ==>* (GMap m2) ->
   seq st1 (GMap m2) ->
   (GFixIndex (n - k) p (trans_exp e (GSLoc p))
     (fun nstep : nat => GRepeat 0 (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc (PWhile p it)) (PWhile p it)) st2) st2)
        ==>* GSomeR (GVNumR (GNum n)).
Proof. Admitted. *)

Lemma idx_soundness_GNoneR : forall e s st1 st2 m2 p m,
  idx m (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some None ->
   st2 ==>* (GSomeR (GMap m2)) ->
   seq st1 (GMap m2) ->
  (GFixIndex 0 (fun nstep : nat =>
     GRepeat 0 (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) st2 >>g= (fun nsto : gxp => trans_exp e nsto)) >>g= toNatG)
        ==>* GNoneR.
Proof. Admitted.

Lemma beq_path_eq: forall c, true = beq_path c c.
Proof.
  intro c.
  induction c; auto.
  simpl. rewrite <- IHc. simpl. apply beq_nat_refl.
Qed.

Lemma subst_trans_exp_commute : forall e c sto sto',
  subst c sto (trans_exp e sto') = trans_exp e (subst c sto sto').
Proof.
  intro e.
  induction e; intros;
     try reflexivity;
     try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
     try (simpl; rewrite IHe; reflexivity).
Qed.

Inductive sub_rel : path -> path -> Prop :=
 | s_PThen : forall c, sub_rel c (PThen c)
 | s_PElse : forall c, sub_rel c (PElse c)
 | s_PFst : forall c, sub_rel c (PFst c)
 | s_PSnd : forall c, sub_rel c (PSnd c)
 | s_PWhile : forall c n, sub_rel c (PWhile c n).

Lemma bsub_path_sub_rel : forall c c' c'',
  sub_rel c c'' ->
  bsub_path c' c = true -> bsub_path c' c'' = true.
Proof. intros. inversion H; subst; simpl; rewrite H0; apply orb_true_r. Qed.

Hint Constructors sub_rel.
Hint Resolve bsub_path_sub_rel.

Lemma bsub_trans : forall c' c c'',
  sub_rel c c'' ->
  bsub_path c'' c' = true -> bsub_path c c' = true.
Proof.
  intro c'.
  induction c'; intros;
    try (simpl; simpl in H0; apply orb_prop in H0;
    apply orb_true_intro; right;
    try apply andb_false_intro1;
    destruct H0; [
      inversion H; subst; destruct c'; inversion H0; simpl; rewrite H2; try reflexivity;
      apply andb_prop in H2; destruct H2 as [ He _]; rewrite He; reflexivity |
      eauto ]);
    try (inversion H0).
Qed.

Lemma bsub_true_beq_false_path : forall c c',
  bsub_path c' c = true -> beq_path c c' = false.
Proof.
  intro c.
  induction c; intros c' H; destruct c'; auto;
    try (simpl; simpl in H; apply orb_prop in H;
    try apply andb_false_intro1;
    destruct H; [
      apply IHc; destruct c; inversion H; simpl;
      try rewrite H; try (apply andb_prop in H; destruct H as [ Ht _ ]; rewrite Ht); reflexivity | 
      apply IHc; eapply bsub_trans; try eassumption; auto ]).
Qed.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Lemma subst_trans_stmts_commute : forall s c c' sto sto',
   bsub_path c' c = true ->
   subst c' sto (trans_stmts s sto' c) = trans_stmts s (subst c' sto sto') c.
Proof.
  intro s. 
  induction s; intros;
     try (simpl; repeat (rewrite subst_trans_exp_commute); try reflexivity);
     try (rewrite IHs1; eauto; rewrite IHs2; eauto; simpl; try (rewrite IHs1; eauto); reflexivity).
  assert (H' := H).
  apply bsub_true_beq_false_path in H. repeat rewrite H.
  assert (
    (fun n0 : nat => subst c' sto (trans_stmts s (GSLoc c) (PWhile c n0))) =
    (fun n0 : nat => trans_stmts s (GSLoc c) (PWhile c n0))). {
    apply functional_extensionality.
    intro x. rewrite IHs; eauto. simpl. rewrite H; auto.
  }
  assert (
    (fun n : nat =>
       GIf (GGet
          (GRepeat 0 (GNum n) c (fun n0 : nat => subst c' sto (trans_stmts s (GSLoc c) (PWhile c n0)))
             (GPut (GPut (GMap empty_store) (GLoc (LId (Id 0))) (GBool true)) (GLoc (LId (Id 1))) (subst c' sto sto')))
                (GLoc (LId (Id 0))))
        (subst c' sto
           (trans_exp e (GGet (GRepeat 0 (GNum n) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome sto')) fdata)))
        (GPut (GMap empty_store) (GLoc (LId (Id 0))) (GBool false))) =
    (fun n : nat =>
       GIf (GGet (GRepeat 0 (GNum n) c (fun n0 : nat => trans_stmts s (GSLoc c) (PWhile c n0))
             (GSome (subst c' sto sto'))) (GLoc (LId (Id 0))))
          (trans_exp e (GGet (GRepeat 0 (GNum n) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it))
                      (GSome (subst c' sto sto'))) fdata))
         (GPut (GMap empty_store) (GLoc (LId (Id 0))) (GBool false)))). {
      apply functional_extensionality.
      intro x. rewrite subst_trans_exp_commute. simpl. rewrite H. rewrite H0. reflexivity.
  }
  repeat rewrite H1. repeat rewrite H0. reflexivity.
Qed.

Lemma subst_comm : forall s c c' sto,
  bsub_path c' c = true ->
  subst c' sto (LETG sto <-- trans_stmts s (GSLoc c') c IN sto) = LETG sto <--trans_stmts s sto c IN sto.
Proof.
  intros.
  simpl.
  rewrite subst_trans_stmts_commute; auto. simpl. rewrite <- beq_path_eq. reflexivity.
Qed.

(* Lemma GRepeat_split_loop_aux : forall k i c s sto0 sto1 sto2 sto3,
  k <= i ->
  sto0 ==>* sto1 ->
  value sto1 -> value sto2 ->
(*   (trans_stmts s sto1 (PWhile c (i - k)) >>g= (fun sto : gxp => sto)) ==>* sto2 -> *)
  GRepeat (i - k) (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it) >>g= (fun ns : gxp => ns)) sto1 ==>* sto2 ->
  GRepeat i (GNum 1) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it) >>g= (fun ns : gxp => ns)) sto2 ==> sto3 ->
  GRepeat (i - k) (GNum (S k)) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it) >>g= (fun ns : gxp => ns)) sto0 ==>* sto3.
Proof.
  intro k.
  induction k; intros i c s sto0 sto1 sto2 sto3 Hki Hstep0 Hv1 Hv2 (* Hstep *) Hfst Hsnd.
  - admit.
  - inversion Hsnd; subst.
    + inversion H5.
    + inversion Hv2; subst; inversion H5.
    + eapply multi_trans. apply GRepeat_Body_R. eassumption.
      econstructor. apply ST_RepeatStep; auto.
      replace (i - S k + 1) with (i - k); try omega.
      eapply multi_trans. apply GRepeat_Body_R.
      rewrite subst_comm. constructor. simpl; rewrite <- beq_path_eq. reflexivity.
      rewrite subst_comm; try (simpl; rewrite <- beq_path_eq; reflexivity).
      
      induction Hfst; subst.
      * inversion Hv2.
      * 
      eapply IHk.
        omega.
        
        auto.
        constructor.
    auto.
    apply  
Admitted. *)

(* Lemma GRepeat_split_loop : forall i n c s sto1 sto1' sto2 sto2' sto3,
  i <= n ->
  sto1 ==>* sto1' -> sto2 ==>* sto2' ->
  store_value sto1' -> store_value sto2' -> store_value sto3 ->
  (exists sto, trans_stmts s (GGet sto1 fdata) (PWhile c (n - i)) ==>* GSomeR sto) ->
  GRepeat (n - i) (GNum i) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) sto1 ==>* sto2 ->
  trans_stmts s (GGet sto2 fdata) (PWhile c (n - i)) sto2 ==>* sto3 ->
  GRepeat (n - i) (GNum (S i)) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) sto1 ==>* sto3.
Proof. *)
(*   induction i; intros.
  - replace (n - 0) with n; try omega.
    apply multi_split_stuck with (c := sto1) in H4; auto.
    apply multi_split_stuck with (b := sto1) (c := sto3) in H5; auto.
    eapply value_deterministic in H4; eauto; subst. auto.
    
    econstructor. constructor. assumption.
  - econstructor. constructor. inversion H1; subst.
    + eapply multi_trans. eapply GMatch_GNoneR_R; eauto. constructor.
      apply multi_split with (b := GNoneR) (c := sto2) in H5; auto.
      apply GNoneR_R in H5; subst.
      apply multi_split with (b := GNoneR) in H6; auto.
      econstructor. constructor. eapply GMatch_GNoneR_R. auto.
    + destruct H4.
      eapply GMatch_GSomeR_R; eauto. constructor.
      rewrite subst_trans_stmts_commute; simpl; rewrite <- beq_path_eq; try reflexivity.
      eapply GMatch_C. try eassumption.
      eapply GMatch_GSomeR_R; eauto. constructor.
      replace (n - S i + 1) with (n - i); try omega.
      eapply IHi.





      eapply multi_split in H5; auto; try eassumption.
      eapply multi_trans. eassumption.
      eapply GMatch_GSomeR_R.
      rewrite subst_trans_stmts_commute; simpl; rewrite <- beq_path_eq; try reflexivity.
      eassumption.
      replace (n - S i + 1) with (n - i); try omega.
      eapply IHi.*)
     
    
     (*       eapply GMatch_R; eauto. constructor.


    inversion H3; subst. inversion H1.
    inversion H5; subst. inversion H13.
    econstructor. constructor. inversion H0; subst.
    + eapply multi_trans. eapply GMatch_GNoneR_R. constructor.
      apply GNoneR_R in H6; subst.
      apply multi_split with (b := GNoneR) (c := sto2) in H3.
      destruct H3. 

    assert (sto2 = GSomeR sto1). admit.
    rewrite <- H8.
  -  *)
(* Admitted. *)

Lemma idx1_some_eval_some : forall k n i m e s st1 p,
  k <= n ->
  idx1 (n - k) (m + k) (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some (Some n) ->
   n >= i -> i >= (n - k) -> exists st0,
     evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some (Some st0).
Proof.
  induction k; intros.
  - destruct m. inversion H0. simpl in H0.
    replace (n - 0) with n in H0; try omega.
    remember (evalLoop e s st1 p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S m))) as loop.
    destruct loop; try inversion H0; clear H0.
    destruct o; try inversion H4; clear H4.
    replace i with n; try omega.
    exists s0. rewrite <- Heqloop. reflexivity.
  - replace (m + S k) with (S m + k) in H0; try omega.
    simpl in H0.
    remember (evalLoop e s st1 p (n - S k) (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))) as loop.
    destruct loop; try inversion H0; clear H0.
    destruct o; try inversion H4; clear H4.
    destruct (〚 e 〛 (s0)); try inversion H3; clear H3.
    destruct v; try inversion H4; clear H4.
    destruct b; simpl in H3.
    + replace (n - S k + 1) with (n - k) in H3; try omega.
      inversion H2; subst.
      * exists s0. rewrite <- Heqloop. reflexivity.
      * eapply IHk with (n := n); eauto; try omega.
    + inversion H3; clear H3. apply False_rec. omega.
Qed.  

Lemma idx_some_eval_some : forall n i e s st1 p fuel,
  idx fuel (fun (i : nat) =>
    sigma'' ↩ evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(fuel))
       IN match evalExp e sigma'' >>= toBool with
          | Some b => Some (Some (negb b))
          | None => Some None
          end) = Some (Some n) ->
   n >= i -> exists st0,
      evalLoop e s st1 p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(fuel)) = Some (Some st0).
Proof.
  intros.
  edestruct (idx1_some_eval_some n n i fuel); try omega.
  eapply idx1_more_val_inv with (n := fuel); try omega.
  replace (n - n) with 0; eauto; try omega.
  exists x; auto.
Qed.

Theorem soundness_stmts: forall s c st1 st1' st2 m2 fuel,
  st2 ==>* (GMap m2) ->
  seq st1 (GMap m2) ->
  value (GMap m2) ->
  evalStmt s st1 c (S fuel) = Some st1' ->
  exists g, (trans_stmts s st2 c) ==>* g /\ store_value g /\ oeq seq st1' g.
Proof.
  intros s.
  induction s; intros c st1 st1' st2 m2 fuel Hstep Hseq Hvs2 HsImp.
  - eexists. split.
    + simpl.  apply alloc_R; eauto.
    + split; auto.
      inversion HsImp; subst. constructor.
      apply seq_preservation. apply seq_preservation; auto.
      apply obj_value_preservation; auto.
      apply objeq_preservation; auto.
  - assert (seq st1 st2) as HseqNR. { eapply seq_C; eauto. }
    destruct (soundness_exp e st1 st2) as [ ew [ Hes Heeq ] ]; auto.
    destruct (soundness_exp e0 st1 st2) as [ e0w [ He0s He0eq ] ]; auto.
    destruct (soundness_exp e1 st1 st2) as [ e1w [ He1s He1eq ] ]; auto.
    inversion Heeq as [ ev1 ev2 Heveq Hesome | Hnone ]; subst.
    + (* e is Some *) inversion Heveq; subst;
       try (eexists GNoneR; split; [
         eapply GMatch_GNoneR_R; eauto |
         split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; inversion HsImp; subst; constructor]).
      (* e is Loc *) assert ((trans_exp e st2 >>g= toLocG) ==>* GSomeR (GLoc l)) as Hre. { apply toLocG_GVLoc_R; eauto. }
      inversion He0eq as [ e0v1 e0v2 He0veq He0some | Hnone ]; subst.
      * (* e0 is Some *) inversion He0veq; subst;
         try (eexists GNoneR; split; [
           eapply GMatch_GSomeR_R; eauto; eapply GMatch_GNoneR_R; eauto |
           split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; rewrite <- He0some in HsImp; inversion HsImp; subst; constructor]).
        (* e0 is Num *)
        assert ((trans_exp e0 st2 >>g= toNatG) ==>* GSomeR (GNum n)) as Hre0. { apply toNatG_GVNum_R; eauto. }
        inversion He1eq as [ e1v1 e1v2 He1veq He1some | Hnone ]; subst.
        -- (* e1 is Some *)
         (* extract object witness from store *)
         destruct (HseqNR l (GGet (trans_exp e st2 >>g= toLocG) fdata)) as [ obj_w [Hs_store [ Hv_obj Hveq ] ] ]. {
          eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
         }
         (* obj_w is some or none *)
         inversion Hveq as [ no ng Hobjeq Hoeq Hgsome | Hnone ]; subst; clear Hveq.
         ++ (* object exists *)
           assert (exists m, ng = GObj m) as Hobj. { apply obj_value_obj; auto. }
           inversion Hobj; subst.
           eexists. split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
            eapply GMatch_GSomeR_R; eauto.
            apply GSome_R.
            eapply multi_trans. eapply GPut_Key_R.
            eapply multi_trans. eapply GGet_Map_R. eassumption. constructor. eapply GGet_fdata_GSomeR_R.
            eapply multi_trans. eapply GPut_Map_R; eauto.
            eapply multi_trans. eapply GPut_Value_R; auto.
            eapply multi_trans. eapply GPut_Key_R.
            eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
            eapply multi_trans. eapply GPut_Map_R; eauto.
            eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
            eapply multi_trans. eapply GPut_Value_R; auto.
            eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
            eapply multi_step. constructor; eauto. apply multi_refl.
            eapply multi_step. constructor; eauto. apply multi_refl.
            eauto 8.
           ** split; eauto 8.
            simpl in HsImp. rewrite <- Hesome in HsImp. rewrite <- He0some in HsImp.
            rewrite <- He1some in HsImp. simpl in HsImp. rewrite <- Hoeq in HsImp.
            inversion HsImp; subst.
            constructor.
            apply seq_preservation; eauto.
            apply objeq_preservation; auto.
         ++ (* object does NOT exists *)
           exists GNoneR; split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
              eapply GMatch_GNoneR_R; eauto.
           ** split; auto.
              simpl in HsImp. rewrite <- Hesome in HsImp. rewrite <- He0some in HsImp.
              rewrite <- He1some in HsImp. simpl in HsImp. rewrite <- Hnone in HsImp. inversion HsImp; subst. constructor.
        -- (* e1 is None *) exists GNoneR; split; [
         eapply GMatch_GSomeR_R; eauto; eapply GMatch_GSomeR_R; eauto; eapply GMatch_GNoneR_R; eauto |
         split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; rewrite <- He0some in HsImp; rewrite <- Hnone in HsImp; inversion HsImp; subst; constructor ].
      * (* e0 is None *) exists GNoneR; split; [
         eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) |
         split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; rewrite <- Hnone in HsImp; inversion HsImp; subst; constructor ].
    + (* e is None *) exists GNoneR; split; [ repeat (eapply GMatch_GNoneR_R; eauto) |
         split; auto; simpl in HsImp; rewrite <- Hnone in HsImp; inversion HsImp; subst; constructor ].
  - assert (seq st1 st2) as HseqNR. { eapply seq_C; eauto. }
    destruct (soundness_exp e st1 st2) as [ ew [ Hes Heeq ] ]; auto.
    inversion Heeq as [ ev1 ev2 Heveq Hesome | Hnone ]; subst.
    + (* e is Some *) inversion Heveq; subst;
      try (eexists GNoneR; split; [
         eapply GMatch_GNoneR_R; eauto |
         split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; inversion HsImp; subst; constructor]).
      (* e is Bool *)
      assert ((trans_exp e st2 >>g= toBoolG) ==>* GSomeR (GBool n)) as Hre0. { apply toBoolG_GVBool_R; eauto. }
      destruct n.
      * (* e is True *) destruct (IHs1 (PThen c) st1 st1' st2 m2 fuel) as [ res1 [ Hres1s [ Hres1sv Hres1eq ] ] ]; auto. {
          simpl in HsImp. rewrite <- Hesome in HsImp. apply HsImp.
        }
        eexists res1. split; auto.
        eapply GMatch_GSomeR_R; eauto.
        eapply multi_trans. eapply GIf_CondTrue_R.
        eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
        eassumption. apply multi_refl.
      * (* e is False *) destruct (IHs2 (PElse c) st1 st1' st2 m2 fuel) as [ res2 [ Hres2s [ Hres2sv Hres2eq ] ] ]; auto. {
          simpl in HsImp. rewrite <- Hesome in HsImp. apply HsImp.
        }
        eexists res2. split; auto.
        eapply GMatch_GSomeR_R; eauto.
        eapply multi_trans. eapply GIf_CondFalse_R.
        eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
        eassumption. apply multi_refl.
    + (* e is None *) exists GNoneR; split; [ repeat (eapply GMatch_GNoneR_R; eauto) |
         split; auto; simpl in HsImp; rewrite <- Hnone in HsImp; inversion HsImp; subst; constructor ].
  - simpl in HsImp. simpl.
    remember (idx (S fuel)
            (fun i : nat =>
             σ' ↩ evalLoop e s st1 c i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel))
             IN match (〚 e 〛 (σ')) >>= toBool with
                | Some b => Some (Some (negb b))
                | None => Some None
                end)) as Hidx.
    destruct Hidx.
    + destruct o.
      * destruct st1'.
        -- (* assert (Heval_some := HeqHidx). symmetry in Heval_some. apply idx_some_eval_some in Heval_some with (i := ). *)
          assert (forall k st1'' i, i <= k -> k <= n -> evalLoop e s st1 c i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1'' ->
                 exists g, GRepeat 0 (GNum i) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
                /\ store_value g /\ oeq seq st1'' g). {
(*             intro k.
            induction k.
            - intros st1'' i Hik Hkn H. inversion Hik; subst; inversion H; subst. exists (GSomeR (GMap m2)); split; auto.
              eapply multi_trans. eapply multi_step. apply ST_RepeatStop.
              eapply GSome_R; eauto. constructor.
            - intros st1'' i Hik Hkn H.
              inversion Hik; subst; clear Hik; [ auto | apply IHk; auto; omega ].
              
              assert (Heval_some := HeqHidx). symmetry in Heval_some. apply idx_some_eval_some with (i := k) in Heval_some; try omega.
              destruct Heval_some as [ stk [ Hloop Hguard] ].
              simpl in H.
              rewrite Hloop in H.
              rewrite Hguard in H. simpl in H.
              destruct (IHk (Some stk) k) as [ gstore [ Hgloop [ Hsv Hg_seq ] ] ]; auto; try omega.
              inversion Hg_seq as [ A kstore |  ]; subst.
              assert (exists m, kstore = GMap m) as Hmap. { apply store_value_map; auto. }
              destruct Hmap as [ mkstore ]; subst.
              destruct (IHs (PWhile c k) stk st1'' (GMap mkstore) mkstore fuel) as [ fstore [ Hbloop [ Hfsv Hfeq ] ] ]; eauto. constructor. *)
              admit.
                (* inversion Hfsv; subst.
              + exists GNoneR; split; auto.
                



              remember (evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(fuel))) as loop.
              destruct loop; try inversion H; clear H.
              destruct o; try inversion H1; subst; clear H1.
            + remember (〚 e 〛 (s0)) as cond. admit. *)
              (* destruct cond; try inversion H0; clear H0.
              destruct v; try inversion H1; clear H1.
              destruct b; try inversion H0; clear H0.
              destruct (IHk s0 k) as [ gstore [ Hloop [ Hsv Hg_seq ] ] ]; auto.
              assert (exists m, gstore = GMap m) as Hmap. { apply store_value_map; auto. }
              destruct Hmap as [ mgstore ]; subst.
              destruct (IHs (PWhile c k) s0 (Some st1'') (GMap mgstore) mgstore fuel) as [ fstore [ Hbloop [ Hfsv Hfeq ] ] ]; eauto. constructor.
              destruct Hfsv as [ | mfstore ].
              * apply False_rec. eapply oeq_falso; eassumption.
              * exists (GMap mfstore); split; eauto.
                eapply multi_trans. eapply GRepeat_Body_R; eauto.
                eapply GRepeat_split_loop with (sto2 := (GMap mgstore)); eauto.
                econstructor. apply ST_RepeatStep; auto.
                eapply multi_trans. apply GRepeat_Body_R with (sto' := (GMap mfstore)).
                rewrite subst_comm. eapply GMatch_GSomeR_R; eauto.
                eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
                simpl; rewrite <- beq_path_eq. reflexivity.
                econstructor. apply ST_RepeatStop; eauto. constructor. 
            + exists GNone; split.
              eapply multi_trans. eapply GRepeat_Body_R; eauto.
              eapply GSome_R; eauto.
              econstructor. apply ST_RepeatStep; eauto.
              eapply GMatch_GSomeR_R. constructor.
              eapply multi_trans. eapply GRepeat_Body_R; eauto.
              rewrite subst_trans_stmts_commute; simpl; rewrite <- beq_path_eq; try reflexivity. *)
         }
         apply (H n (Some s0) n) in HsImp; try omega.
         destruct HsImp as [ gstore [Hloop [ Hsv Hg_seq ] ] ].
         inversion Hg_seq; subst.
         symmetry in HeqHidx. eapply idx_soundness_GSomeR in HeqHidx; eauto.
         
         exists (GSomeR g). split; auto.
         eapply GMatch_GSomeR_R; eauto.
         eapply multi_trans. eapply GRepeat_NumIt_R; eauto.
         eapply multi_trans. eapply GGet_Map_R; eauto.
         eapply GGet_fdata_GSomeR_R; eauto.
         assumption. apply GSome_R; auto.
        -- assert (Heval_some := HeqHidx). symmetry in Heval_some. apply idx_some_eval_some with (i := n) in Heval_some; try omega.
           rewrite HsImp in Heval_some. inversion Heval_some. inversion H.
      * inversion HsImp; subst.
        exists GNoneR. split; eauto.
        eapply GMatch_GNoneR_R; eauto. 
        eapply idx_soundness_GNoneR; eauto.
        eapply GSome_R; auto.
    + inversion HsImp.
  - remember (〚s1〛(st1, PFst c)(S fuel)) as step1.
    destruct step1.
    + destruct (IHs1 (PFst c) st1 o st2 m2 fuel) as [ res1 [ Hres1s [ Hres1sv Hres1eq ] ] ]; auto; clear IHs1.
      inversion Hres1eq as [st1'' st2''| B]; subst.
      * (* first statement returns Some *)
        assert (exists m, st2'' = GMap m) as Hmap. { apply store_value_map; auto. }
        inversion Hmap as [ m'']; subst; clear Hmap.
        destruct (IHs2 (PSnd c) st1'' st1' (GGet (trans_stmts s1 st2 (PFst c)) fdata) m'' fuel) as [ res2 [ Hres2s [ Hres2sv Hres2eq ] ] ]; auto. {
          eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
        }
        simpl in HsImp. rewrite <- Heqstep1 in HsImp. auto.
        exists res2. simpl. split; auto.
        eapply GMatch_GSomeR_R; eauto.
      * (* first statement returns None *)
        exists GNoneR. split; [ eapply GMatch_GNoneR_R; eauto | split; auto; simpl in HsImp; rewrite <- Heqstep1 in HsImp; inversion HsImp; constructor ].
    + (* timeout case *) simpl in HsImp. rewrite <- Heqstep1 in HsImp. inversion HsImp.
  - inversion HsImp; subst.
    exists (GSomeR (GMap m2)); split; auto. apply GSome_R; auto.
  - inversion HsImp; subst. exists GNoneR; auto.
Admitted.

End Translation.