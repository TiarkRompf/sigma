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
  | GRepeat : gxp -> path -> (nat -> gxp) -> gxp -> gxp.

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

Definition GGetOrElse (scrutinee: gxp) (default: gxp): gxp :=
  GIf (GGet scrutinee fvalid) (GGet scrutinee fdata) default.

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
      let n:= GFixIndex 0
                   (fun (nstep : nat) =>
                     GGetOrElse (LETG nsto <-- GRepeat (GNum nstep)
                       c (fun (it: nat) => trans_stmts s (GSLoc c) (PWhile c it)) (GSome sto) IN
                         (trans_exp cnd nsto >>g= toBoolG)) (GBool false)
                   ) in
      LETG sto' <-- GRepeat n c (fun (it: nat) => trans_stmts s (GSLoc c) (PWhile c it)) (GSome sto) IN
        LETG _ <-- trans_exp cnd sto' >>g= toBoolG IN GSome sto'
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
  | GRepeat i l b sto =>
      if beq_path l x then
        GRepeat (subst x s i) l b (subst x s sto)
      else
        GRepeat (subst x s i) l (fun n => subst x s (b n)) (subst x s sto)
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
  | ST_EqConstConst : forall n1 n2,
          GEq (GNum n1) (GNum n2)
      ==> GBool (n1 =? n2)
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
         GIf (ob i)
           (GFixIndex (i + 1) ob)
           (GNum i)

  (* GRepeat *)
  | ST_RepeatNumIt : forall n n' l ob sto,
       n ==> n' ->
       GRepeat n l ob sto ==> GRepeat n' l ob sto
  | ST_RepeatStop : forall l ob sto,
       GRepeat (GNum 0) l ob sto ==> sto
  | ST_RepeatStep : forall i l ob sto,
       GRepeat (GNum (S i)) l ob sto ==>
         LETG nsto <-- GRepeat (GNum i) l ob sto IN
           (subst l nsto (ob i))

  (* GHasField *)
  | ST_ObjHasFieldTrue : forall n m,
       m n <> None ->
       GHasField (GObj m) (GNum n) ==> GBool true
  | ST_ObjHasFieldFalse : forall n m,
       m n = None ->
       GHasField (GObj m)(GNum n)  ==> GBool false
  | ST_StoHasFieldTrue : forall l m,
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

(* Theorem step_deterministic : forall t t1 t2,
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
Admitted. *)

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

(* Theorem multi_deterministic : forall t t1 t2,
  t ==>* t1 -> stuck t1 -> t ==>* t2 -> stuck t2 ->
  t1 = t2.
Proof. Admitted. *)
 
Lemma multi_trans : forall e1 e2 e3, e1 ==>* e2 -> e2 ==>* e3 -> e1 ==>* e3.
Proof.
  intros e1 e2 e3 H.
  induction H; [ eauto | intros; econstructor; eauto].
Qed.

(* (* Lemma multi_split_stuck : forall a b c,
  stuck c ->
  a ==>* b -> a ==>* c -> b ==>* c.
Proof. Admitted. *)

Lemma multi_split : forall a b c,
  a ==>* b -> a ==>* c -> (b ==>* c \/ c ==>* b).
Proof. Admitted. *)

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
  forall n1 n2, neq n1 n2 -> ((GHasField o2 (GNum n1)) ==>* GBool true /\ exists v1 v2, (GGet o2 (GNum n1)) ==>* v2 /\ o1 n1 = Some v1 /\ veq v1 v2)
                             \/ ((GHasField o2 (GNum n1)) ==>* GBool false /\ o1 n1 = None).

Definition seq (s1 : store) (s2 : gxp): Prop := 
  forall l1 l2, leq l1 l2 -> ((GHasField s2 (GLoc l1)) ==>* GBool true /\ exists o1 o2, (GGet s2 (GLoc l1)) ==>* (GObj o2) /\ value (GObj o2) /\ s1 l1 = Some o1 /\ objeq o1 (GObj o2))
                             \/ ((GHasField s2 (GLoc l1)) ==>* GBool false /\ s1 l1 = None).

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
  (GNum tpe) <> tbool ->
  GEq (GGet (GGet e1 fdata) ftpe) (GNum tpe) ==>* GBool false.
Proof.
  intros n e1 tpe He1 Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVBoolR_R.
  econstructor. apply ST_EqConstConst; auto.
  destruct (nat_dec 1 tpe); subst.
  - apply False_rec. auto.
  - rewrite <- Nat.eqb_neq in H. rewrite H. constructor.
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
  (GNum tpe) <> tloc ->
  GEq (GGet (GGet e1 fdata) ftpe) (GNum tpe) ==>* GBool false.
Proof.
  intros n e1 tpe He1 Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVLocR_R.
  econstructor. apply ST_EqConstConst; auto.
  destruct (nat_dec 2 tpe); subst.
  - apply False_rec. auto.
  - rewrite <- Nat.eqb_neq in H. rewrite H. constructor.
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
  (GNum tpe) <> tnat ->
  GEq (GGet (GGet e1 fdata) ftpe) (GNum tpe) ==>* GBool false.
Proof.
  intros n e1 tpe He1 Htpe.
  eapply multi_trans. apply GEq_left_R.
  repeat (apply GGet_Map_R; auto). eassumption.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_Map_R; auto. apply GGet_fdata_GSomeR_R.
  eapply multi_trans. apply GEq_left_R.
  apply GGet_ftpe_GVNumR_R.
  econstructor. apply ST_EqConstConst; auto.
  destruct (nat_dec 0 tpe); subst.
  - apply False_rec. auto.
  - rewrite <- Nat.eqb_neq in H. rewrite H. constructor.
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

Lemma GEq_R : forall e1 e1' e2,
  e1 ==>* e1' ->
  GEq e1 e2 ==>* GEq e1' e2.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
Qed.

Lemma GEq_right_R : forall e2 e2' v,
  value v ->
  e2 ==>* e2' ->
  GEq v e2 ==>*  GEq v e2'.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor. apply ST_Eq2; eauto. assumption.
Qed.

Lemma GNot_R : forall e1 e1',
  e1 ==>* e1' ->
  GNot e1 ==>* GNot e1'.
Proof.
  intros. induction H.
  - constructor.
  - econstructor. constructor. eassumption. assumption.
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
  unfold objeq. intros. right. split.
  - econstructor. apply ST_ObjHasFieldFalse. reflexivity. constructor.
  - reflexivity.
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
  GRepeat n a b c ==>* GRepeat n' a b c.
Proof.
  intros n n' a b c H.
  induction H.
  - constructor.
  - econstructor. apply ST_RepeatNumIt; eauto. assumption.
Qed.

Lemma func_eq_value_eq : forall { X Y : Type } (f g : X -> Y) (v : X),
  f = g -> (f v) = (g v).
Proof.
  intros. rewrite H. reflexivity.
Qed.

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

Lemma GRepeat_GNoneR_R : forall i b c,
   GRepeat (GNum i) c b GNoneR ==>* GNoneR.
Proof.
   intros. induction i.
   - econstructor. apply ST_RepeatStop. constructor. 
   - econstructor. apply ST_RepeatStep. eapply GMatch_GNoneR_R; eauto.
Qed.

Hint Resolve value_deterministic GRepeat_GNoneR_R.

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

Lemma seq_C : forall st1 st2 st2',
  st2 ==>* st2' ->
  seq st1 st2' ->
  seq st1 st2.
Proof.
  intros st1 st2 st2' Hstep Hseq.
  intros l1 l2 Hleq.
  destruct (Hseq l1 (GLoc l1)) as [ [ Hhf [ obj1 [ obj2 [ Hsel [ Hsome Hoeq ] ] ] ] ] | [ Hhf Heq ] ]; auto. constructor.
  - left. split.
    + eapply multi_trans. eapply GHasField_Key_R. econstructor.
      eapply multi_trans. eapply GHasField_Map_R; eauto. auto.
    + exists obj1. exists obj2. split; auto.
      eapply multi_trans. eapply GGet_Key_R. econstructor.
      eapply multi_trans. eapply GGet_Map_R; eauto. auto.
  - right. split; auto.
    eapply multi_trans. eapply GHasField_Map_R; eauto. auto.
Qed.

Definition req := oeq veq.

Lemma GNoneR_GSomeR_neq : forall v,
  t_update beq_loc empty_store (LId (Id 0)) (Some (GBool false)) =
    t_update beq_loc (t_update beq_loc empty_store (LId (Id 0)) (Some (GBool true)))
      (LId (Id 1)) (Some v) -> False.
Proof.
  intros.
  apply func_eq_value_eq with (v0 := LId (Id 0)) in H. inversion H.
Qed.

Hint Resolve GNoneR_GSomeR_neq.

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
         (* e2 is Nat *) exists (GSomeR (GVBoolR (GBool (n <? n0)))). split.
          -- simpl.
           assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n0)) as Hre2. { apply toNatG_GVNum_R; eauto. }
           repeat (eapply GMatch_GSomeR_R; eauto).
           eapply GSome_R; eauto. apply GVBool_R; eauto.
           eapply multi_trans. eapply GLt_R. apply GGet_fdata_GSomeR_RR; eauto.
           eapply multi_trans; auto. eapply GLt_right_R; auto. apply GGet_fdata_GSomeR_RR; eauto.
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
         (* e2 is Nat *) exists (GSomeR (GVBoolR (GBool (n =? n0)))). split.
          -- simpl.
           assert ((trans_exp e2 s2 >>g= toNatG) ==>* GSomeR (GNum n0)) as Hre2. { apply toNatG_GVNum_R; eauto. }
           repeat (eapply GMatch_GSomeR_R; eauto).
           eapply GSome_R; eauto. apply GVBool_R; eauto.
           eapply multi_trans. eapply GEq_R. apply GGet_fdata_GSomeR_RR; eauto.
           eapply multi_trans; auto. eapply GEq_right_R; auto. apply GGet_fdata_GSomeR_RR; eauto.
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
      (* e1 is Bool *) assert ((trans_exp e1 s2 >>g= toBoolG) ==>* GSomeR (GBool n)) as Hre1. { apply toBoolG_GVBool_R; eauto. }
         inversion Heq2 as [ e2imp e2fun Hveq2 Hval2 | Hval ]; subst.
      * (* e2 is Some *) inversion Hveq2; subst; try (exists GNoneR; split;
           [ eapply GMatch_GSomeR_R; [ apply toBoolG_GVBool_R; eauto | eapply GMatch_GNoneR_R; eauto]
           | simpl; rewrite <- Hval2; rewrite LetImp_body_None; constructor ]). simpl.
         (* e2 is Bool *) assert ((trans_exp e2 s2 >>g= toBoolG) ==>* GSomeR (GBool n0)) as Hre2. { apply toBoolG_GVBool_R; eauto. }
        destruct n.
        -- (* e1 is true *) exists (GSomeR (GVBoolR (GBool n0))). split.
          ++ repeat (eapply GMatch_GSomeR_R; eauto).
             eapply GSome_R; eauto. apply GVBool_R; eauto.
             eapply multi_trans. eapply GIf_CondTrue_R. apply GGet_fdata_GSomeR_RR; eauto.
             apply GGet_fdata_GSomeR_RR; eauto. constructor.
          ++ simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
        -- (* e1 is false *) exists (GSomeR (GVBoolR (GBool false))). split.
          ++ repeat (eapply GMatch_GSomeR_R; eauto).
             eapply GSome_R; eauto. apply GVBool_R; eauto.
             eapply GIf_CondFalse_R. apply GGet_fdata_GSomeR_RR; eauto. constructor.
          ++ simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. constructor. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat apply GMatch_GNoneR_R; auto | simpl; rewrite <- Hval; constructor].
  - inversion IHe as [te1 [Hs1 Heq1] ]; clear IHe.
    inversion Heq1 as [ e1imp e1fun Hveq1 Hval1 | Hval ]; subst.
    + (* e1 is Some *) inversion Hveq1; subst; try (
          exists GNoneR; split; [ eapply GMatch_GNoneR_R; eauto | simpl; rewrite <- Hval1; constructor]).
      (* e1 is Bool *) assert ((trans_exp e s2 >>g= toBoolG) ==>* GSomeR (GBool n)) as Hre1. { apply toBoolG_GVBool_R; eauto. }
      exists (GSomeR (GVBoolR (GBool (negb n)))). split.
      * simpl. repeat (eapply GMatch_GSomeR_R; eauto).
        eapply GSome_R; eauto. apply GVBool_R; eauto.
        eapply multi_trans. eapply GNot_R. apply GGet_fdata_GSomeR_RR; eauto.
        econstructor; constructor.
      * simpl. rewrite <- Hval1. simpl. constructor. constructor.
    + (* e1 is None *) exists GNoneR; split; [ repeat apply GMatch_GNoneR_R; auto | simpl; rewrite <- Hval; constructor].
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
         (* obj_w is some or none *)
         destruct (Hseq l (GLoc l)) as [ [ Hhft [ obj1 [ obj2 [Hs_store [ Hvo [ Hsome Hobjeq ] ] ] ] ] ] | [ Hff Hnone ] ]; auto. constructor.
       (*     eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
         } *)
         -- (* object exists *)
(*            inversion Hveq as [ obj gobj Hobjeq Hsome H | ]; subst; [ auto | apply False_rec; eauto ]. *)
           assert (GVSelect s2 (GGet (trans_exp e1 s2 >>g= toLocG) fdata) ==>* GSomeR (GObj obj2)). {
             eapply GIf_CondTrue_R. eapply multi_trans. eapply GHasField_Key_R; eauto.
             eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. auto.
             eapply GSome_R; auto. eapply multi_trans. eapply GGet_Key_R; eauto.
             eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R; auto. auto.
           }
           assert (GGet (trans_exp e2 s2 >>g= toNatG) fdata ==>* GNum n). {
             eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
           }
           destruct (Hobjeq n (GNum n)) as [ [ Hhfto [ v1  [ v2 [ Hv_v [ Hsomev Hveq ] ] ] ] ] | [ Hhffo Hnone ] ]; subst; auto.  { constructor. }
         (*     eapply multi_trans. eapply GGet_Map_R. eassumption. constructor. apply GGet_fdata_GSomeR_R.
           } *)
           ++ exists (GSomeR v2). split.
             ** eapply GMatch_GSomeR_R. eassumption. eapply GMatch_GSomeR_R. eassumption.
                eapply GMatch_GSomeR_R. eauto.
                eapply GIf_CondTrue_R. eapply multi_trans. eapply GHasField_Key_R; eauto.
                eapply multi_trans. eapply GHasField_Map_R; eauto.
                eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. auto.
                eapply GSome_R. eapply multi_trans. eapply GGet_Key_R; eauto.
                eapply multi_trans. eapply GGet_Map_R; auto.
                eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. auto. 
                inversion Hveq; subst; auto.
             ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. rewrite Hsome. rewrite Hsomev. constructor. auto.
           ++ exists GNoneR. split.
             ** eapply GMatch_GSomeR_R. eassumption. eapply GMatch_GSomeR_R. eassumption.
                eapply GMatch_GSomeR_R. eauto.
                eapply GIf_CondFalse_R; auto. eapply multi_trans. eapply GHasField_Key_R; eauto.
                eapply multi_trans. eapply GHasField_Map_R; eauto.
                eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R. auto.
             ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. rewrite Hsome. rewrite Hnone. constructor.
         -- (* object does NOT exists *) 
           exists GNoneR. split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
              eapply GMatch_GNoneR_R; eauto. eapply GIf_CondFalse_R; auto.
              eapply multi_trans. eapply GHasField_Key_R; eauto.
              eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R; auto. auto.
           ** simpl. rewrite <- Hval1. rewrite <- Hval2. simpl. rewrite Hnone. constructor.
      * (* e2 is None *) exists GNoneR; split; [ eapply GMatch_GSomeR_R; eauto; repeat(eapply GMatch_GNoneR_R; eauto) 
        | simpl; rewrite <- Hval; rewrite LetImp_body_None; constructor ].
    + (* e1 is None *) exists GNoneR; split; [ repeat (apply GMatch_GNoneR_R; auto) | simpl; rewrite <- Hval; constructor].
Qed.

Lemma req_eq : forall e s0 v1 v2,
  req (evalExp e s0) v1 ->
  req (evalExp e s0) v2 ->
  v1 = v2.
Proof.
  intros.
  inversion H; subst.
  rewrite <- H1 in H0. inversion H0; subst.
  inversion H2; subst; inversion H4; subst; auto.
  rewrite <- H2 in H0. inversion H0; subst. reflexivity.
Qed.

Lemma trans_exp_C : forall e sigma sto m v,
  seq sigma sto ->
  trans_exp e (GMap m) ==>* v ->
  req (evalExp e sigma) v ->
  trans_exp e sto ==>* v.
Proof.
  intros.
  destruct (soundness_exp e sigma sto) as [eg [ Hestep Heeq'] ]; auto.
  replace v with eg. auto.
  eapply req_eq; eassumption.
Qed.

Definition gstore_update (st : loc -> option gxp) (x : loc) (v : gxp) :=
  t_update beq_loc st x (Some v).

Definition gobj_update (st : nat -> option gxp) (x : nat) (v : gxp) :=
  t_update beq_nat st x (Some v).

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

Lemma GGet_Obj_eq : forall e1 o n1 n v,
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

Lemma GGet_Sto_eq : forall e1 o n1 n v,
  n1 ==>* GLoc n ->
  e1 ==>* GMap (gstore_update o n v) ->
  GGet e1 n1 ==>* v.
Proof.
  intros e1 o n1 n v Hnr Her.
  eapply multi_trans. eapply GGet_Key_R; eauto.
  eapply multi_trans. eapply GGet_Map_R; eauto.
  econstructor. constructor. unfold gstore_update. apply t_update_eq.
  constructor.
Qed.

Lemma GVSelect_NoneR_R : forall o n n',
  o n' = None ->
  n ==>* (GNum n') ->
  GVSelect (GObj o) n ==>* GNoneR.
Proof.
  intros.
  eapply GIf_CondFalse_R; auto.
  eapply multi_trans. eapply GHasField_Key_R; eauto.
  econstructor; try apply multi_refl.
  constructor; auto.
Qed.

Lemma GHasField_True_Obj_I : forall o2 n1,
  GHasField (GObj o2) (GNum n1) ==>* GBool true -> o2 n1 <> None.
Proof.
  intros.
  inversion H; subst. inversion H0; subst; try solve_by_inverts 2.
  assumption.
Qed.

Lemma GHasField_False_Obj_I : forall o2 n1,
  GHasField (GObj o2) (GNum n1) ==>* GBool false -> o2 n1 = None.
Proof.
  intros.
  inversion H; subst. inversion H0; subst; try solve_by_inverts 2.
  assumption.
Qed.

Lemma GHasField_True_Sto_I : forall o2 n1,
  GHasField (GMap o2) (GLoc n1) ==>* GBool true -> o2 n1 <> None.
Proof.
  intros.
  inversion H; subst. inversion H0; subst; try solve_by_inverts 2.
  assumption.
Qed.

Lemma GHasField_False_Sto_I : forall o2 n1,
  GHasField (GMap o2) (GLoc n1) ==>* GBool false -> o2 n1 = None.
Proof.
  intros.
  inversion H; subst. inversion H0; subst; try solve_by_inverts 2.
  assumption.
Qed.

Lemma GGet_Value_Obj_I : forall o2 n1 v2,
  value v2 -> value (GObj o2) ->
  GGet (GObj o2) (GNum n1) ==>* v2 -> o2 n1 = Some v2.
Proof.
  intros.
  inversion H1; subst. inversion H.
  inversion H0; subst.
  inversion H2; subst; try solve_by_inverts 2.
  inversion H3; subst; auto.
  apply (H5 n1 y) in H8. inversion H8; subst; inversion H4.
Qed.

Lemma GGet_Value_Sto_I : forall s2 l1 o2,
  value (GMap s2) -> value (GObj o2) ->
  GGet (GMap s2) (GLoc l1) ==>* (GObj o2) -> s2 l1 = Some (GObj o2).
Proof.
  intros.
  inversion H1; subst.
  inversion H; subst.
  inversion H2; subst; try solve_by_inverts 2.
  inversion H3; subst; auto.
  apply (H5 l1 y) in H8. inversion H8; subst; inversion H4.
Qed.

Hint Resolve GHasField_True_Obj_I GHasField_False_Obj_I GHasField_True_Sto_I GHasField_False_Sto_I.

Lemma objeq_preservation : forall n o1 o2 v1 v2,
  objeq o1 (GObj o2) ->
  veq v1 v2 ->
  value (GObj o2) ->
  objeq (obj_update o1 n v1) (GObj (gobj_update o2 n v2)).
Proof.
  intros.
  intros n1 n2 Hneq.
  destruct (nat_dec n n1); subst.
  - (* n = n1 *) left. split.
    econstructor. apply ST_ObjHasFieldTrue. unfold gobj_update.
    rewrite t_update_eq. intro. discriminate. constructor.
    exists v1; exists v2; split; auto. eapply GGet_Obj_eq; constructor.
    split; auto. unfold obj_update. rewrite t_update_eq; auto.
  - (* n <> n1 *) destruct (H n1 n2) as [ [ Hhft [ v1' [ v2' [ Hget [ Hsome Heq ] ] ] ] ] | [ Hhff Hnone ] ]; auto.
    + left. split. econstructor; econstructor. unfold gobj_update.
      rewrite t_update_neq; auto.
      exists v1'; exists v2'; split.
      econstructor; try econstructor. unfold gobj_update.
      rewrite t_update_neq; auto.
      apply GGet_Value_Obj_I; auto. inversion Heq; subst; auto.
      split; auto. unfold obj_update. rewrite t_update_neq; auto.
    + right. split. econstructor. apply ST_ObjHasFieldFalse. unfold gobj_update.
      rewrite t_update_neq; auto. constructor.
      unfold obj_update. rewrite t_update_neq; auto.
Qed.

Lemma seq_preservation : forall l o1 o2 s1 s2,
  seq s1 (GMap s2) ->
  value (GObj o2) ->
  objeq o1 (GObj o2) ->
  value (GMap s2) ->
  seq (store_update s1 l o1) (GMap (gstore_update s2 l (GObj o2))).
Proof.
  intros.
  intros l1 l2 Hleq.
  destruct (loc_dec l l1); subst.
  - (* l = l1 *) left. split.
    econstructor. apply ST_StoHasFieldTrue. unfold gstore_update.
    rewrite t_update_eq. intro. discriminate. constructor.
    exists o1; exists o2; split; auto. eapply GGet_Sto_eq; constructor.
    split; auto. split; auto. unfold store_update. rewrite t_update_eq; auto.
  - (* l <> l1 *) destruct (H l1 l2) as [ [ Hhft [ o1' [ o2' [ Hget [ Hv [ Hsome Heq ] ] ] ] ] ] | [ Hhff Hnone ] ]; auto.
    + left. split. econstructor; econstructor. unfold gstore_update.
      rewrite t_update_neq; auto.
      exists o1'; exists o2'; split.
      econstructor; try econstructor. unfold gstore_update.
      rewrite t_update_neq; auto.
      apply GGet_Value_Sto_I; auto.
      split; auto. split; auto. unfold store_update. rewrite t_update_neq; auto.
    + right. split. econstructor. apply ST_StoHasFieldFalse. unfold gstore_update.
      rewrite t_update_neq; auto. constructor.
      unfold store_update. rewrite t_update_neq; auto.
Qed.

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

Lemma idx1_val_min : forall m i p n,
  idx1 i m p = Some n -> n >= i.
Proof.
  intro m.
  induction m.
  - intros. inversion H.
  - intros. simpl in H.
    destruct (p i); inversion H; clear H; auto.
    destruct b; try inversion H1; clear H1.
    auto.
    assert (n >= i + 1). eapply IHm; eauto. omega.
Qed. 

Definition soundness_evalLoop (e : exp) (s : stmt) (st1 : store) (st2 : gxp) (c: path) (n fuel : nat): Prop :=  
  forall k st1'', k <= n ->
  evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(fuel)) = Some st1'' ->
  exists g, GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
  /\ store_value g /\ oeq seq st1'' g.

Lemma GGetOrElse_GSomeR_R : forall e1 v1 e2,
  e1 ==>* GSomeR v1 ->
  GGetOrElse e1 e2 ==>* v1.
Proof.
  intros. eapply multi_trans. apply GIf_CondTrue_R.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fvalid_GSomeR_R.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
  constructor.
Qed.

Lemma GGetOrElse_GNoneR_R : forall e1 e2,
  e1 ==>* GNoneR ->
  GGetOrElse e1 e2 ==>* e2.
Proof.
  intros. apply GIf_CondFalse_R.
  eapply multi_trans. apply GGet_Map_R; eauto. apply GGet_fvalid_GNoneR_R.
  constructor.
Qed.

Lemma idx1_soundness_error : forall k n e s sigma sigma' st2 p m,
  k <= n ->
  soundness_evalLoop e s sigma st2 p n m ->
  evalLoop_monotone e s sigma p n m ->
  evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some None \/ 
  (evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') /\
  (evalExp e sigma' >>= toBool) = None) \/
  (evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') /\
  (evalExp e sigma' = Some (VBool false))) ->
  GFixIndex (n - k) (fun nstep : nat =>
     GGetOrElse (GRepeat (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) (GSome st2) >>g= (fun nsto : gxp =>
       (trans_exp e nsto >>g= toBoolG))) (GBool false)) ==>* GNum n.
Proof.
  induction k; intros.
  - econstructor. constructor.
    replace (n - 0) with n; try omega.
    destruct H2 as [ Hnone | [ [ Hsome Hnone ] | [ Hsome Hcsome ] ] ].
    + destruct (H0 n None) as [ gstore [ Hloop [ Hv Heq ] ] ]; auto; try omega.
      inversion Heq; subst.
      apply GIf_CondFalse_R. apply GGetOrElse_GNoneR_R.
      eapply GMatch_GNoneR_R; auto.
      constructor.
    + destruct (H0 n (Some sigma')) as [ gstore [ Hloop [ Hv Heq ] ] ]; auto; try omega.
      inversion Heq; subst.
      destruct (soundness_exp e sigma' g) as [ ge [ Hcond Hceq ] ]; auto.
      destruct (store_value_map g Hv) as [ gm ]; subst.
      remember (〚 e 〛 (sigma')) as eImp.
      apply GIf_CondFalse_R. apply GGetOrElse_GNoneR_R.
      eapply GMatch_GSomeR_R; eauto.
      destruct eImp; inversion Hceq; subst.
      * inversion H4; subst; inversion Hnone.
        -- eapply toBoolG_GVNumR_None.
           eapply trans_exp_C; eauto.
           eapply seq_C; eauto.
           eapply multi_trans. eapply GGet_Map_R; eauto.
           apply GGet_fdata_GSomeR_R. rewrite <- HeqeImp. auto.
        -- eapply toBoolG_GVLocR_None.
           eapply trans_exp_C; eauto.
           eapply seq_C; eauto.
           eapply multi_trans. eapply GGet_Map_R; eauto.
           apply GGet_fdata_GSomeR_R. rewrite <- HeqeImp. auto.
      * eapply GMatch_GNoneR_R. eapply trans_exp_C; eauto.
        eapply seq_C; eauto.
        eapply multi_trans. eapply GGet_Map_R; eauto.
        apply GGet_fdata_GSomeR_R. rewrite <- HeqeImp. auto.
      * constructor.
    + destruct (H0 n (Some sigma')) as [ gstore [ Hloop [ Hv Heq ] ] ]; auto; try omega.
      inversion Heq; subst.
      destruct (soundness_exp e sigma' g) as [ ge [ Hcond Hceq ] ]; auto.
      destruct (store_value_map g Hv) as [ gm ]; subst.
      rewrite Hcsome in Hceq. inversion Hceq; subst.
      inversion H4; subst.
      apply GIf_CondFalse_R. apply GGetOrElse_GSomeR_R.
      eapply GMatch_GSomeR_R; eauto. eapply toBoolG_GVBool_R.
      eapply trans_exp_C; eauto.
      eapply seq_C; eauto.
      eapply multi_trans. eapply GGet_Map_R; eauto.
      apply GGet_fdata_GSomeR_R. rewrite Hcsome. auto. constructor.
  - destruct (H1 (n - S k)) as [ sigma'' [ Hiloop Hicond ] ]; try omega.
    destruct (H0 (n - S k) (Some sigma'')) as [ g [ Giloop [ Giv Gieq ] ] ]; auto; try omega.
    inversion Gieq; subst.
    destruct (soundness_exp e sigma'' g0) as [ ge [ Hcond Hceq ] ]; auto.
    destruct (store_value_map g0 Giv) as [ gm ]; subst.
    rewrite Hicond in Hceq. inversion Hceq; subst.
    inversion H5; subst.
    assert ((GRepeat (GNum (n - S k)) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) (GSome st2) >>g=
   (fun nsto : gxp => trans_exp e nsto >>g= toBoolG)) ==>* GSomeR  (GBool true)). {
      eapply GMatch_GSomeR_R. eassumption.
      apply toBoolG_GVBool_R.
      eapply trans_exp_C; eauto.
      eapply seq_C; eauto.
      eapply multi_trans. eapply GGet_Map_R; eauto.
      apply GGet_fdata_GSomeR_R.
      rewrite Hicond. auto.
    }
    econstructor. constructor.
    eapply GIf_CondTrue_R. apply GGetOrElse_GSomeR_R; auto.
    replace (n - S k + 1) with (n - k); try omega.
    eapply IHk; eauto; omega.
Qed.

Lemma idx_soundness : forall e s sigma sigma' st2 p n m,
  soundness_evalLoop e s sigma st2 p n m ->
  evalLoop_monotone e s sigma p n m ->
  evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some None \/ 
  (evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') /\
  (evalExp e sigma' >>= toBool) = None)  \/
  (evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') /\
  (evalExp e sigma' = Some (VBool false))) ->
  GFixIndex 0 (fun nstep : nat =>
     GGetOrElse (GRepeat (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) (GSome st2) >>g= (fun nsto : gxp =>
       (trans_exp e nsto >>g= toBoolG))) (GBool false)) ==>* GNum n.
Proof.
  intros.
  assert (GFixIndex (n - n) (fun nstep : nat =>
     GGetOrElse (GRepeat (GNum nstep) p (fun it : nat => trans_stmts s (GSLoc p) (PWhile p it)) (GSome st2) >>g= (fun nsto : gxp =>
       (trans_exp e nsto >>g= toBoolG))) (GBool false)) ==>* GNum n). eapply idx1_soundness_error; eauto.
  replace (n - n) with 0 in H2; auto; omega.
Qed.
  
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

Lemma help_commute : forall n ob ob',
  ob = ob' -> GFixIndex n ob = GFixIndex n ob'.
Proof. intros; subst; auto. Qed.

Lemma help_commute_1 : forall n ob ob' e1 e2 e3 e4 e5 e6,
  ob = ob' -> GPut e1 e2 (GGet (GRepeat (GFixIndex n ob) e3 e4 e5) e6) = GPut e1 e2 (GGet (GRepeat (GFixIndex n ob') e3 e4 e5) e6).
Proof. intros; subst; auto. Qed.

Lemma help_commute_2 : forall n ob ob' e1 e2 e3 e4 e5 e6,
  ob = ob' -> GIf (GGet (GRepeat (GFixIndex n ob) e3 e4 e5) e6) e1 e2 = GIf (GGet (GRepeat (GFixIndex n ob') e3 e4 e5) e6) e1 e2.
Proof. intros; subst; auto. Qed.

Lemma help_commute_3 : forall e s c c' sto sto',
  beq_path c c' = false ->
  (fun n0 : nat => subst c' sto (trans_stmts s (GSLoc c) (PWhile c n0))) =
    (fun n0 : nat => trans_stmts s (GSLoc c) (PWhile c n0)) ->
  subst c' sto (GGet (GRepeat
    (GFixIndex 0 (fun nstep : nat => GGetOrElse
      (GRepeat (GNum nstep) c
        (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) 
          (GSome sto') >>g= (fun nsto : gxp => trans_exp e nsto >>g= toBoolG))
            (GBool false))) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it))
              (GSome sto')) fdata) =
   GGet (GRepeat
    (GFixIndex 0 (fun nstep : nat => GGetOrElse
      (GRepeat (GNum nstep) c
        (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) 
          (GSome (subst c' sto sto')) >>g= (fun nsto : gxp => trans_exp e nsto >>g= toBoolG))
            (GBool false))) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it))
              (GSome (subst c' sto sto'))) fdata.
Proof.
  intros. simpl.
  erewrite help_commute.
  2: { apply functional_extensionality.
       intro x. repeat rewrite H. repeat rewrite H0.
       rewrite subst_trans_exp_commute.
       simpl. repeat rewrite H. simpl. repeat rewrite H0.
       reflexivity.
  }
  rewrite H.  rewrite H0. reflexivity.
Qed.

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
  rewrite H0.
  rewrite help_commute_3; auto.
  erewrite help_commute_1.
  2: { apply functional_extensionality.
       intro x. repeat rewrite H. repeat rewrite H0.
       rewrite subst_trans_exp_commute.
       simpl. repeat rewrite H. simpl. repeat rewrite H0.
       reflexivity.
  }
  erewrite help_commute_2.
  2: { apply functional_extensionality.
       intro x. repeat rewrite H. repeat rewrite H0.
       rewrite subst_trans_exp_commute.
       simpl. repeat rewrite H. simpl. repeat rewrite H0.
       reflexivity.
  }
  reflexivity. 
Qed.

Definition soundness_stmts_def (s : stmt): Prop :=  
  forall c st1 st1' st2 m2 fuel,
    st2 ==>* (GMap m2) ->
    seq st1 (GMap m2) ->
    value (GMap m2) ->
    evalStmt s st1 c (S fuel) = Some st1' ->
    exists g, (trans_stmts s st2 c) ==>* g /\ store_value g /\ oeq seq st1' g.

Lemma soundness_evaloop_partial : forall k n e s c st1 st1' st1'' st2 m2 fuel,
   k <= n ->
   st2 ==>* (GMap m2) ->
   seq st1 (GMap m2) ->
   value (GMap m2) ->
   soundness_stmts_def s ->
   evalLoop_monotone e s st1 c n (S fuel) ->
   evalLoop e s st1 c n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1' ->
   evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1'' ->
     exists g, GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
     /\ store_value g /\ oeq seq st1'' g.
Proof.
  induction k; intros.
  - inversion H6; subst. 
    eexists. split. eapply multi_step. apply ST_RepeatStop. eapply GSome_R; eauto. eauto.
  - inversion H; subst.
    + (* S k = n *)
      rewrite H6 in H5. inversion H5; subst; clear H5.
      destruct (H4 k) as [ st0 [ Hloop Hcond ] ]; try omega.
      assert (Hsk := H6).
      simpl in H6. rewrite Hloop in H6. rewrite Hcond in H6. simpl in H6.
      destruct (IHk (S k) e s c st1 st1' (Some st0) st2 m2 fuel) as [ gst0 [ Gloop [ Gsv Geq ] ] ]; auto; try omega.
      inversion Geq; subst.
      destruct (store_value_map g Gsv) as [ gm ]; subst.
      destruct (H3 (PWhile c k) st0 st1'
         (GGet (GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2)) fdata) gm fuel) as [ gst1' [ Gloop' Goo ] ]; auto. {
        eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
      }
      exists gst1'. split; auto.
      eapply multi_step. apply ST_RepeatStep.
      eapply GMatch_GSomeR_R; eauto. 
      rewrite subst_trans_stmts_commute; simpl; rewrite <- beq_path_eq; try reflexivity.
      auto.
    + (* S k < n *)
      destruct (H4 k) as [ st0 [ Hloop Hcond ] ]; try omega.
      assert (Hsk := H6).
      simpl in H6. rewrite Hloop in H6. rewrite Hcond in H6. simpl in H6.
      destruct (IHk (S m) e s c st1 st1' (Some st0) st2 m2 fuel) as [ gst0 [ Gloop [ Gsv Geq ] ] ]; auto; try omega.
      inversion Geq; subst.
      destruct (store_value_map g Gsv) as [ gm ]; subst.
      destruct (H3 (PWhile c k) st0 st1''
         (GGet (GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2)) fdata) gm fuel) as [ gst1' [ Gloop' Goo ] ]; auto. {
        eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
      }
      exists gst1'. split; auto.
      eapply multi_step. apply ST_RepeatStep.
      eapply GMatch_GSomeR_R; eauto. 
      rewrite subst_trans_stmts_commute; simpl; rewrite <- beq_path_eq; try reflexivity.
      auto.
Qed.

Theorem soundness_stmts: forall s, soundness_stmts_def s .
Proof.
  intro s.
  induction s; unfold soundness_stmts_def; intros c st1 st1' st2 m2 fuel Hstep Hseq Hvs2 HsImp.
  - exists (GSomeR (GMap
     (t_update beq_loc (t_update beq_loc m2 (LNew c) (Some OEmpty)) (LId i)
        (Some (GObj (t_update Nat.eqb (t_empty None) 0 (Some (GVLocR (GLoc (LNew c)))))))))). split.
    + simpl.  apply alloc_R; eauto.
    + split; auto.
      inversion HsImp; subst. constructor.
      apply seq_preservation; auto. apply seq_preservation; eauto.
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
      (* e is Loc *)
      assert ((trans_exp e st2 >>g= toLocG) ==>* GSomeR (GLoc l)) as Hre. { apply toLocG_GVLoc_R; eauto. }
      assert (GGet (trans_exp e st2 >>g= toLocG) fdata ==>* GLoc l). {
        eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
      }
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
         destruct (HseqNR l (GLoc l)) as [ [ Hhft [ obj1 [ obj2 [Hs_store [ Hvo [ Hsome Hobjeq ] ] ] ] ] ] | [ Hff Hnone ] ]; auto. constructor.
         ++ assert (GVSelect st2 (GGet (trans_exp e st2 >>g= toLocG) fdata) ==>* GSomeR (GObj obj2)). {
              eapply GIf_CondTrue_R. eapply multi_trans. eapply GHasField_Key_R; eauto. eauto.
              eapply GSome_R; auto. eapply multi_trans. eapply GGet_Key_R; eauto. eauto.
            }
            assert (GGet (trans_exp e0 st2 >>g= toNatG) fdata ==>* GNum n). {
             eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
            }
        (*  inversion Hveq as [ no ng Hobjeq Hoeq Hgsome | Hnone ]; subst; clear Hveq. *)
     (*     ++ (* object exists *)
           assert (exists m, ng = GObj m) as Hobj. { apply obj_value_obj; auto. }
           inversion Hobj; subst. *)
           eexists. split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
              eapply GMatch_GSomeR_R; eauto.
              apply GSome_R. eapply multi_trans. eapply GPut_Key_R; eauto.
              eapply multi_trans. eapply GPut_Map_R; eauto.
              eapply multi_trans. eapply GPut_Value_R; auto.
              eapply multi_trans. eapply GPut_Key_R; eauto.
              eapply multi_trans. eapply GPut_Map_R; eauto.
              eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
              eapply multi_trans. eapply GPut_Value_R; auto.
              eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
              eapply multi_step. constructor; eauto. apply multi_refl.
              eapply multi_step. constructor; eauto. apply multi_refl.
              eauto 8.
           ** split; eauto 8.
            simpl in HsImp. rewrite <- Hesome in HsImp. rewrite <- He0some in HsImp.
            rewrite <- He1some in HsImp. simpl in HsImp. rewrite Hsome in HsImp.
            inversion HsImp; subst.
            constructor.
            apply seq_preservation; eauto.
            apply objeq_preservation; auto.
         ++ (* object does NOT exists *)
           exists GNoneR; split.
           ** eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto. eapply GMatch_GSomeR_R; eauto.
              eapply GMatch_GNoneR_R; eauto.
              eapply GIf_CondFalse_R. eapply multi_trans. eapply GHasField_Key_R; eauto. eauto. auto.
           ** split; auto.
              simpl in HsImp. rewrite <- Hesome in HsImp. rewrite <- He0some in HsImp.
              rewrite <- He1some in HsImp. simpl in HsImp. rewrite Hnone in HsImp. inversion HsImp; subst. constructor.
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
      try (exists GNoneR; split; [
         eapply GMatch_GNoneR_R; eauto |
         split; auto; simpl in HsImp; rewrite <- Hesome in HsImp; inversion HsImp; subst; constructor]).
      (* e is Bool *)
      assert ((trans_exp e st2 >>g= toBoolG) ==>* GSomeR (GBool n)) as Hre0. { apply toBoolG_GVBool_R; eauto. }
      destruct n.
      * (* e is True *) destruct (IHs1 (PThen c) st1 st1' st2 m2 fuel) as [ res1 [ Hres1s [ Hres1sv Hres1eq ] ] ]; auto. {
          simpl in HsImp. rewrite <- Hesome in HsImp. apply HsImp.
        }
        exists res1. split; auto.
        eapply GMatch_GSomeR_R; eauto.
        eapply multi_trans. eapply GIf_CondTrue_R.
        eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
        eassumption. apply multi_refl.
      * (* e is False *) destruct (IHs2 (PElse c) st1 st1' st2 m2 fuel) as [ res2 [ Hres2s [ Hres2sv Hres2eq ] ] ]; auto. {
          simpl in HsImp. rewrite <- Hesome in HsImp. apply HsImp.
        }
        exists res2. split; auto.
        eapply GMatch_GSomeR_R; eauto.
        eapply multi_trans. eapply GIf_CondFalse_R.
        eapply multi_trans. eapply GGet_Map_R; eauto. eapply GGet_fdata_GSomeR_R.
        eassumption. apply multi_refl.
    + (* e is None *) exists GNoneR; split; [ repeat (eapply GMatch_GNoneR_R; eauto) |
         split; auto; simpl in HsImp; rewrite <- Hnone in HsImp; inversion HsImp; subst; constructor ].
  - assert (seq st1 st2) as HseqNR. { eapply seq_C; eauto. }
    simpl in HsImp. simpl.
    remember (idx (S fuel)
               (fun i : nat =>
                match
                  σ' ↩ evalLoop e s st1 c i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel))
                  IN b ← (〚 e 〛 (σ')) >>= toBool IN Some (Some (negb b))
                with
                | Some (Some b) => Some b
                | Some None => Some true
                | None => None
                end)) as Hidx.
    destruct Hidx.
    + assert (Heval_some := HeqHidx). symmetry in Heval_some.
      apply idx_evalLoop_some in Heval_some; try omega.
      destruct Heval_some as [ Hmon [ [ Hloop | Hloop ] | [ sigma [ [ Hcsome | Hcnone ] Hloop ] ] ] ]; rewrite Hloop in HsImp; inversion HsImp; clear H0.
      * assert (forall k st1'',
             k <= n ->
             evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1'' ->
             exists g, GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
            /\ store_value g /\ oeq seq st1'' g). { intros.
           eapply soundness_evaloop_partial with (n := n); eauto.
        }
        exists GNoneR. split; auto.
        eapply GMatch_GNoneR_R.
        eapply multi_trans. eapply GRepeat_NumIt_R. eapply idx_soundness; eauto.
        destruct (H n None) as [ gNone [ Hnone [ Hsv Heq ] ] ]; auto. inversion Heq; subst. auto.
      * assert (forall k st1'',
               k <= n ->
            evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1'' ->
            exists g, GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
           /\ store_value g /\ oeq seq st1'' g). { intros.
          eapply soundness_evaloop_partial with (n := n); eauto.
        }
        rewrite Hcsome in HsImp; simpl in HsImp;  inversion HsImp; subst; clear HsImp.
        assert (Hsave := Hloop).
        apply (H n (Some sigma)) in Hloop; try omega.
        destruct Hloop as [ gstore [ Hgloop [ Hsv Hg_seq ] ] ].
        inversion Hg_seq; subst.
        destruct (store_value_map g Hsv) as [ gm ]; subst.
        assert (GRepeat
           (GFixIndex 0
              (fun nstep : nat =>
               GGetOrElse
                 (GRepeat (GNum nstep) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) >>g=
                  (fun nsto : gxp => trans_exp e nsto >>g= toBoolG)) (GBool false))) c
           (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* GSomeR (GMap gm)). {
          eapply multi_trans. apply GRepeat_NumIt_R. eapply idx_soundness; eauto. assumption.
        }
        destruct (soundness_exp e sigma (GMap gm)) as [ ew [ Hes' Heeq' ] ]; auto.
        rewrite Hcsome in Heeq'.
        inversion Heeq'; subst; clear Heeq'.
        inversion H3; subst; clear H3.
        exists (GSomeR (GMap gm)). split; auto.
        eapply GMatch_GSomeR_R; eauto.
        eapply GMatch_GSomeR_R. eapply toBoolG_GVBool_R. eapply trans_exp_C; eauto.
        eapply seq_C; eauto.
        eapply multi_trans. eapply GGet_Map_R; eauto.
        apply GGet_fdata_GSomeR_R. rewrite Hcsome. constructor. constructor.
        eapply GSome_R; eauto. eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
      * assert (forall k st1'',
             k <= n ->
             evalLoop e s st1 c k (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S fuel)) = Some st1'' ->
             exists g, GRepeat (GNum k) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* g
            /\ store_value g /\ oeq seq st1'' g). { intros.
           eapply soundness_evaloop_partial with (n := n); eauto.
        }
        rewrite Hcnone in HsImp; simpl in HsImp; inversion HsImp; subst; clear HsImp.
        assert (Hsave := Hloop).
        apply (H n (Some sigma)) in Hloop; try omega.
        destruct Hloop as [ gstore [ Hgloop [ Hsv Hg_seq ] ] ].
        inversion Hg_seq; subst.
        destruct (store_value_map g Hsv) as [ gm ]; subst.
        assert (GRepeat
           (GFixIndex 0
              (fun nstep : nat =>
               GGetOrElse
                 (GRepeat (GNum nstep) c (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) >>g=
                  (fun nsto : gxp => trans_exp e nsto >>g= toBoolG)) (GBool false))) c
           (fun it : nat => trans_stmts s (GSLoc c) (PWhile c it)) (GSome st2) ==>* GSomeR (GMap gm)). {
          eapply multi_trans. apply GRepeat_NumIt_R. eapply idx_soundness; eauto. assumption.
        }
        destruct (soundness_exp e sigma (GMap gm)) as [ ew [ Hes' Heeq' ] ]; auto.
        remember (〚 e 〛 (sigma)) as cond.
        destruct  cond; inversion Heeq'; subst; clear Heeq'.
        ++ exists GNoneR. split; auto.
           eapply GMatch_GSomeR_R; eauto.
           destruct v; inversion H3; subst; clear H3; inversion Hcnone; subst; clear Hcnone.
           ** eapply GMatch_GNoneR_R. eapply toBoolG_GVNumR_None.
              eapply trans_exp_C; eauto. eapply seq_C; eauto.
              eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
              rewrite <- Heqcond. constructor. auto.
           ** eapply GMatch_GNoneR_R. eapply toBoolG_GVLocR_None.
              eapply trans_exp_C; eauto. eapply seq_C; eauto.
              eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
              rewrite <- Heqcond. constructor. auto.
        ++ exists GNoneR. split; auto.
           eapply GMatch_GSomeR_R; eauto.
           eapply GMatch_GNoneR_R. eapply GMatch_GNoneR_R.
           eapply trans_exp_C; eauto. eapply seq_C; eauto.
           eapply multi_trans. eapply GGet_Map_R; eauto. apply GGet_fdata_GSomeR_R.
           rewrite <- Heqcond. constructor.
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
Unshelve. apply st1.
Qed.

End Translation.