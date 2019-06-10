(* code partly taken from Software Foundations Imp.v *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

(* ---------- maps ---------- *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Definition total_map (A:Type) := id -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

(* ---------- Source language IMP ---------- *)
(* TODO: field read, allocation, field assignment, abort *)
Inductive exp : Type :=
  | AId : id -> exp
  | ANum : nat -> exp
  | APlus : exp -> exp -> exp
  | AMinus : exp -> exp -> exp
  | AMult : exp -> exp -> exp

  | BTrue : exp
  | BFalse : exp
  | BEq : exp -> exp -> exp
  | BLe : exp -> exp -> exp
  | BNot : exp -> exp
  | BAnd : exp -> exp -> exp
.

Inductive stm : Type :=
  | CSkip : stm
  | CAss : id -> exp -> stm
  | CSeq : stm -> stm -> stm
  | CIf : exp -> stm -> stm -> stm
  | CWhile : exp -> stm -> stm.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* ---------- semantics ---------- *)

Inductive val: Type :=
  | VNum : nat -> val
  | VBool : bool -> val
  | VLoc : id -> val.

Definition store := total_map (option val).

Definition empty_store : store :=
  t_empty None.

Definition W : id := Id 10.
Definition X : id := Id 11.
Definition Y : id := Id 12.
Definition Z : id := Id 13.

Definition toNat v :=
  match v with
  | VNum n => Some n
  | _ => None
  end.
Definition toBool v :=
  match v with
  | VBool n => Some n
  | _ => None
  end.
Definition toLoc v :=
  match v with
  | VLoc n => Some n
  | _ => None
  end.

Notation "'LET' x <-- e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
Notation "'LET' x <--- e1 'IN' e2"
   := (match e1 with
         | Some (Some x) => e2
         | Some None => Some None
         | None => None
       end)
   (right associativity, at level 60).

Notation "e1 '>>=' e2"
   := (match e1 with
         | Some x => e2 x
         | None => None
       end)
   (right associativity, at level 80).
Notation "e1 '>>>=' e2"
   := (match e1 with
         | Some (Some x) => e2 x
         | Some None => Some None
         | None => None
       end)
   (right associativity, at level 80).

(* ----------- IMP evaluation ----------- *)

Fixpoint eval_exp (e: exp) (sto: store): option val :=
  match e with
  | AId x => sto x
  | ANum n => Some (VNum n)
  | APlus a b =>  LET a <-- eval_exp a sto >>= toNat IN
                  LET b <-- eval_exp b sto >>= toNat IN
                  Some (VNum (a + b))
  | AMinus a b => LET a <-- eval_exp a sto >>= toNat IN
                  LET b <-- eval_exp b sto >>= toNat IN
                  Some (VNum (a - b))
  | AMult a b =>  LET a <-- eval_exp a sto >>= toNat IN
                  LET b <-- eval_exp b sto >>= toNat IN
                  Some (VNum (a * b))
  | BTrue => Some (VBool true)
  | BFalse => Some (VBool false)
  | BEq a b =>    LET a <-- eval_exp a sto >>= toNat IN
                  LET b <-- eval_exp b sto >>= toNat IN
                  Some (VBool (beq_nat a b))
  | BLe a b =>    LET a <-- eval_exp a sto >>= toNat IN
                  LET b <-- eval_exp b sto >>= toNat IN
                  Some (VBool (leb a b))
  | BAnd a b =>   LET a <-- eval_exp a sto >>= toBool IN
                  LET b <-- eval_exp b sto >>= toBool IN
                  Some (VBool (andb a b))
  | BNot a =>     LET a <-- eval_exp a sto >>= toBool IN
                  Some (VBool (negb a))
  end.

Fixpoint idx1 (i:nat) (m:nat) (p: nat -> option bool): option nat :=
  match m with 
  | O => None
  | S m' =>
    LET b <-- p i IN
    if b then Some i else idx1 (i+1) m' p
  end.

Definition idx (m:nat) (p: nat -> option bool): option nat := idx1 0 m p.

Fixpoint eval_loop (b1 : exp) (c : stm) (st : store)(n : nat)(m : nat)
                   (evstm: store -> option (option store))
                   : option (option store) :=
  match n with
  | O => Some (Some st)
  | S n' =>
    LET st' <--- eval_loop b1 c st n' m evstm IN
    LET b <-- eval_exp b1 st' >>= toBool IN
    if b then evstm st' else Some None (* error or timeout ??? *)
  end.

Fixpoint eval_stm (c : stm) (st : store)(m : nat) {struct c}
                  : option (option store) :=
    match c with
      | SKIP =>
          Some (Some st)
      | l ::= a1 => Some (
          LET v <-- eval_exp a1 st IN
          Some (t_update st l (Some v)))
      | c1 ;; c2 =>
          LET st' <--- eval_stm c1 st m IN
          eval_stm c2 st' m
      | IFB b THEN c1 ELSE c2 FI =>
          LET b <-- eval_exp b st >>= toBool IN
          if b
            then eval_stm c1 st m
            else eval_stm c2 st m
      | WHILE b1 DO c1 END =>
          LET n <-- idx m (fun i =>
                             match (LET st1 <--- eval_loop b1 c1 st i m (fun st2 => eval_stm c1 st2 m) IN
                             LET b <-- eval_exp b1 st1 >>= toBool IN
                             Some (Some (negb b))) with | Some (Some b) => Some b | Some None => Some true | None => None  end (* TODO: cleanup slightly. inline eval_loop? *)
                          ) IN
          eval_loop b1 c1 st n m (fun st2 => eval_stm c1 st2 m) 
    end.

(* ---------- test cases ---------- *)

Definition test_ceval (st:store) (c:stm) :=
  match eval_stm c st 500 with
  | Some (Some st) => Some (Some (st X, st Y, st Z))
  | Some None      => Some None
  | None           => None
  end.

Definition fact_in_coq : stm :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Compute
     (test_ceval empty_store
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3
            ELSE Z ::= ANum 4
          FI)).
(*   ====>
      Some (2, _, 4)   *)

Compute
     (test_ceval empty_store
         (X ::= AId Z)).
(*   ====>
      Some None (* error *)   *)

Compute
     (test_ceval empty_store
         (WHILE BTrue DO SKIP END)).
(*   ====>
      None (* timeout *)   *)

Compute (test_ceval (t_update empty_store X (Some (VNum 4))) fact_in_coq).
(*   ====>
      Some (4, 24, 0)   *)

(* ---------- Target language FUN ---------- *)
(* TODO: extend the target language to FUN *)
Inductive gxp : Type :=
  | GNum : nat -> gxp
  | GMap : (total_map (option gxp)) -> gxp
  | GGet : gxp -> id -> gxp
  | GPut : gxp -> id -> gxp -> gxp

  | GPlus : gxp -> gxp -> gxp
  | GMinus : gxp -> gxp -> gxp
  | GMult : gxp -> gxp -> gxp

  | GBool : bool -> gxp
  | GEq : gxp -> gxp -> gxp
  | GLe : gxp -> gxp -> gxp
  | GNot : gxp -> gxp
  | GAnd : gxp -> gxp -> gxp

  | GIf : gxp -> gxp -> gxp -> gxp
.

Definition fvalid : id := Id 0. (* "$valid" *)
Definition fdata :  id := Id 1. (* "$data"  *)
Definition ftpe :   id := Id 0. (* "$tpe"   *)
Definition fval :   id := Id 1. (* "$val"   *)

Definition tnat :   gxp := GNum 0.
Definition tbool :  gxp := GNum 1.
Definition tloc :   gxp := GNum 2.

Definition GEmpty : gxp := GMap (t_empty None).

Definition GNone :  gxp := GPut GEmpty fvalid (GBool false).
Definition GSome a : gxp := GPut (GPut GEmpty fvalid (GBool true)) fdata a.

Definition GMatch (scrutinee: gxp) (none: gxp) (some: gxp -> gxp): gxp :=
  GIf (GGet scrutinee fvalid) (some (GGet scrutinee fdata)) none.

Definition GVNum (a: gxp): gxp :=
  GPut (GPut GEmpty ftpe tnat) fval a.

Definition GVBool (a: gxp): gxp :=
  GPut (GPut GEmpty ftpe tbool) fval a.

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
(* Notation "e1 '>>>g=' e2"
   := (match e1 with
         | Some (Some x) => e2 x
         | Some None => Some None
         | None => None
       end)
   (right associativity, at level 80). *)

(* ---------- translation (exp only for now) --------- *)
Fixpoint trans_exp (e: exp) (sto: gxp): gxp :=
  match e with
  | AId x => GGet sto x (* fixme: check error *)
  | ANum n => GSome (GVNum (GNum n))
  | APlus a b =>  LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GPlus a b))
  | AMinus a b => LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GMinus a b))
  | AMult a b =>  LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVNum (GMult a b))
  | BTrue =>      GSome (GVBool (GBool true))
  | BFalse =>     GSome (GVBool (GBool false))
  | BEq a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GEq a b))
  | BLe a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GLe a b))
  | BAnd a b =>   LETG a <-- trans_exp a sto >>g= toBoolG IN
                  LETG b <-- trans_exp b sto >>g= toBoolG IN
                  GSome (GVBool (GAnd a b))
  | BNot a =>     LETG a <-- trans_exp a sto >>g= toBoolG IN
                  GSome (GVBool (GNot a))
  end.

(* ---------- normal-order simplification semantics for FUN --------- *)

(* simplification / normalization *)
Fixpoint sms_eval_exp (e: gxp): gxp :=
  match e with
(*  | GNum n => e
  | GMap m => e (* simpl in Map? *) *)
  | GGet a x => match sms_eval_exp a with
                | GMap m => match m x with Some y => y | None => GGet (GMap m) x end
                | a' => GGet a' x
                end 
  | GPut a x b => match sms_eval_exp a, sms_eval_exp b with
                  | GMap m, b' => GMap (t_update m x (Some b'))
                  | a', b' => GPut a' x b'
                  end 
  | GPlus a b => match sms_eval_exp a, sms_eval_exp b with
                 | GNum a', GNum b' => GNum (a' + b')
                 | a', b' => GPlus a' b'
                 end 
  | GMinus a b => match sms_eval_exp a, sms_eval_exp b with
                 | GNum a', GNum b' => GNum (a' - b')
                 | a', b' => GMinus a' b'
                 end
  | GMult a b => match sms_eval_exp a, sms_eval_exp b with
                 | GNum a', GNum b' => GNum (a' * b')
                 | a', b' => GMult a' b'
                 end 
  | GEq a b => match sms_eval_exp a, sms_eval_exp b with
                 | GNum a', GNum b' => GBool (beq_nat a' b')
                 | a', b' => GEq a' b'
                 end 
  | GIf c a b => match sms_eval_exp c with
                 | GBool c' => if c' then sms_eval_exp a else sms_eval_exp b
                 | c' => GIf c' (sms_eval_exp a) (sms_eval_exp b)
                 end 
  | _ => e (* TODO *)                                   
  end.

(* examples, sanity checks *)

Definition testprog := (trans_exp (APlus (ANum 2) (ANum 3)) (GMap (t_empty None))).

Definition testprog2 := fun e1 e2 => (trans_exp (APlus e1 e2) (GMap (t_empty None))).

Definition testprog1 := (trans_exp (ANum 2)) (GMap (t_empty None)).

(* WARNING: computing of GMao unfolds string comparison (<-- huge term!!!) *)
Compute testprog.
Compute testprog1.
Compute testprog2. 

Compute (sms_eval_exp (GPut GEmpty fvalid (GBool true))).

(* Compute (fun e1 e2 => sms_eval_exp (testprog2 e1 e2)).  *)

(* ----- equivalence with respect to simplification ----- *)

Definition geq a b := sms_eval_exp a = sms_eval_exp b.

Definition fgeq f1 f2 := forall b1 b2, geq b1 b2 -> geq (f1 b1) (f2 b2).

Lemma GEQ_trans: forall a b c, geq a b -> geq b c -> geq a c.
Proof.
  intros. unfold geq in *. simpl. rewrite H. simpl. auto.
Qed.

Lemma FGEQ_refl: forall f, (forall b1 b2, geq b1 b2 -> geq (f b1) (f b2)) -> fgeq f f.
Proof. intros. unfold fgeq. intros. eapply H. eauto. Qed. 

(* ----- prove some congruence rules ----- *)

Lemma GEQ_IfC: forall c1 c2 a1 a2 b1 b2,
    geq c1 c2 -> geq a1 a2 -> geq b1 b2 -> geq (GIf c1 a1 b1) (GIf c2 a2 b2).
Proof. intros. unfold geq in *. simpl. rewrite H. rewrite H0. rewrite H1. simpl. auto. Qed.

Lemma GEQ_GetC: forall a1 a2 x,
    geq a1 a2 -> geq (GGet a1 x) (GGet a2 x).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_PlusC: forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GPlus a1 b1) (GPlus a2 b2).
Proof. intros. unfold geq in *. simpl. rewrite H. rewrite H0. simpl. auto. Qed.

Lemma GEQ_SomeC: forall a b, geq a b -> geq (GSome a) (GSome b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_VNumC: forall a b, geq a b -> geq (GVNum a) (GVNum b).
Proof.  intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_toNatC: forall a b, geq a b -> geq (toNatG a) (toNatG b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_BindC: forall a1 a2 f1 f2,
    geq a1 a2 -> fgeq f1 f2 ->
    geq (a1 >>g= f1) (a2 >>g= f2).
Proof.
  intros.
  unfold GMatch. eapply GEQ_IfC. eapply GEQ_GetC. eauto. eapply H0. eapply GEQ_GetC. eauto. reflexivity.
Qed.

(* ----- and reduction rules ----- *)

Lemma GEQ_PlusR: forall a1 a2 n1 n2,
    geq a1 (GNum n1) -> geq a2 (GNum n2) -> geq (GPlus a1 a2) (GNum (n1 + n2)).
Proof. intros. eapply GEQ_trans. eapply GEQ_PlusC; eauto.  unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_SomeR: forall a b, geq a (GSome b) -> geq (GGet a fdata) b.
Proof. intros. eapply GEQ_trans. eapply GEQ_GetC; eauto. unfold geq in *. simpl. reflexivity. Qed. 

Lemma GEQ_BindSomeR: forall a b c f, geq a (GSome b) -> geq (f b) c -> fgeq f f -> geq (a >>g= f) c.
Proof. intros. eapply GEQ_trans. eapply GEQ_BindC; eauto.
       unfold GMatch. unfold fgeq in *. unfold geq in *. simpl. rewrite <-H0. 
       eapply H1. eapply GEQ_SomeR. reflexivity. Qed.

Lemma GEQ_BindNoneR: forall a f, geq a GNone -> geq (a >>g= f) GNone.
Proof.
  intros. unfold GMatch. unfold geq in *. simpl. rewrite H. simpl. reflexivity. 
Qed.

Lemma GEQ_toNatR: forall a b, geq a (GVNum b) -> geq (toNatG a) (GSome b).
Proof. intros. eapply GEQ_trans. eapply GEQ_toNatC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toNatBoolR: forall a b, geq a (GVBool b) -> geq (toNatG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toNatC. eauto. unfold geq in *. simpl. reflexivity. Qed. 

(*
Lemma GEQ_PlusR: forall n1 n2, geq (GPlus (GNum n1) (GNum n2)) (GNum (n1 + n2)).
Proof. intros. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_SomeR: forall a, geq (GGet (GSome a) fdata) a.
Proof. intros. unfold geq in *. simpl. reflexivity. Qed. 

Lemma GEQ_BindSomeR: forall a f, geq ((GSome a) >>g= f) (f (GGet (GSome a) fdata)).
Proof. intros. unfold GMatch. unfold geq in *. simpl. reflexivity. Qed. 

Lemma GEQ_BindNoneR: forall f, geq ((GNone) >>g= f) GNone.
Proof.
  intros. unfold GMatch. unfold geq in *. simpl. reflexivity. 
Qed.


Lemma GEQ_toNatR: forall a, geq (toNatG (GVNum a)) (GSome a).
Proof. 
  intros. unfold geq in *. simpl. reflexivity. 
Qed.

Lemma GEQ_toNatBoolR: forall a, geq (toNatG (GVBool a)) GNone.
Proof.
  intros. unfold geq in *. simpl. reflexivity.
Qed.
*)

(* ----- equivalence between IMP and FUN ----- *)

Inductive veq : val -> gxp -> Prop :=
| VEQ_Num : forall n r,
    geq r (GVNum (GNum n)) ->
    veq (VNum n) r
| VEQ_Bool : forall n r,
    geq  r (GVBool (GBool n)) ->
    veq (VBool n) r.

Inductive oeq {X:Type} (peq: X -> gxp -> Prop): option X -> gxp -> Prop :=
| REQ_Some : forall v g r,
    peq v g ->
    geq r (GSome g) ->
    oeq peq (Some v) r
| REQ_None : forall r,
    geq r GNone ->
    oeq peq None r.

Definition req := oeq veq.

Definition neq (n1: nat) (n2: gxp) := n2 = (GNum n1).

Lemma REQ_BindC: forall X Y (peq: X -> gxp -> Prop)  (qeq: Y -> gxp -> Prop) a1 a2 f1 f2,
    oeq peq a1 a2 ->
    (forall b1 b2, peq b1 b2 -> oeq qeq (f1 b1) (f2 b2)) ->
    (forall b c, geq b c -> geq (f2 b) (f2 c)) ->
    oeq qeq (a1 >>= f1) (a2 >>g= f2).
Proof.
  intros. inversion H; subst a1 r.
  - specialize (H0 _ _ H2). inversion H0; subst r.
    + eapply REQ_Some. eauto. eapply GEQ_BindSomeR; eauto.
    + eapply REQ_None. eapply GEQ_BindSomeR; eauto. 
  - eapply REQ_None. eapply GEQ_BindNoneR; eauto. 
Qed.

Lemma REQ_toNatC: forall (b0 : val) (b3 : gxp), veq b0 b3 -> oeq neq (toNat b0) (toNatG b3).
Proof.
  intros. inversion H; subst b0 r.
  - eapply REQ_Some. reflexivity. eapply GEQ_toNatR. eauto. 
  - eapply REQ_None. eapply GEQ_toNatBoolR. eauto. 
Qed.

(* ----- soundness of IMP -> FUN translation ----- *)

Theorem soundness: forall e,
    req (eval_exp e (empty_store)) (trans_exp e (GMap (t_empty None))).
Proof.
  intros e. induction e.
  - (* var *) simpl.  admit. (* fixme *)
  - (* num *) simpl. eapply REQ_Some. eapply VEQ_Num. reflexivity. reflexivity. 
  - (* plus *)
    simpl.

    (* eapply REQ_BindC. eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    intros. eapply REQ_BindC. eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    intros. eapply REQ_Some. eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_PlusR. reflexivity. reflexivity. rewrite H. rewrite H0. reflexivity.
    intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. reflexivity. eauto.
    intros. eapply GEQ_BindC. eapply GEQ_BindC. reflexivity. intros ? ? ?. eapply GEQ_toNatC. eauto. intros ? ? ?.
    eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. eauto. eauto. *)
    
    simpl eval_exp. simpl trans_exp.

    remember (eval_exp e1 empty_store) as a1.
    remember (eval_exp e2 empty_store) as a2.
    remember (trans_exp e1 (GMap (t_empty None))) as b1.
    remember (trans_exp e2 (GMap (t_empty None))) as b2.

    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)). eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)). eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    
    eapply REQ_BindC. eauto. intros. eapply REQ_BindC. eauto.
    intros. eapply REQ_Some. eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_PlusR. reflexivity. reflexivity. rewrite H1. rewrite H2. reflexivity.
    intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. reflexivity. eauto. 

    intros. eapply GEQ_BindC. reflexivity. intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. eauto. eauto. 

  - (* minus *) admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted. 

(* ---------- small-step rules for FUN: experimental / not currently used ---------- *)

(*NOTE: small-step not currently used *)
Inductive value : gxp -> Prop :=
| v_num : forall n, value (GNum n)
| v_bool : forall b, value (GBool b)
| v_obj: forall m, (forall x y, m x = Some y -> value y) -> value (GMap m).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : gxp -> gxp -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
          GPlus (GNum n1) (GNum n2)
      ==> GNum (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        GPlus t1 t2 ==> GPlus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        (* value v1 -> *)                     (* <----- n.b. *)
        t2 ==> t2' ->
        GPlus v1 t2 ==> GPlus v1 t2'

  where " t '==>' t' " := (step t t').

Definition relation (X: Type) := X->X->Prop.

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '==>*' t' " := (multi step t t') (at level 40).

(* small-step: not currently used *)
Theorem soundness1: forall e,
    exists g, (trans_exp e (GMap (t_empty None))) ==>* g /\
    req (eval_exp e (empty_store)) g.
Proof.
  intros e. induction e.
  - (* var *) simpl. admit. (* fixme: var case *)
  - (* num *) simpl. eexists. repeat econstructor.
  - (* plus *) simpl.
    remember (trans_exp e1 (GMap (t_empty None))) as a1.
    remember (trans_exp e2 (GMap (t_empty None))) as a2.
    remember (eval_exp e1 empty_store) as b1.
    remember (eval_exp e2 empty_store) as b2.
    unfold toNatG. unfold toNat. unfold GMatch. 

(*    
    destruct IHe1 as [g1 [T1 R1]]. destruct IHe2 as [g2 [T2 R2]].
    destruct (eval_exp e1 empty_store). inversion R1. subst b1 g1. 
    inversion H0. subst v g. simpl.

    destruct (eval_exp e2 empty_store). inversion R2. subst v0 g2.
    inversion H1. subst v g. simpl. 

    exists (GSome (GVNum (GNum (n + n0)))). split.
    {
      remember (trans_exp e1 (GMap (t_empty None))) as a1.
      remember (trans_exp e2 (GMap (t_empty None))) as a2.
      unfold toNatG. unfold GMatch. unfold GSome. unfold GNone. unfold GEmpty.
      admit. (* todo: reduction rules *)
    }
    repeat econstructor.
    + (* error: bool instead of nat *)
      exists GNone. subst v g. simpl. split. simpl.
      admit. (* reduction *)
      eapply REQ_None. 
 *)

Admitted.
