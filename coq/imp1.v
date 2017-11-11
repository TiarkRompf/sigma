(* code partly taken from Software Foundations Imp.v *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import Maps.

(* ---------- syntax ---------- *)

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

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".


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

Fixpoint eval_loop (b1 : exp) (c : stm) (st : store)(n : nat)(m : nat) (evstm: store -> option (option store))
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

Definition fval : id := Id "$val".
Definition ftpe : id := Id "$tpe".
Definition fvalid : id := Id "$valid".
Definition fdata : id := Id "$data".

Definition tnat : gxp := GNum 0.
Definition tbool : gxp := GNum 1.
Definition tloc : gxp := GNum 2.

Definition GEmpty : gxp := GMap (t_empty None).

Definition GNone : gxp := GPut GEmpty fvalid (GBool false).
Definition GSome a : gxp := GPut (GPut GEmpty fvalid (GBool true)) fdata a.

Definition GMatch (scrutinee: gxp) (none: gxp) (some: gxp -> gxp): gxp :=
  GIf (GGet scrutinee fvalid) none (some (GGet scrutinee fdata)).

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



Fixpoint trans_exp (e: exp) (sto: gxp): gxp :=
  match e with
  | AId x => GGet sto x
  | ANum n => GNum n
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


