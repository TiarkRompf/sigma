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

Definition total_map (A : Type) (B : Type) := A -> B.

Definition t_empty {A : Type} {B : Type} (v : B) : total_map A B :=
  (fun _ => v). 

Definition t_update {A B : Type} (beq : A -> A -> bool)
           (m : total_map A B) (x : A) (v : B) :=
  fun x' => if beq x x' then v else m x'. 

Definition partial_map (A : Type) (B : Type) := total_map A (option B).

Notation "a '⇀' b" := (partial_map a b) (at level 60, right associativity).

Definition empty {A : Type} {B : Type} : partial_map A B :=
  t_empty None.

Definition update {A B : Type} (beq : A -> A -> bool)
           (m : partial_map A B) (x : A) (v : B) :=
  t_update beq m x (Some v).

(* Source language IMP *)

(* Syntax *)

Inductive exp : Type :=
(* Constants *)
| EId : id -> exp
| ENum : nat -> exp
| EBool : bool -> exp
| ELoc : id -> exp
(* Arithmetics *)
| EPlus : exp -> exp -> exp
| EMinus : exp -> exp -> exp
| EMult : exp -> exp -> exp
(* Boolean *)
| ELt : exp -> exp -> exp
| EEq : exp -> exp -> exp
| EAnd : exp -> exp -> exp
| ENeg : exp -> exp
(* Field read *)
| EFieldRead : exp -> exp -> exp
.

Inductive stmt : Type :=
| SAlloc : id -> stmt (* TODO: size? *)
| SAssign : exp -> exp -> exp -> stmt
| SIf : exp -> stmt -> stmt -> stmt
| SWhile : exp -> stmt -> stmt
| SSeq : stmt -> stmt -> stmt
| SSkip : stmt
| SAbort : stmt
.

(* Syntatic sugar *)

(* TODO: x == &x[0] ? *)

Notation "x '::=' 'ALLOC'" :=
  (SAlloc x) (at level 80, right associativity).

Notation "x '::=' e" :=
  (SAssign x (ENum 0) e) (at level 80, right associativity).

Notation "s1 ;; s2" :=
  (SSeq s1 s2) (at level 80, right associativity).

Notation "'WHILE' b 'DO' s 'END'" :=
  (SWhile b s) (at level 80, right associativity).

Notation "'IF' e 'THEN' s1 'ELSE' s2 'FI'" :=
  (SIf e s1 s2) (at level 80, right associativity).

Notation "'SKIP'" := SSkip.

Notation "'ABORT'" := SAbort.

(* Context path *)

Inductive ctx : Type :=
| CRoot : ctx
| CThen : ctx -> ctx
| CElse : ctx -> ctx
| CFst  : ctx -> ctx          
| CSnd  : ctx -> ctx
| CWhile : ctx -> nat -> ctx
.

(* Store locations *)

Inductive loc : Type :=
| LId : id -> loc
| LNew : ctx -> loc
.

(* Values *)

Inductive val : Type :=
| VNum : nat -> val
| VBool : bool -> val
| VLoc : loc -> val
.

(* Context path equivalence *)

Fixpoint beq_ctx c1 c2 : bool :=
  match c1, c2 with
  | CRoot, CRoot => true
  | CThen c1, CThen c2 => beq_ctx c1 c2
  | CElse c1, CElse c2 => beq_ctx c1 c2
  | CFst c1, CFst c2 => beq_ctx c1 c2
  | CSnd c1, CSnd c2 => beq_ctx c1 c2
  | CWhile c1 n1, CWhile c2 n2 =>
    beq_ctx c1 c2 && beq_nat n1 n2
  | _, _ => false
  end.

(* Location equivalence *)

Fixpoint beq_loc l1 l2 : bool :=
  match l1, l2 with
  | LId id1, LId id2 => beq_id id1 id2
  | LNew c1, LNew c2 => beq_ctx c1 c2
  | _, _ => false
  end.

(* Objects *)

Definition obj := nat ⇀ val.

Definition mt_obj : obj := t_empty None.

(* Stores *)

Definition store := loc ⇀ obj.

Definition mt_store : store := t_empty None.

(* Monad operations *)

Definition toNat v :=
  match v with
  | VNum n => Some n
  | _      => None
  end.

Definition toBool v :=
  match v with
  | VBool b => Some b
  | _       => None
  end.

Definition toLoc v :=
  match v with
  | VLoc l => Some l
  | _      => None
  end.

Notation "x '←' e1 'IN' e2" :=
  (match e1 with
   | Some x => e2
   | None   => None
   end)
  (at level 60, right associativity).

Notation "x '↩' e1 'IN' e2" :=
  (match e1 with
   | Some (Some x) => e2
   | Some None     => Some None
   | None          => None
   end)
  (at level 60, right associativity).

Notation "e1 '>>=' e2" :=
  (match e1 with
   | Some x => e2 x
   | None   => None
   end)
  (at level 80, right associativity).

Notation "e1 '>>>=' e2" :=
  (match e1 with
   | Some (Some x) => e2 x
   | Some None     => Some None
   | None          => None
   end)
  (at level 80, right associativity).

(* IMP Evaluation *)

Fixpoint eval_exp (e: exp) (σ: store) : option val :=
  match e with
  | EId x  => o ← (σ (LId x)) IN o 0
  | ENum n => Some (VNum n)
  | EBool b => Some (VBool b)
  | ELoc x => Some (VLoc (LId x))
  | EPlus x y =>
    a ← eval_exp x σ >>= toNat IN
    b ← eval_exp y σ >>= toNat IN
    Some (VNum (a + b))
  | EMinus x y =>
    a ← eval_exp x σ >>= toNat IN
    b ← eval_exp y σ >>= toNat IN
    Some (VNum (a - b))
  | EMult x y =>
    a ← eval_exp x σ >>= toNat IN
    b ← eval_exp y σ >>= toNat IN
    Some (VNum (a * b))
  | ELt x y =>
    a ← eval_exp x σ >>= toNat IN
    b ← eval_exp y σ >>= toNat IN
    Some (VBool (a <? b))
  | EEq x y =>
    a ← eval_exp x σ >>= toNat IN
    b ← eval_exp y σ >>= toNat IN
    Some (VBool (a =? b))
  | EAnd x y =>
    a ← eval_exp x σ >>= toBool IN
    b ← eval_exp y σ >>= toBool IN
    Some (VBool (andb a b))
  | ENeg x =>
    a ← eval_exp x σ >>= toBool IN
    Some (VBool (negb a))
  | EFieldRead e1 e2 =>
    l ← eval_exp e1 σ >>= toLoc IN
    n ← eval_exp e2 σ >>= toNat IN
    o ← σ l IN
    o n
  end.

(* TODO: out-of-fuel or error? *)

Fixpoint idx1 (i : nat) (m : nat) (p : nat -> option bool) : option nat :=
  match m with
  | O => None
  | S m' =>
    b ← p i IN
    if b then Some i else idx1 (i + 1) m' p
  end.

Fixpoint idx (m : nat) (p : nat -> option bool) : option nat :=
  idx1 0 m p.
