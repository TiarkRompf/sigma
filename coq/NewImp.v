(* code partly taken from Software Foundations Imp.v *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Utf8.
Import ListNotations.

(* Maps *)

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

(* IMP Syntax *)

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

Definition fieldId (x : id) : nat :=
  match x with
  | Id n => n
  end.

Notation "e '·' x" :=
  (EFieldRead e (ENum (fieldId x))) (at level 80, right associativity).

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

Notation "e1 '[[' e2 ']]' '::=' e3" :=
  (SAssign e1 e2 e3) (at level 80, right associativity).

Notation "e1 '[[' e2 ']]'" :=
  (EFieldRead e1 e2) (at level 80, right associativity).

Notation "'ASSERT' e" :=
  (SIf e SSkip SAbort) (at level 80, right associativity).

Notation "'TRUE'" := (EBool true).

Notation "'FALSE'" := (EBool false).

Notation "'SKIP'" := SSkip.

Notation "'ABORT'" := SAbort.

(* Context path *)

Inductive path : Type :=
| PRoot : path
| PThen : path -> path
| PElse : path -> path
| PFst  : path -> path
| PSnd  : path -> path
| PWhile : path -> nat -> path
.

(* Store locations *)

Inductive loc : Type :=
| LId : id -> loc
| LNew : path -> loc
.

(* Context path equivalence *)

Fixpoint beq_path c1 c2 : bool :=
  match c1, c2 with
  | PRoot, PRoot => true
  | PThen c1, PThen c2 => beq_path c1 c2
  | PElse c1, PElse c2 => beq_path c1 c2
  | PFst c1, PFst c2 => beq_path c1 c2
  | PSnd c1, PSnd c2 => beq_path c1 c2
  | PWhile c1 n1, PWhile c2 n2 =>
    beq_path c1 c2 && beq_nat n1 n2
  | _, _ => false
  end.

(* Location equivalence *)

Fixpoint beq_loc l1 l2 : bool :=
  match l1, l2 with
  | LId id1, LId id2 => beq_id id1 id2
  | LNew c1, LNew c2 => beq_path c1 c2
  | _, _ => false
  end.

(* IMP Relational big-step semantics *)

Module IMPRel.

  (* Values *)

  Inductive val : Type :=
  | VNum : nat -> val
  | VBool : bool -> val
  | VLoc : loc -> val
  | VErr : val
  (* TODO: explicitly model error/undef/divergence? Related, the relational semantics for Abort *)
  .

  (* Objects *)

  Definition obj := nat → val. (* TODO: model partialness? *)

  Definition mt_obj : obj := t_empty VErr.
  Definition o0 : obj := mt_obj.

  Definition obj_update (st : obj) (x : nat) (v : val) :=
    t_update beq_nat st x v.

  Notation "x 'obj↦' v ; m" := (obj_update m x v) (at level 60, v at next level, right associativity).
  Notation "x 'obj↦' v" := (obj_update mt_obj x v) (at level 60).

  (* Stores *)

  Definition store := loc → obj.

  Definition mt_store : store := t_empty mt_obj.
  Definition σ0 : store := mt_store. (* TODO: Follow Def 3.4 *)

  Definition store_update (st : store) (x : loc) (v : obj) :=
    t_update beq_loc st x v.

  Notation "x 'st↦' v ';' m" := (store_update m x v)
    (at level 60, v at next level, right associativity).
  Notation "x 'st↦' v" := (store_update mt_store x v) (at level 60).

  (* Evaluation relation for expressions *)

  Definition VNumArith (op : nat → nat → nat) n1 n2 : val :=
    match n1, n2 with
    | (VNum x), (VNum y) => VNum (op x y)
    | _, _ => VErr
    end.

  Definition VNumPlus : val → val → val := VNumArith plus.
  Definition VNumMinus : val → val → val := VNumArith minus.
  Definition VNumMult : val → val → val := VNumArith mult.

  Definition VNumComp (op : nat → nat → bool) n1 n2 : val :=
    match n1, n2 with
    | (VNum x), (VNum y) => VBool (op x y)
    | _, _ => VErr
    end.

  Definition VNumLt : val → val → val := VNumComp Nat.ltb.
  Definition VNumEq : val → val → val := VNumComp Nat.eqb.

  Definition VBoolAnd b1 b2 : val :=
    match b1, b2 with
    | (VBool b1), (VBool b2) => VBool (andb b1 b2)
    | _, _ => VErr
    end.

  Definition VBoolNed b : val :=
    match b with
    | VBool b => VBool (negb b)
    | _ => VErr
    end.

  Definition fieldRead (σ : store) (l : val) (i : val) : val :=
    match l, i with
    | (VLoc l), (VNum n) => σ l n
    | _, _ => VErr
    end.

  Reserved Notation "st '⊢' e '⇓ₑ' v" (at level 90, left associativity).

  Inductive evalExpR : store → exp → val → Prop :=
  | RId x :  ∀ σ, σ ⊢ (EId x) ⇓ₑ (σ (LId x)) 0
  | RNum n : ∀ σ, σ ⊢ (ENum n) ⇓ₑ (VNum n)
  | RBool b : ∀ σ, σ ⊢ (EBool b) ⇓ₑ (VBool b)
  | RLoc x : ∀ σ, σ ⊢ (ELoc x) ⇓ₑ (VLoc (LId x))
  | RPlus x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ n1 →
      σ ⊢ y ⇓ₑ n2 →
      σ ⊢ (EPlus x y) ⇓ₑ (VNumPlus n1 n2)
  | RMinus x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ n1 →
      σ ⊢ y ⇓ₑ n2 →
      σ ⊢ (EMinus x y) ⇓ₑ (VNumMinus n1 n2)
  | RMult x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ n1 →
      σ ⊢ y ⇓ₑ n2 →
      σ ⊢ (EMult x y) ⇓ₑ (VNumMult n1 n2)
  | RLt x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ n1 →
      σ ⊢ y ⇓ₑ n2 →
      σ ⊢ (ELt x y) ⇓ₑ (VNumLt n1 n2)
  | REq x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ n1 →
      σ ⊢ y ⇓ₑ n2 →
      σ ⊢ (EEq x y) ⇓ₑ (VNumEq n1 n2)
  | RAnd x y : ∀ σ b1 b2,
      σ ⊢ x ⇓ₑ b1 →
      σ ⊢ y ⇓ₑ b2 →
      σ ⊢ (EAnd x y) ⇓ₑ (VBoolAnd b1 b2)
  | RNeg x : ∀ σ b,
      σ ⊢ x ⇓ₑ b →
      σ ⊢ (ENeg x) ⇓ₑ (VBoolNed b)
  | RFieldRead e1 e2 : ∀ σ l n,
      σ ⊢ e1 ⇓ₑ l →
      σ ⊢ e2 ⇓ₑ n →
      σ ⊢ (EFieldRead e1 e2) ⇓ₑ (fieldRead σ l n)
  where "st '⊢' e '⇓ₑ' v" := (evalExpR st e v) : type_scope.

  Reserved Notation "( st1 , c ) '⊢' ( e , s ) n '⇓∞' st2" (at level 90, left associativity).
  Reserved Notation "( st1 , c ) '⊢' s '⇓' st2" (at level 90, left associativity).

  Inductive evalLoopR : store → path → exp → stmt → nat → store → Prop :=
  | RWhileZero : ∀ σ c e s,
      (σ, c) ⊢ (e, s) 0 ⇓∞ σ
  (* | RWhileFalse : ∀ σ c e s n,
      σ ⊢ e ⇓ₑ (VBool false) → (* Note: is it necessary? *)
      (σ, c) ⊢ (e, s) n ⇓∞ σ *)
  | RWhileMore : ∀ (σ σ' σ'' : store) c n e s,
      (σ, c) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool true) →
      (σ', PWhile c n) ⊢ s ⇓ σ'' →
      (σ, c) ⊢ (e, s) n+1 ⇓∞ σ''
  where "( st1 , c ) ⊢ ( e , s ) n '⇓∞' st2" := (evalLoopR st1 c e s n st2) : type_scope
  with evalStmtR : store → path → stmt → store → Prop :=
  | RAlloc x : ∀ σ p,
      (σ, p) ⊢ x ::= ALLOC ⇓ (LNew p st↦ mt_obj ;
                              LId x  st↦ (0 obj↦ VLoc (LNew p)) ;
                              σ)
  | RAssign e1 e2 e3 : ∀ σ p l idx v,
      σ ⊢ e1 ⇓ₑ (VLoc l) →
      σ ⊢ e2 ⇓ₑ (VNum idx) →
      σ ⊢ e3 ⇓ₑ v →
      (σ, p) ⊢ e1[[e2]] ::= e3 ⇓ (l st↦ (idx obj↦ v ; σ l) ; σ)
  | RIfTrue e s1 s2 : ∀ σ p σ',
      σ ⊢ e ⇓ₑ (VBool true) →
      (σ, PThen p) ⊢ s1 ⇓ σ' →
      (σ, p) ⊢ SIf e s1 s2 ⇓ σ' (* FIXME: the notation doesn't work here *)
  | RIfFalse e s1 s2 : ∀ σ p σ',
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, PElse p) ⊢ s2 ⇓ σ' →
      (σ, p) ⊢ SIf e s1 s2 ⇓ σ'
  | RWhile e s : ∀ σ p σ' n,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ WHILE e DO s END ⇓ σ'
  | RSeq s1 s2 : ∀ σ p σ' σ'',
      (σ,  PFst p) ⊢ s1 ⇓ σ' →
      (σ', PSnd p) ⊢ s2 ⇓ σ'' →
      (σ, p) ⊢ s1 ;; s2 ⇓ σ''
  | RSkip : ∀ σ p, (σ, p) ⊢ SKIP ⇓ σ
  | RAbort : ∀ σ p, (σ, p) ⊢ ABORT ⇓ σ0
  where "( st1 , c ) '⊢' s '⇓' st2" := (evalStmtR st1 c s st2) : type_scope.

  Inductive result : stmt → Prop :=
  | ResStore : ∀ σ p s,
      (σ0, p) ⊢ s ⇓ σ → result s
  | ResError : ∀ s, result s
  | ResDiverge : ∀ s, result s
  .

  (* TODO: clean up this *)
  Theorem exp_deterministic : ∀ σ e v1 v2,
      σ ⊢ e ⇓ₑ v1 →
      σ ⊢ e ⇓ₑ v2 →
      v1 = v2.
  Proof.
    intros σ e v1 v2 E1 E2.
    generalize dependent v2.
    induction E1; intros; inversion E2; subst; auto.
    - specialize IHE1_1 with (v2 := n0).
      specialize IHE1_2 with (v2 := n3).
      assert (n1 = n0). apply IHE1_1. apply H2.
      assert (n2 = n3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := n0).
      specialize IHE1_2 with (v2 := n3).
      assert (n1 = n0). apply IHE1_1. apply H2.
      assert (n2 = n3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := n0).
      specialize IHE1_2 with (v2 := n3).
      assert (n1 = n0). apply IHE1_1. apply H2.
      assert (n2 = n3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := n0).
      specialize IHE1_2 with (v2 := n3).
      assert (n1 = n0). apply IHE1_1. apply H2.
      assert (n2 = n3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := n0).
      specialize IHE1_2 with (v2 := n3).
      assert (n1 = n0). apply IHE1_1. apply H2.
      assert (n2 = n3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := b0).
      specialize IHE1_2 with (v2 := b3).
      assert (b1 = b0). apply IHE1_1. apply H2.
      assert (b2 = b3). apply IHE1_2. apply H4.
      subst. reflexivity.
    - specialize IHE1 with (v2 := b0).
      assert (b = b0). apply IHE1. apply H1.
      subst. reflexivity.
    - specialize IHE1_1 with (v2 := l0).
      specialize IHE1_2 with (v2 := n0).
      assert (l = l0). apply IHE1_1. apply H2.
      assert (n = n0). apply IHE1_2. apply H4.
      subst. reflexivity.
  Qed.

  Lemma loop0_store_inv : ∀ σ σ' p e s,
      (σ, p) ⊢ (e, s) 0 ⇓∞ σ' →
      σ = σ'.
  Proof.
    intros. inversion H. auto. auto. omega.
  Qed.

  Lemma loop_false_store_inv : ∀ σ σ' p e s n,
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ = σ'.
  Proof.
    intros. induction H0. auto. auto. assert (σ ⊢ e ⇓ₑ VBool false) as H'.
    auto. apply IHevalLoopR in H. subst.
    assert (VBool false = VBool true). eapply exp_deterministic. eauto. eauto.
    discriminate H.
  Qed.

  Lemma succ_eq : forall x y : nat, x + 1 = y + 1 <-> x = y.
  Proof.
    intros. split.
    - intros. induction x. inversion H. omega. omega.
    - intros. subst. reflexivity.
  Qed.

  Theorem loop_determinisitc : ∀ σ p e s n σ' σ'',
      (σ, p) ⊢ (e, s) n ⇓∞ σ'  →
      (σ, p) ⊢ (e, s) n ⇓∞ σ'' →
      σ' = σ''
  with stmt_deterministic : ∀ σ p s σ' σ'',
      (σ, p) ⊢ s ⇓ σ'  →
      (σ, p) ⊢ s ⇓ σ'' →
      σ' = σ''.
  Proof.
    (* loop determinisitc *)
    - intros σ p e s n σ' σ'' E1 E2.
      generalize dependent σ''. induction E1.
      + intros. subst. inversion E2. auto. auto. omega.
      (* + intros. inversion E2. auto. subst. omega.
           induction n0.
           * assert (σ = σ'). { eapply loop0_store_inv. eauto. } subst.
             assert (VBool true = VBool false). { eapply exp_deterministic. eauto. eauto. } inversion H3.
           * eapply loop_false_store_inv. eauto. eauto. *)
      + intros. inversion E2.
        * subst. omega.
        (* * subst. assert (σ''0 = σ').
          { eapply loop_false_store_inv. eauto. eauto. }
          subst. assert (VBool true = VBool false).
          { eapply exp_deterministic. eauto. eauto. }
          inversion H2. *)
        * subst. rewrite succ_eq in H1. subst.
          specialize IHE1 with (σ'' := σ'0).
          apply IHE1 in H2. subst.
          eapply stmt_deterministic. eauto. eauto.
    (* stmt determinisitc *)
    - intros σ p s σ' σ'' E1 E2.
      generalize dependent σ''.
      induction E1; intros; inversion E2; auto.
      + assert (VLoc l = VLoc l0) as LEq. { eapply exp_deterministic. eauto. auto. } inversion LEq.
        assert (VNum idx = VNum idx0) as NEq. { eapply exp_deterministic. eauto. auto. } inversion NEq.
        assert (v = v0). { eapply exp_deterministic. eauto. auto. } subst. reflexivity.
      + assert (VBool true = VBool false) as BEq.
        { eapply exp_deterministic. eauto. auto. } inversion BEq.
      + assert (VBool true = VBool false) as BEq.
        { eapply exp_deterministic. eauto. auto. } inversion BEq.
      + assert (n = n0). { admit. } eapply loop_determinisitc. eauto. subst.
        assert (σ' = σ''). { eapply loop_determinisitc. eauto. eauto. } subst. auto.
      + specialize IHE1_1 with (σ'' := σ'0).
        specialize IHE1_2 with (σ''0 := σ''0).
        assert (σ' = σ'0). { apply IHE1_1. apply H3. } subst.
        assert (σ'' = σ''0). { apply IHE1_2. apply H5. } apply H.
  Admitted.


End IMPRel.

(* IMP Standard semantics, without context path *)

Module IMPStd.

End IMPStd.

(* IMP Monadic functional semantics *)

Module IMPEval.

  Inductive val : Type :=
  | VNum : nat -> val
  | VBool : bool -> val
  | VLoc : loc -> val
  .

  (* Objects *)

  Definition obj := nat ⇀ val.

  Definition mt_obj : obj := t_empty None.

  Definition obj_update (st : obj) (x : nat) (v : val) :=
    t_update beq_nat st x (Some v).

  (* Stores *)

  Definition store := loc ⇀ obj.

  Definition mt_store : store := t_empty None.

  Definition store_update (st : store) (x : loc) (v : obj) :=
    t_update beq_loc st x (Some v).

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

  (* IMP Evaluation function *)

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
  
  Fixpoint eval_loop (b1: exp) (s: stmt) (σ: store) (c: path) (n: nat) (m: nat)
           (evstmt: store -> path -> option store) : option store :=
    match n with
    | O => Some σ
    | S n' =>
      σ' ← eval_loop b1 s σ c n' m evstmt IN
      b ← eval_exp b1 σ' >>= toBool IN
      if b then evstmt σ' (PWhile c n') else None (* error or timeout ??? *)
    end.

  Fixpoint eval_stm (s: stmt) (σ: store) (c: path) (m: nat) : option store :=
    match s with
    | x ::= ALLOC =>
      Some (store_update (store_update σ (LNew c) mt_obj)
                         (LId x)
                         (obj_update mt_obj 0 (VLoc (LNew c))))
    | SAssign e1 e2 e3 =>
      l ← eval_exp e1 σ >>= toLoc IN
      n ← eval_exp e2 σ >>= toNat IN
      v ← eval_exp e3 σ IN
      o ← σ l IN
      Some (store_update σ l (obj_update o n v))
    | IF b THEN s1 ELSE s2 FI =>
      b ← eval_exp b σ >>= toBool IN
      if b
      then eval_stm s1 σ (PThen c) m
      else eval_stm s2 σ (PElse c) m
    | WHILE b1 DO s1 END =>
      n ← idx m (fun i =>
                   match (σ' ← eval_loop b1 s1 σ c i m (fun σ'' c1 => eval_stm s1 σ'' c1 m) IN
                          b ← eval_exp b1 σ' >>= toBool IN
                          Some (negb b)) with
                   | Some b => Some b
                   | None => Some true end
                (* TODO: cleanup slightly. inline eval_loop? *)
                ) IN
      eval_loop b1 s1 σ c n m (fun σ' c1 => eval_stm s1 σ' c1 m)
    | s1 ;; s2 =>
      σ' ← eval_stm s1 σ (PFst c) m IN
      eval_stm s2 σ' (PSnd c) m
    | SKIP =>
      Some σ
    | SAbort => None
    end.

End IMPEval.
