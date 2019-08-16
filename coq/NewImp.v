(* code partly taken from Software Foundations Imp.v *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Utf8.
Import ListNotations.

Lemma succ_eq : forall x y : nat, x + 1 = y + 1 <-> x = y.
Proof.
  intros. split.
  - intros. induction x. inversion H. omega. omega.
  - intros. subst. reflexivity.
Qed.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => 
    match m with
    | O => false
    | S m' => ble_nat n' m'
    end
  end.

Definition blt_nat (n m : nat) : bool := andb (negb (beq_nat n m)) (ble_nat n m).

Lemma beq_reflect : ∀ x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply beq_nat_true_iff.
Qed.

Lemma blt_reflect : ∀ x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : ∀ x y, reflect (x ≤ y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                    assert (H: reflect e X); subst e;
                    [eauto with bdestruct
                    | destruct H as [H|H];
                      [ | try first [apply not_lt in H | apply not_le in H] ] ].

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

Lemma t_update_eq : forall { A B : Type } beq (m : total_map A B) x v,
  (t_update beq m x v) x = v.
Proof. Admitted.

Lemma t_update_neq : forall { A B : Type } beq (m : total_map A B) x y v,
  x <> y ->
  (t_update beq m x v) y = m y.
Proof. Admitted.

Lemma t_update_shadow : forall { A B : Type } beq (m : total_map A B) x v1 v2,
  (t_update beq (t_update beq m x v1) x v2) = t_update beq m x v2.
Proof. Admitted.

Lemma t_update_same : forall { A B : Type } beq (m : total_map A B) x,
  t_update beq m x (m x) = m.
Proof. Admitted.

Lemma t_update_permute : forall { A B : Type } beq (m : total_map A B) x y v1 v2,
  x <> y ->
  (t_update beq (t_update beq m x v1) y v2) = (t_update beq (t_update beq m y v2) x v1).
Proof. Admitted.

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
(* | EId : id -> exp *)
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

Notation "'σ[' x ']'" := (EFieldRead (ELoc x) (ENum 0)) (at level 70).

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
  (SSeq s1 s2) (at level 85, right associativity).

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

Lemma loc_dec : forall (l1 l2 : loc), l1 = l2 \/ l1 <> l2.
Proof.
Admitted.

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

Lemma beq_loc_eq: forall l, beq_loc l l = true.
Proof.
Admitted.

(* Values *)

Inductive val : Type :=
| VNum : nat -> val
| VBool : bool -> val
| VLoc : loc -> val
.

(* Objects *)

Definition obj := nat ⇀ val. (* TODO: model partialness? *)

Definition mt_obj : obj := t_empty None.
Definition o0 : obj := mt_obj.

Definition obj_update (st : obj) (x : nat) (v : val) :=
  t_update beq_nat st x (Some v).

Notation "x 'obj↦' v ; m" := (obj_update m x v) (at level 15, v at next level, right associativity).
Notation "x 'obj↦' v" := (obj_update mt_obj x v) (at level 15).

(* Stores *)

Definition store := loc ⇀ obj.

Definition mt_store : store := t_empty None.
Definition σ0 : store := fun k =>
                           match k with
                           | LId x => Some mt_obj
                           | LNew p => None
                           end.

Definition store_update (st : store) (x : loc) (v : obj) :=
  t_update beq_loc st x (Some v).

Notation "x 'st↦' v ';' m" := (store_update m x v)
                                (at level 15, v at next level, right associativity).
Notation "x 'st↦' v" := (store_update mt_store x v) (at level 15).

(* IMP Relational big-step semantics *)

Module IMPRel.
  (* Evaluation relation for expressions *)

  Reserved Notation "st '⊢' e '⇓ₑ' v" (at level 15).

  Inductive evalExp : store → exp → val → Prop :=
  (* | RId x :  ∀ σ, σ ⊢ (EId x) ⇓ₑ (σ (LId x)) 0 *)
  | RNum n : ∀ σ, σ ⊢ (ENum n) ⇓ₑ (VNum n)
  | RBool b : ∀ σ, σ ⊢ (EBool b) ⇓ₑ (VBool b)
  | RLoc x : ∀ σ, σ ⊢ (ELoc x) ⇓ₑ (VLoc (LId x))
  | RPlus x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ (VNum n1) →
      σ ⊢ y ⇓ₑ (VNum n2) →
      σ ⊢ (EPlus x y) ⇓ₑ VNum (n1 + n2)
  | RMinus x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ (VNum n1) →
      σ ⊢ y ⇓ₑ (VNum n2) →
      σ ⊢ (EMinus x y) ⇓ₑ VNum (n1 - n2)
  | RMult x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ (VNum n1) →
      σ ⊢ y ⇓ₑ (VNum n2) →
      σ ⊢ (EMult x y) ⇓ₑ VNum (n1 * n2)
  | RLt x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ (VNum n1) →
      σ ⊢ y ⇓ₑ (VNum n2) →
      σ ⊢ (ELt x y) ⇓ₑ VBool (Nat.ltb n1 n2)
  | REq x y : ∀ σ n1 n2,
      σ ⊢ x ⇓ₑ (VNum n1) →
      σ ⊢ y ⇓ₑ (VNum n2) →
      σ ⊢ (EEq x y) ⇓ₑ VBool (Nat.eqb n1 n2)
  | RAnd x y : ∀ σ b1 b2,
      σ ⊢ x ⇓ₑ (VBool b1) →
      σ ⊢ y ⇓ₑ (VBool b2) →
      σ ⊢ (EAnd x y) ⇓ₑ VBool (andb b1 b2)
  | RNeg x : ∀ σ b,
      σ ⊢ x ⇓ₑ (VBool b) →
      σ ⊢ (ENeg x) ⇓ₑ VBool (negb b)
  | RFieldRead e1 e2 : ∀ σ l n o v,
      σ ⊢ e1 ⇓ₑ (VLoc l) →
      σ ⊢ e2 ⇓ₑ (VNum n) →
      σ l = Some o →
      o n = Some v →
      σ ⊢ (EFieldRead e1 e2) ⇓ₑ v
  where "st '⊢' e '⇓ₑ' v" := (evalExp st e v) : type_scope.

  Reserved Notation "'(' st1 , c ')' '⊢' '(' e , s ')' n '⇓∞' st2" (at level 15).
  Reserved Notation "( st1 , c ) '⊢' s '⇓' st2" (at level 15).

  Inductive evalLoop : store → path → exp → stmt → nat → store → Prop :=
  | RWhileZero : ∀ σ c e s,
      (σ, c) ⊢ (e, s) 0 ⇓∞ σ
  | RWhileMore : ∀ (σ σ' σ'' : store) c n e s,
      (σ, c) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool true) →
      (σ', PWhile c n) ⊢ s ⇓ σ'' →
      (σ, c) ⊢ (e, s) 1+n ⇓∞ σ''
  where "( st1 , c ) ⊢ ( e , s ) n '⇓∞' st2" := (evalLoop st1 c e s n st2) : type_scope
  with evalStmt : store → path → stmt → store → Prop :=
  | RAlloc x : ∀ σ p,
      (σ, p) ⊢ x ::= ALLOC ⇓ (LNew p st↦ mt_obj ;
                              LId x  st↦ (0 obj↦ VLoc (LNew p)) ;
                              σ)
  | RAssign e1 e2 e3 : ∀ σ p l idx v o,
      σ ⊢ e1 ⇓ₑ (VLoc l) →
      σ ⊢ e2 ⇓ₑ (VNum idx) →
      σ ⊢ e3 ⇓ₑ v →
      σ l = Some o →
      (σ, p) ⊢ e1[[e2]] ::= e3 ⇓ (l st↦ (idx obj↦ v ; o) ; σ)
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
  where "( st1 , c ) '⊢' s '⇓' st2" := (evalStmt st1 c s st2) : type_scope.

  Scheme evalLoopRelMut := Induction for evalLoop Sort Prop
    with evalStmtRelMut := Induction for evalStmt Sort Prop.

  (* TODO: clean up this *)
  Theorem exp_deterministic : ∀ σ e v1 v2,
      σ ⊢ e ⇓ₑ v1 →
      σ ⊢ e ⇓ₑ v2 →
      v1 = v2.
  Proof.
    intros σ e v1 v2 E1 E2.
    generalize dependent v2.
    induction E1; intros; inversion E2; subst; auto.
    - specialize IHE1_1 with (v2 := VNum n0).
      specialize IHE1_2 with (v2 := VNum n3).
      assert (VNum n1 = VNum n0). apply IHE1_1. apply H2.
      assert (VNum n2 = VNum n3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VNum n0).
      specialize IHE1_2 with (v2 := VNum n3).
      assert (VNum n1 = VNum n0). apply IHE1_1. apply H2.
      assert (VNum n2 = VNum n3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VNum n0).
      specialize IHE1_2 with (v2 := VNum n3).
      assert (VNum n1 = VNum n0). apply IHE1_1. apply H2.
      assert (VNum n2 = VNum n3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VNum n0).
      specialize IHE1_2 with (v2 := VNum n3).
      assert (VNum n1 = VNum n0). apply IHE1_1. apply H2.
      assert (VNum n2 = VNum n3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VNum n0).
      specialize IHE1_2 with (v2 := VNum n3).
      assert (VNum n1 = VNum n0). apply IHE1_1. apply H2.
      assert (VNum n2 = VNum n3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VBool b0).
      specialize IHE1_2 with (v2 := VBool b3).
      assert (VBool b1 = VBool b0). apply IHE1_1. apply H2.
      assert (VBool b2 = VBool b3). apply IHE1_2. apply H4.
      inversion H. inversion H0. subst. reflexivity.
    - specialize IHE1 with (v2 := VBool b0).
      assert (VBool b = VBool b0). apply IHE1. apply H1.
      inversion H. subst. reflexivity.
    - specialize IHE1_1 with (v2 := VLoc l0).
      specialize IHE1_2 with (v2 := VNum n0).
      assert (VLoc l = VLoc l0). apply IHE1_1. apply H3.
      assert (VNum n = VNum n0). apply IHE1_2. apply H4.
      inversion H1. inversion H2. subst.
      remember (σ l0) as σl. rewrite H6 in H. inversion H. subst.
      remember (o n0) as on. rewrite H0 in H8. inversion H8. reflexivity.
Qed.

  Lemma loop0_store_inv : ∀ σ σ' p e s,
      (σ, p) ⊢ (e, s) 0 ⇓∞ σ' →
      σ = σ'.
  Proof.
    intros. inversion H. auto.
Qed.

  Lemma loop_false_store_inv : ∀ σ σ' p e s n,
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ = σ'.
  Proof.
    intros. induction H0. auto. auto. assert (σ ⊢ e ⇓ₑ VBool false) as H'.
    auto. apply IHevalLoop in H. subst.
    assert (VBool false = VBool true). eapply exp_deterministic. eauto. eauto.
    discriminate H.
Qed.

  Lemma loop_false_inv : ∀ σ σ' p e s n v,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ ⊢ e ⇓ₑ (VBool false) →
      σ' ⊢ e ⇓ₑ (VBool v) →
      false = v.
  Proof.
    intros. assert (σ = σ'). eapply loop_false_store_inv. eauto. eauto.
    subst. assert (VBool false = VBool v). eapply exp_deterministic.
    eauto. eauto. inversion H2. reflexivity.
Qed.
  
  Theorem loop_false_store_inv3 : ∀ σ σ' σ'' p e s n m,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      m >= n →
      (σ', p) ⊢ (e, s) m ⇓∞ σ'' →
      (σ', p) ⊢ (e, s) m+1 ⇓∞ σ'' →
      σ' = σ''.
  Proof.
  Admitted.

  Theorem loop_false_store_inv4 : ∀ σ σ1 σ2 σ3 p e s n a b,
      (σ, p) ⊢ (e, s) n ⇓∞ σ1 →
      σ1 ⊢ e ⇓ₑ (VBool false) →
      (σ1, p) ⊢ (e, s) a ⇓∞ σ2 →
      (σ1, p) ⊢ (e, s) b ⇓∞ σ3 →
      σ1 = σ2 ∧ σ1 = σ3.
  Proof.
    intros. split. 
    - eapply loop_false_store_inv. eauto. eauto.
    - eapply loop_false_store_inv. eauto. eauto.
Qed.
         
  Lemma loop0_deterministic : ∀ σ p e s σ' σ'',
      (σ, p) ⊢ (e, s) 0 ⇓∞ σ'  →
      (σ, p) ⊢ (e, s) 0 ⇓∞ σ'' →
      σ' = σ''.
  Proof.
    intros.
    assert (σ = σ'). eapply loop0_store_inv. eauto.
    assert (σ = σ''). eapply loop0_store_inv. eauto.
    subst. reflexivity.
Qed.

  Lemma loop_sigma_exists : ∀ n σ p e s,
      ∃ σ', (σ, p) ⊢ (e, s) n ⇓∞ σ'.
  Proof.
Admitted.

  Lemma loop_false_store_contra : ∀ σ σ' p e s n,
      σ ⊢ e ⇓ₑ (VBool false) →
      n > 0 →
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      False.
  Proof.
    intros. generalize dependent σ'. induction n; intros.
    omega.
    inversion H1; subst.
    destruct n. inversion H3; subst.
    assert (VBool false = VBool true).
    eapply exp_deterministic. eauto. eauto. inversion H2.
    eapply IHn. omega. apply H3.
Qed.

  Lemma loop_Sn_cond_true : ∀ n e s p σ σ',
      (σ, p)⊢ (e, s) 1 + n ⇓∞ σ' → σ ⊢ e ⇓ₑ (VBool true).
  Proof.
    intro n. induction n; intros.
    - inversion H. subst. eapply loop0_store_inv in H1. subst. assumption.
    - inversion H; subst. eapply IHn.
      assert (S n = 1 + n). omega. rewrite <- H0. eapply H1.
Qed.
      
  Lemma skip_store_inv : ∀ p σ σ',
      (σ, p)⊢ SKIP ⇓ σ' → σ = σ'.
  Proof.
    intros. inversion H. subst. reflexivity.
Qed.

  Theorem stmt_deterministic : ∀ s σ σ' σ'' p,
      (σ, p) ⊢ s ⇓ σ'  →
      (σ, p) ⊢ s ⇓ σ'' →
      σ' = σ''.
  Proof.
    intros s. induction s; intros. inversion H; inversion H0; subst; auto.
    - inversion H; inversion H0; subst.
      assert (v = v0). eapply exp_deterministic. eauto. eauto. subst.
      assert (VLoc l = VLoc l0). eapply exp_deterministic. eauto. eauto. inversion H1. subst.
      assert (VNum idx = VNum idx0). eapply exp_deterministic. eauto. eauto. inversion H2.
      subst. rewrite H10 in H20. inversion H20. subst. reflexivity.
    - inversion H; inversion H0; subst.
      + eapply IHs1. eauto. eauto.
      + assert (VBool false = VBool true). eapply exp_deterministic. eauto. eauto.
        inversion H1.
      + assert (VBool false = VBool true). eapply exp_deterministic. eauto. eauto.
        inversion H1.
      + eapply IHs2. eauto. eauto.
    - assert (∀ m σ' σ'', (σ, p)⊢ (e, s) m ⇓∞ σ' →
                          (σ, p)⊢ (e, s) m ⇓∞ σ'' →
                          σ' = σ'') as loop_deterministic.
      { intro m. induction m; intros.
        - assert (σ = σ'0). eapply loop0_store_inv. eauto.
          assert (σ = σ''0). eapply loop0_store_inv. eauto.
          subst. reflexivity.
        - inversion H1; inversion H2; subst.
          assert (σ'1 = σ'2). eapply IHm. eauto. eauto.
          subst. eapply IHs. eauto. eauto. }
      assert (∀ m σ' σ'', (σ, p) ⊢ (e, s) m ⇓∞ σ' →
                          σ' ⊢ e ⇓ₑ (VBool false) →
                          (σ, p) ⊢ (e, s) S m ⇓∞ σ'' →
                          False) as loop_false_mSm_contra.
      { intros. remember (S m) as sm. induction H3; subst.
        - omega.
        - inversion Heqsm. subst.
          assert (σ'0 = σ'1). eapply loop_deterministic. eauto. eauto. subst.
          assert (VBool false = VBool true). eapply exp_deterministic.
          eauto. eauto. inversion H6. }
      assert (∀ n m σ' σ'', (σ, p) ⊢ (e, s) n ⇓∞ σ' →
                            σ' ⊢ e ⇓ₑ (VBool false) →
                            (σ, p) ⊢ (e, s) m ⇓∞ σ'' →
                            n < m →
                            False) as loop_false_nm_contra.
      { intros. generalize dependent σ''0. induction H4; intros.
        - eapply loop_false_mSm_contra. apply H1. apply H2. apply H3.
        - assert (n < m). omega. inversion H3; subst.
          eapply IHle. apply H7. }
      inversion H; inversion H0; subst.
      bdestruct (n =? n0).
      + subst. eapply loop_deterministic. eauto. eauto.
      + bdestruct (n <? n0).
        * assert False. eapply loop_false_nm_contra. apply H5. apply H7. apply H12. apply H2. inversion H3.
        * assert (n > n0). omega.
          assert False. eapply loop_false_nm_contra. apply H12. apply H14. apply H5. apply H3. inversion H4.
    - inversion H; inversion H0; subst.
      assert (σ'0 = σ'1). eapply IHs1. eauto. eauto. subst.
      eapply IHs2. eauto. eauto.
    - assert (σ = σ'). eapply skip_store_inv. eauto.
      assert (σ = σ''). eapply skip_store_inv. eauto.
      subst. reflexivity.
    - inversion H.
Qed.
      
End IMPRel.

(* IMP Standard semantics, without context path *)

Module IMPStd.

End IMPStd.

(* IMP Monadic functional semantics *)

Module IMPEval.

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

  Reserved Notation "'〚' e '〛' ( st ) " (at level 90, left associativity).

  Fixpoint evalExp (e: exp) (σ: store) : option val :=
    match e with
    (* | EId x  => o ← (σ (LId x)) IN o 0 *)
    | ENum n => Some (VNum n)
    | EBool b => Some (VBool b)
    | ELoc x => Some (VLoc (LId x))
    | EPlus x y =>
      a ←〚x〛(σ) >>= toNat IN
      b ←〚y〛(σ) >>= toNat IN
      Some (VNum (a + b))
    | EMinus x y =>
      a ←〚x〛(σ) >>= toNat IN
      b ←〚y〛(σ) >>= toNat IN
      Some (VNum (a - b))
    | EMult x y =>
      a ←〚x〛(σ) >>= toNat IN
      b ←〚y〛(σ) >>= toNat IN
      Some (VNum (a * b))
    | ELt x y =>
      a ←〚x〛(σ) >>= toNat IN
      b ←〚y〛(σ) >>= toNat IN
      Some (VBool (a <? b))
    | EEq x y =>
      a ←〚x〛(σ) >>= toNat IN
      b ←〚y〛(σ) >>= toNat IN
      Some (VBool (a =? b))
    | EAnd x y =>
      a ←〚x〛(σ) >>= toBool IN
      b ←〚y〛(σ) >>= toBool IN
      Some (VBool (andb a b))
    | ENeg x =>
      a ←〚x〛(σ) >>= toBool IN
      Some (VBool (negb a))
    | EFieldRead e1 e2 =>
      l ←〚e1〛(σ) >>= toLoc IN
      n ←〚e2〛(σ) >>= toNat IN
      o ← σ l IN
      o n
    end
  where "'〚' e '〛' ( st ) " := (evalExp e st) : type_scope.

  Definition toSomeBool (oob : option (option bool)) :=
    match oob with
    | Some (Some b) => Some b
    | Some None => Some true
    | None => None
    end.

  Fixpoint idx1 (i : nat) (m : nat) (p : nat -> option (option bool)) : option (option nat) :=
    match m with
    | O => None (* out of fuel *)
    | S m' =>
      match p i with
      | Some (Some true) => Some (Some i)
      | Some (Some false) => idx1 (i + 1) m' p
      | Some None => Some None
      | None => None
      end
      (*
      b ← p i IN
      if b then Some i else idx1 (i + 1) m' p
      *)
    end.
    
  Fixpoint idx2 (ub : nat) (m : nat) (p : nat → option (option bool)) : option (option nat) :=
    match m with
    | O => None
    | S m' =>
      match p (ub - m) with
      | Some (Some true) => Some (Some (ub - m))
      | Some (Some false) => idx2 ub m' p
      | Some None => Some None
      | None => None
      end
    end.

  Lemma idx1_eq_idx2 : ∀ m p, idx1 0 m p = idx2 m m p.
  Proof.
Admitted.

  (* idx finds the least index *)
  Definition idx (m : nat) (p : nat -> option (option bool)) : option (option nat) := idx1 0 m p.

  Fixpoint evalLoop (cnd : exp) (s : stmt) (σ : store) (c : path) (n : nat)
           (evstmt : store → path → option (option store)) : option (option store) :=
    match n with
    | O => Some (Some σ)
    | S n' =>
      σ' ↩ evalLoop cnd s σ c n' evstmt IN
      bv ↩ Some (〚cnd〛(σ') >>= toBool) IN
      if bv
      then evstmt σ' (PWhile c n') (* continue evaluation *)
      else Some None (* error, this case should not happen if idx has guessed a correct n ??? *)
    end.

  (*
  Fixpoint evalLoop (s : stmt) (σ : store) (p : path) (n : nat)
           (evstmt : store → path → option (option store)) : option (option store) :=
    match n with
    | O => Some (Some σ)
    | S n' =>
      σ' ↩ evalLoop s σ p n' evstmt IN
      evstmt σ' (PWhile p n')
    end.
   *)

  Reserved Notation "'〚' s '〛' ( st , c ) ( m )" (at level 90, left associativity).

  Fixpoint evalStmt (s: stmt) (σ: store) (c: path) (m: nat) : option (option store) :=
    match s with
    | x ::= ALLOC =>
      Some (Some (LNew c st↦ mt_obj ;
            LId x st↦ (0 obj↦ (VLoc (LNew c))) ;
            σ))
    | e1[[e2]] ::= e3 =>
      l ↩ Some (〚e1〛(σ) >>= toLoc) IN
      n ↩ Some (〚e2〛(σ) >>= toNat) IN
      v ↩ Some (〚e3〛(σ)) IN
      o ← σ l IN
      Some (Some (l st↦ (n obj↦ v ; o) ; σ))
    | IF b THEN s1 ELSE s2 FI =>
      b ↩ Some (〚b〛(σ) >>= toBool) IN
      if b
      then 〚s1〛(σ, PThen c)(m)
      else 〚s2〛(σ, PElse c)(m)
    | WHILE cnd DO s END =>
      (* TODO: cleanup slightly. inline evalLoop? *)
      (*
      let guess :=
          idx m (fun i => toSomeBool (σ' ↩ evalLoop cnd s σ c i (fun σ'' c1 => 〚s〛(σ'', c1)(m)) IN
                                      b ↩ Some (〚cnd〛(σ') >>= toBool) IN
                                  Some (Some (negb b)))) in
      n ← guess IN
      evalLoop cnd s σ c n (fun σ' c1 => 〚s〛(σ', c1)(m))
       *)
      let guess :=
          idx m (fun i => σ' ↩ evalLoop cnd s σ c i (fun σ'' c1 => 〚s〛(σ'', c1)(m)) IN
                          b ↩ Some (〚cnd〛(σ') >>= toBool) IN
                          Some (Some (negb b))) in
      n ↩ guess IN
      evalLoop cnd s σ c n (fun σ' c1 => 〚s〛(σ', c1)(m))
    | s1 ;; s2 =>
      σ' ↩ 〚s1〛(σ, PFst c)(m) IN
     〚s2〛(σ', PSnd c)(m)
    | SKIP => Some (Some σ)
    | SAbort => Some None
    end
  where "'〚' s '〛' ( st , c ) ( m )" := (evalStmt s st c m) : type_scope.

  (*
  Fixpoint idx1 (i : nat) (m : nat) (p : nat -> option (option bool)) {struct m} : option (option nat) :=
    match m with
    | O => None (* out of fuel *)
    | S m' =>
      match p i with
      | Some (Some true) => Some (Some i)
      | Some (Some false) => idx1 (i + 1) m' p
      | Some None => Some None
      | None => None
      end
    end
  with evalLoop (cnd : exp) (s : stmt) (σ : store) (c : path) (n : nat) {struct n} : option (option store) :=
    match n with
    | O => Some (Some σ)
    | S n' =>
      σ' ↩ evalLoop cnd s σ c n' IN
      bv ↩ Some (〚cnd〛(σ') >>= toBool) IN
      if bv
      then evalStmt s σ' (PWhile c n') n' (* continue evaluation *)
      else Some None (* error, this case should not happen if idx has guessed a correct n ??? *)
    end
  with evalStmt (s : stmt) (σ : store) (c : path) (m : nat) {struct m} : option (option store) :=
    match m with
    | O => None
    | S m' =>
      match s with
      | x ::= ALLOC =>
        Some (Some (LNew c st↦ mt_obj ;
                    LId x st↦ (0 obj↦ (VLoc (LNew c))) ;
                    σ))
      | e1[[e2]] ::= e3 =>
        l ↩ Some (〚e1〛(σ) >>= toLoc) IN
        n ↩ Some (〚e2〛(σ) >>= toNat) IN
        v ↩ Some (〚e3〛(σ)) IN
        o ← σ l IN
        Some (Some (l st↦ (n obj↦ v ; o) ; σ))
      | IF b THEN s1 ELSE s2 FI =>
        b ↩ Some (〚b〛(σ) >>= toBool) IN
        if b
        then 〚s1〛(σ, PThen c)(m')
        else 〚s2〛(σ, PElse c)(m')
      | WHILE cnd DO s END =>
        let guess :=
          idx m (fun i => σ' ↩ evalLoop cnd s σ c i IN
                          b ↩ Some (〚cnd〛(σ') >>= toBool) IN
                          Some (Some (negb b))) in
        n ↩ guess IN
        evalLoop cnd s σ c n
      | s1 ;; s2 =>
        σ' ↩ 〚s1〛(σ, PFst c)(m') IN
       〚s2〛(σ', PSnd c)(m')
      | SKIP => Some (Some σ)
      | SAbort => Some None
      end
    end
  where "'〚' s '〛' ( st , c ) ( m )" := (evalStmt s st c m) : type_scope.
   *)

  Definition eval (s: stmt) :=〚s〛(σ0, PRoot)(500).

End IMPEval.

Module Adequacy.

  Import IMPRel.
  Import IMPEval.

  Theorem exp_adequacy : ∀ e σ v,
    σ ⊢ e ⇓ₑ v <->〚 e 〛(σ) = Some v.
  Proof.
    intros. split.
    - intros. induction H; simpl; auto; try (rewrite IHevalExp1; rewrite IHevalExp2; simpl; reflexivity).
      + rewrite IHevalExp. simpl.  reflexivity.
      + rewrite IHevalExp1. rewrite IHevalExp2. simpl. rewrite H1. auto.
    - intros. generalize dependent v.
      induction e; intros; inversion H; inversion H; clear H2.
      + eapply RNum.
      + eapply RBool.
      + eapply RLoc.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply RPlus. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply RMinus. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply RMult. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply RLt. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply REq. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          eapply RAnd. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
        * destruct v0; simpl in H1; inversion H1.
      + destruct (〚e〛(σ)); inversion H1.
        * destruct v0; simpl in H1; inversion H1.
          eapply RNeg. eapply IHe. reflexivity.
      + destruct (〚e1〛(σ)); destruct (〚e2〛(σ)); inversion H1.
        * destruct v0; destruct v1; simpl in H1; inversion H1.
          simpl in H2. case_eq (σ l); intros; rewrite H0 in H1.
          eapply RFieldRead. eapply IHe1. reflexivity. eapply IHe2. reflexivity.
          eapply H0. eapply H1.
          inversion H1.
        * destruct v0; simpl in H1; inversion H1.
Qed.

  Lemma idx1_more_val_inv : ∀ m n p i x,
      m >= n →
      idx1 x n p = Some (Some i) →
      idx1 x m p = Some (Some i).
  Proof.
    intro m. induction m; intros.
    - inversion H. subst. simpl in H0. inversion H0.
    - simpl. destruct n.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (p x) eqn:Hpx.
        destruct o eqn:Ho. destruct b eqn:Hb.
        apply H0. assert (m >= n). omega. eapply IHm. apply H1.
        apply H0. inversion H0. inversion H0.
Qed.

  Lemma idx_more_val_inv : ∀ m n p i,
      m >= n →
      idx n p = Some (Some i) →
      idx m p = Some (Some i).
  Proof.
    intros.
    replace (idx n p) with (idx1 0 n p) in H0.
    replace (idx m p) with (idx1 0 m p).
    eapply idx1_more_val_inv. apply H. apply H0.
    auto. auto.
Qed.

  (*
  Lemma idx_more_val_inv : ∀ m n f g i x,
      m >= n →
      idx1 x n f = Some (Some i) →
      idx1 x m g = Some (Some i).
   *)

  Lemma idx1_more_err_inv : ∀ m n p x, m >= n → idx1 x n p = Some None → idx1 x m p = Some None.
  Proof.
    intro m. induction m; intros.
    - inversion H. subst. simpl in H0. inversion H0.
    - simpl. destruct n.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (p x) eqn:Hpx.
        destruct o eqn:Ho. destruct b eqn:Hb.
        apply H0. assert (m >= n). omega. eapply IHm. apply H1.
        apply H0. reflexivity. inversion H0.
Qed.

  Lemma idx_more_inv : ∀ m n p x v,
      m >= n →
      idx1 x n p = Some v →
      idx1 x m p = Some v.
  Proof.
    intros. destruct v.
    eapply idx1_more_val_inv. apply H. apply H0.
    eapply idx1_more_err_inv. apply H. apply H0.
  Qed.

  Lemma idx_not_zero {A : Type} : ∀ n p e (v : A),
      n0 ↩ idx n p IN e = Some (Some v) -> n > 0.
  Proof.
    intros.
    induction n.
    - simpl in H. inversion H.
    - omega.
Qed.

  Lemma loop_more_val_none : ∀ i e s σ σ' p f,
      evalLoop e s σ p i f = Some (Some σ') →
      〚e〛(σ') = Some (VBool false) →
      evalLoop e s σ p (S i) f = Some None.
  Proof.
    intro i. induction i; intros.
    - simpl. simpl in H. inversion H. subst.
      rewrite H0. simpl. reflexivity.
    - simpl. simpl in H. rewrite H. rewrite H0. simpl.
      reflexivity.
Qed.

  Lemma loop_more_val_true : ∀ i e s σ σ' p f,
      evalLoop e s σ p i f = Some (Some σ') →
      〚e〛(σ') = Some (VBool true) →
      evalLoop e s σ p (S i) f = f σ' (PWhile p i).
  Proof.
    intro i. induction i; intros.
    - simpl. simpl in H. inversion H. rewrite H0. simpl. reflexivity.
    - simpl. simpl in H. rewrite H. rewrite H0. simpl. reflexivity.
Qed.

  Lemma loop_more_some_none: ∀ i e s σ p f,
      evalLoop e s σ p i f = Some None →
      evalLoop e s σ p (S i) f = Some None.
  Proof.
    intro i. induction i; intros.
    - simpl in H. inversion H.
    - simpl in H. simpl. rewrite H. reflexivity.
Qed.

  Lemma loop_eval_more_val_Sn : ∀ n e s σ c i v,
      evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n)) = Some (Some v) →
      evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n)) = Some (Some v).
  Proof.
Admitted.

  Lemma idx_range : ∀ m f i x, x < m → idx1 x m f = Some (Some i) -> x <= i ∧ i < m.
  Proof.
    (*
    generalize dependent x. generalize dependent i.
    induction m; intros.
    - simpl in H0. inversion H0.
    - simpl in H0. destruct (f x); inversion H0.
      destruct o; inversion H2.
      destruct b; inversion H3. subst. split. auto. auto.*)
      Admitted.

  Definition eq_under (m : nat) (p q : nat → option (option bool)) :=
    forall i, 0 <= i /\ i <= m -> p i = q i.
  Lemma idx_eq : forall m p q x, eq_under m p q → x <= m → idx1 x m p = idx1 x m q.
  Proof.
  Admitted.
  (*
    intros. cbv delta in H. simpl in H.
    generalize dependent p. generalize dependent q.  generalize dependent x.
    induction m; intros.
    - cbv. reflexivity.
    - cbv. subst. assert (p 0 = q 0). eapply H. omega.
      assert (p x = q x).
      { eapply H. omega. }
      rewrite H2. destruct (q x) eqn:Eqqx.
      + destruct o eqn:Eqo.
        * destruct b eqn:Eqb. reflexivity.
          rewrite plus_comm.
    *)  

(*
  Lemma stmt_eval_more_val_Sn : ∀ s n σ c v,
      evalStmt s σ c n = Some v →
      evalStmt s σ c (S n) = Some v.
  Proof.
    intro s. induction s; intros.
    - simpl in H; simpl; auto.
    - simpl in H; simpl; auto.
    - simpl in H; simpl; auto.
      destruct (〚 e 〛 (σ) >>= toBool). destruct b.
      eapply IHs1. apply H. eapply IHs2. apply H. apply H.
    - simpl in H. simpl. unfold idx.
      assert (∀ i n σ v c ,
                 evalLoop e s σ c i (fun σ' c1 => 〚s〛(σ', c1)(n)) = Some v →
                 evalLoop e s σ c i (fun σ' c1 => 〚s〛(σ', c1)(S n)) = Some v)
             as evalLoopMoreStep.
      { intro i. induction i; intros.
        - simpl. simpl in H0. apply H0.
        - simpl. simpl in H0.
          remember (evalLoop e s σ1 c0 i (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(n0))) as loopn.
          remember (evalLoop e s σ1 c0 i (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(S n0))) as loopsn.
          destruct loopn.
          + symmetry in Heqloopn. eapply IHi in Heqloopn.
            rewrite Heqloopn in Heqloopsn. rewrite Heqloopsn.
            destruct o.
            * destruct (〚 e 〛 (s0) >>= toBool).
              ** destruct b. eapply IHs. apply H0. apply H0.
              ** apply H0.
            * apply H0.
          + inversion H0.
      }
      assert (∀ x a n m,
          idx1 a x
          (λ i : nat,
             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
             IN match 〚 e 〛 (σ') >>= toBool with
                | Some b => Some (Some (negb b))
                | None => Some None
                end) = Some m →
          idx1 a (S x)
          (λ i : nat,
             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
             IN match 〚 e 〛 (σ') >>= toBool with
                | Some b => Some (Some (negb b))
                | None => Some None
                end) = Some m) as idxMoreStep.
      { unfold idx. intros x.
        induction x; intros.
        - simpl in H0. inversion H0.
        - simpl in H0. remember (S x) as sx. simpl.
          remember (evalLoop e s σ c a (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n0))) as loopn.
          remember (evalLoop e s σ c a (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n0))) as loopsn.
          destruct loopn.
          + symmetry in Heqloopn. eapply evalLoopMoreStep in Heqloopn.
            rewrite Heqloopn in Heqloopsn. rewrite Heqloopsn.
            destruct o.
            * destruct (〚 e 〛 (s0) >>= toBool).
              ** destruct b.
                ++ simpl. simpl in H0. eapply IHx. apply H0.
                ++ simpl in H0. simpl. apply H0.
              ** apply H0.
            * apply H0.
          + inversion H0.
      }
      unfold idx in *. remember (idx1 0 n
          (λ i : nat,
             σ'
             ↩ evalLoop e s σ c i
                 (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
             IN match 〚 e 〛 (σ') >>= toBool with
                | Some b => Some (Some (negb b))
                | None => Some None
                end)) as ix0.
      remember (idx1 0 (S n) (λ i : nat,
                            σ' ↩ evalLoop e s σ c i
                              (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
                              IN match 〚 e 〛 (σ') >>= toBool with
                                 | Some b => Some (Some (negb b))
                                 | None => Some None
                                 end)) as ix1.
      destruct ix0. 2: inversion H.
      symmetry in Heqix0.
      eapply idxMoreStep in Heqix0. rewrite Heqix0 in Heqix1. subst.
      destruct o. eapply evalLoopMoreStep. apply H.
      apply H.
    - simpl in H. simpl.
      destruct (〚 s1 〛 (σ, PFst c)(n)) eqn:Eqs1.
      eapply IHs1 in Eqs1.
      + destruct o.
        * eapply IHs2 in H. rewrite Eqs1. apply H.
        * rewrite Eqs1. apply H.
      + inversion H.
    - simpl in H. simpl. apply H.
    - simpl in H. simpl. apply H.
  Qed.
      
  (* Lemma stmt_eval_more_val_Sn : ∀ n m s σ c v, *)
  Lemma stmt_eval_more_val_nm : ∀ s n m σ c v,
      n <= m →
      evalStmt s σ c n = Some v →
      evalStmt s σ c m = Some v.
  Proof.
    intro s.
    induction s; intros.
    - simpl in H0. simpl. auto.
    - simpl in H0. simpl. auto.
    - simpl in H0. simpl.
      destruct (〚 e 〛 (σ) >>= toBool).
      destruct b. eapply IHs1. apply H. apply H0.
      eapply IHs2. apply H. apply H0. apply H0.
    - induction m.
      + inversion H. subst. apply H0.
      + bdestruct (n =? S m).
        * subst. apply H0.
        * assert (n <= m). omega.
          eapply stmt_eval_more_val_Sn. apply IHm. apply H2.
    - simpl in H0. simpl.
      destruct (〚 s1 〛 (σ, PFst c)(n)) eqn:Eqs1n.
      + eapply (@IHs1 _ _ _ _ _ H) in Eqs1n. rewrite Eqs1n.
        destruct o. eapply IHs2. apply H. apply H0. apply H0.
      + inversion H0.
    - simpl in H0. simpl. apply H0.
    - simpl in H0. simpl. apply H0.
  Qed.
  
  (*

  Lemma idx_start_Sn_val_inv : ∀ n i j p,
      bool_monotonic p →
      idx1 i n p = Some (Some j) →
      idx1 (S i) n p = Some (Some j).
  Proof.
    intro n. induction n; intros i j p Mp H.
    - simpl in H. inversion H.
    - simpl in H. simpl. unfold bool_monotonic in Mp.
      destruct (p i) eqn:Eqpi.
      + destruct o.
        * destruct b. inversion H. rewrite <- H1. rewrite Mp.
          ++ 
  
  Lemma stmt_eval_more_val_Sn : ∀ s n σ c v,
      evalStmt s σ c n = Some (Some v) →
      evalStmt s σ c (S n) = Some (Some v).
  Proof.
    intro s. induction s; intros.
    - simpl in H; auto.
    - simpl in H; auto.
    - simpl in H. simpl. destruct (〚e〛(σ) >>= toBool). destruct b.
      eapply IHs1. auto. eapply IHs2. auto. inversion H.
    - simpl. simpl in H. 
      simpl. destruct (〚e〛(σ) >>= toBool).
      + destruct b.
        * simpl. simpl in H.
          
      induction n.
      + simpl in H. inversion H.
      + simpl in H. simpl.
        destruct (〚e〛(σ) >>= toBool). destruct b. simpl. simpl in H.
   *)

  Theorem stmt_adequacy_1 : ∀ s σ σ' p,
      (σ, p) ⊢ s ⇓ σ' -> ∃ m,〚s〛(σ, p)(m) = Some (Some σ').
  Proof.
    intros. generalize dependent p. generalize dependent σ. generalize dependent σ'.
    induction s; intros; inversion H; subst.
    - simpl. exists 1. reflexivity.
    - simpl. exists 1. simpl. eapply exp_adequacy in H3. eapply exp_adequacy in H6.
      eapply exp_adequacy in H8. rewrite H3. rewrite H6. rewrite H8.
      simpl. rewrite H9. reflexivity.
    - simpl. eapply exp_adequacy in H6. rewrite H6. simpl.
      eapply IHs1. apply H7.
    - simpl. eapply exp_adequacy in H6. rewrite H6. simpl.
      eapply IHs2. apply H7.
    - (*
      assert (∀ σ n σ',
                 (σ, p)⊢ (e, s) n ⇓∞ σ' →
                 σ' ⊢ e ⇓ₑ VBool false →
                 ∃ (m : nat), idx m (λ i : nat,
                    σ'0 ↩ evalLoop e s σ p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(m))
                    IN match 〚 e 〛 (σ'0) >>= toBool with
                        | Some b => Some (Some (negb b))
                        | None => Some None
                       end) = Some (Some n)).
      { intros.
        induction n0.
        - exists 1. inversion H0. subst. eapply exp_adequacy in H1. unfold idx. simpl. rewrite H1. simpl.
          reflexivity.
        - 
          

      + inversion H4; subst.
        simpl. reflexivity.
      + assert (σ ⊢ e ⇓ₑ (VBool true)). eapply loop_Sn_cond_true. eapply H4.
        inversion H4; subst. 
        *)
      
  Admitted.
  (*
      simpl. induction n.
      * simpl. inversion H4. subst. eapply exp_adequacy in H6. rewrite H6.
        simpl. reflexivity.
      * assert (σ ⊢ e ⇓ₑ (VBool true)). eapply loop_Sn_cond_true. eapply H4.
        eapply exp_adequacy in H0. rewrite H0. simpl. rewrite H0. simpl.
        rewrite H0 in IHn. simpl in IHn.
    *)    
    
  Theorem stmt_adequacy_2 : ∀ s σ σ' p,
      ex (fun m =>〚s〛(σ, p)(m) = Some (Some σ')) -> (σ, p) ⊢ s ⇓ σ'.
  Proof.
    intros s σ σ' p H. inversion H.
    generalize dependent σ. generalize dependent σ'. generalize dependent p.
    induction s; intros.
    - simpl in H0. inversion H0. eapply RAlloc.
    - simpl in H0. 
      destruct (〚e〛(σ)) eqn:EqE; destruct (〚e0〛(σ)) eqn:EqE0; destruct (〚e1〛(σ)) eqn:EqE1;
        try (destruct v; simpl in H0; inversion H0).
      * eapply exp_adequacy in EqE. eapply exp_adequacy in EqE0. eapply exp_adequacy in EqE1.
        destruct v0; simpl in H2; inversion H2. destruct (σ l) eqn:SomeO; inversion H2.
        eapply RAssign. eauto. eauto. eauto. eauto.
      * destruct (toNat v0); inversion H0.
      * inversion H0.
    - simpl in H0.
      destruct (〚e〛(σ)) eqn:EqE; inversion H. destruct v; simpl in H0; inversion H0.
      destruct b; eapply exp_adequacy in EqE.
      eapply RIfTrue. eauto. eauto.
      eapply RIfFalse. eauto. eauto. inversion H0.
    - simpl in H0.
      remember (idx x
           (λ i : nat,
              σ' ↩ evalLoop e s σ p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(x))
              IN match 〚 e 〛 (σ') >>= toBool with
                 | Some b => Some (Some (negb b))
                 | None => Some None
                 end) ) as idxx.
      destruct idxx; inversion H0. destruct o; inversion H0.
      assert (〚e〛(σ') = Some (VBool false)). admit.
      eapply exp_adequacy in H1.
      eapply RWhile with (n := n). 2: apply H1.
      clear H2. clear H3.
      assert (∀ n σ p x σ',
                 evalLoop e s σ p n (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(x)) = Some (Some σ') →
                 σ' ⊢ e ⇓ₑ VBool false →
                 (σ, p)⊢ (e, s) n ⇓∞ σ').
      { intro n0. induction n0; intros.
        - admit.
        - eapply RWhileMore. eapply IHn0.

      

      generalize dependent σ.
      generalize dependent σ'.
      generalize dependent p.
      induction n; intros.
      + simpl in H0. inversion H0. eapply RWhileZero.
      + 
        eapply RWhileMore. eapply IHn. apply H. eapply H0.



      simpl in H0.
      eapply RWhile.
      destruct x eqn:IHx.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (〚 e 〛 (σ) >>= toBool).
        * subst. admit.
        * simpl in H0.
          destruct (〚 e 〛 (σ) >>= toBool).
          inversion IHx.
          inversion IHx.
        * inversion IHx. subst. 
    - simpl in H0. destruct (〚s1〛(σ, PFst p)(x)) eqn:EqS1; destruct (〚s2〛(σ, PSnd p)(x)) eqn:EqS2.
      * destruct o; inversion H0. destruct o1; eapply RSeq; eauto; eauto.
      * destruct o; inversion H0. eapply RSeq. eauto. eauto.
      * inversion H0.
      * inversion H0.
    - inversion H0. eapply RSkip.
    - inversion H0.
  Qed.


  Theorem stmt_adequacy : ∀ s σ σ' p,
      (σ, p) ⊢ s ⇓ σ' <-> ∃ m,〚s〛(σ, p)(m) = Some (Some σ').
  Proof.
    Admitted.
*)
End Adequacy.

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
  | GAnd : gxp -> gxp -> gxp

  | GIf : gxp -> gxp -> gxp -> gxp.


Definition fvalid : gxp := GLoc (LId (Id 0)). (* "$valid" *)
Definition fdata :  gxp := GLoc (LId (Id 1)). (* "$data"  *)
Definition ftpe :   gxp := GNum 0. (* "$tpe"   *)
Definition fval :   gxp := GNum 1. (* "$val"   *)

Definition tnat :   gxp := GNum 0.
Definition tbool :  gxp := GNum 1.
Definition tloc :   gxp := GNum 2.

Definition GEmpty : gxp := GMap (fun k =>
                           match k with
                           | LId x => Some (GObj (t_empty None))
                           | LNew p => None
                           end).

Definition OEmpty : gxp := GObj(t_empty None).

Definition GNone :  gxp := GPut GEmpty fvalid (GBool false).
Definition GSome a : gxp := GPut (GPut GEmpty fvalid (GBool true)) fdata a.

Definition GMatch (scrutinee: gxp) (none: gxp) (some: gxp -> gxp): gxp :=
  GIf (GGet scrutinee fvalid) (some (GGet scrutinee fdata)) none.

Definition GVSelect (addr: gxp) (field: gxp): gxp :=
  GIf (GHasField addr field) (GSome (GGet addr field)) GNone.

Definition GVNum (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tnat) fval a.

Definition GVBool (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tbool) fval a.

Definition GVLoc (a: gxp): gxp :=
  GPut (GPut OEmpty ftpe tloc) fval a.

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
  | EBool b =>      GSome (GVBool (GBool b))
  | EEq a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GEq a b))
  | ELt a b =>    LETG a <-- trans_exp a sto >>g= toNatG IN
                  LETG b <-- trans_exp b sto >>g= toNatG IN
                  GSome (GVBool (GLt a b))
  | EAnd a b =>   LETG a <-- trans_exp a sto >>g= toBoolG IN
                  LETG b <-- trans_exp b sto >>g= toBoolG IN
                  GSome (GVBool (GAnd a b))
  | ENeg a =>     LETG a <-- trans_exp a sto >>g= toBoolG IN
                  GSome (GVBool (GNot a))
  | EFieldRead s n =>
                  LETG s' <-- trans_exp s sto >>g= toLocG IN
                  LETG n' <-- trans_exp n sto >>g= toNatG IN
                  LETG o <-- GVSelect sto s' IN
                  GVSelect o n'
  end.


Fixpoint trans_loop (e: exp) (s: stmt) (sto: gxp) (c: path) (n: nat) (* How to use GFixIndex? *)
    (evstmt : gxp → path → gxp) : gxp:=
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


(* simplification / normalization *)

Definition hasField {X Y : Type} (m: total_map X (option Y)) (x : X): gxp := match m x with
    | Some _ => GBool true
    | None => GBool false
end.

(* Fixpoint simpl_map (e: gxp): gxp := match e with
  | GGet (GPut m x v1) y => if beq_loc x y
                            then v1
                            else *)

(* | GPut m y v => match sms_eval_exp x with
          | GLoc x' => match sms_eval_exp y with
                       | GLoc y' => if beq_loc x' y'
                                      then GBool true
                                       else GBool false
                       | y' => GHasField (GPut m y' v) (GLoc x') end
          | x' => GHasField (GPut m y v) x' end *)

(* Fixpoint beq_gxp (l : gxp) (r : gxp): bool := match l, r with
  | GNum n, GNum m => beq_nat n m
  | GBool n, GBool m => eqb n m
  | GLoc n, GLoc m => beq_nat n m
  | GMap m =>
  | GObj n => e
  | GHasField a x => 
  | GGet a x => 
  | GPut a x b => 
  | GPlus a b =>
  | GMinus a b => 
  | GMult a b => 
  | GEq a b => 
  | GIf c a b => 
  | GLt a b => 
  | GAnd a b => 
  | GNot a => *)

Fixpoint sms_eval_exp (e: gxp): gxp :=
  match e with
  | GNum n => e
  | GBool n => e
  | GLoc n => e
  | GMap m => e (* simpl in Map? *)
  | GObj n => e
  | GHasField a x => match sms_eval_exp a, sms_eval_exp x with
                     | GMap m, GLoc x => hasField m x
                     | GObj m, GNum x => hasField m x
(*                      | GPut m y v, x' => GIf (GEq x' y) (GBool true) (GHasField m x') *)
                     | a', x' => GHasField a' x'
                     end
  | GGet a x => match sms_eval_exp a, sms_eval_exp x with
                | GMap m, GLoc x => match m x with Some y => y | None => GNone end
(*                 | GPut m y v, x' => GIf (GEq x' y) v (GGet m x') *)
                | GObj m, GNum x => match m x with Some y => y | None => GNone end
                | a', x' => GGet a' x'
                end
  | GPut a x b => match sms_eval_exp a, sms_eval_exp x, sms_eval_exp b with
                  | GMap m, GLoc x', b' => GMap (t_update beq_loc m x' (Some b'))
                  | GObj m, GNum x', b' => GObj (t_update beq_nat m x' (Some b'))
                  | a', x', b' => GPut a' x' b'
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
                 | GNum a', GNum b' => GBool (Nat.eqb a' b')
                 | GLoc a', GLoc b' => GBool (beq_loc a' b')
                 | a', b' => GEq a' b'
                 end
  | GIf c a b => match sms_eval_exp c with
                 | GBool c' => if c' then sms_eval_exp a else sms_eval_exp b
                 | c' => GIf c' (sms_eval_exp a) (sms_eval_exp b)
                 end
  | GLt a b => match sms_eval_exp a, sms_eval_exp b with
                 | GNum a', GNum b' => GBool (Nat.ltb a' b')
                 | a', b' => GLt a' b'
                 end
  | GAnd a b => match sms_eval_exp a, sms_eval_exp b with
                 | GBool a', GBool b' => GBool (andb a' b')
                 | a', b' => GAnd a' b'
                 end
  | GNot a => match sms_eval_exp a with
                 | GBool a' => GBool (negb a')
                 | a' => GNot a'
                 end
  end.

(* examples, sanity checks *)

Definition testprog := (trans_exp (EPlus (ENum 2) (ENum 3)) (GMap (t_empty None))).

Definition testprog2 := fun e1 e2 => (trans_exp (EPlus e1 e2) (GMap (t_empty None))).

Definition testprog1 := (trans_exp (ENum 2)) (GMap (t_empty None)).

(* WARNING: computing of GMao unfolds string comparison (<-- huge term!!!) *)
Compute testprog.
Compute testprog1.
Compute testprog2.

Compute (sms_eval_exp (GPut GEmpty fvalid (GBool true))).

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

Lemma GEQ_GetC: forall a1 a2 x1 x2,
    geq a1 a2 -> geq x1 x2 -> geq (GGet a1 x1) (GGet a2 x2).
Proof. intros. unfold geq in *. simpl. rewrite H. rewrite H0. reflexivity.  Qed.

Lemma GEQ_PlusC: forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GPlus a1 b1) (GPlus a2 b2).
Proof. intros. unfold geq in *. simpl. rewrite H. rewrite H0. simpl. auto. Qed.

Lemma GEQ_MinusC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GMinus a1 b1) (GMinus a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. auto.
Qed.

Lemma GEQ_MultC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GMult a1 b1) (GMult a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. auto.
Qed.

Lemma GEQ_LtC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GLt a1 b1) (GLt a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. auto.
Qed.

Lemma GEQ_EqC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GEq a1 b1) (GEq a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. auto.
Qed.

Lemma GEQ_AndC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GAnd a1 b1) (GAnd a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. auto.
Qed.

Lemma GEQ_NotC : forall a1 a2,
    geq a1 a2 -> geq (GNot a1) (GNot a2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. auto.
Qed.

Lemma GEQ_HasFieldC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GHasField a1 b1) (GHasField a2 b2).
Proof.
  intros. unfold geq in *. simpl. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma GEQ_SomeC: forall a b, geq a b -> geq (GSome a) (GSome b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_VNumC: forall a b, geq a b -> geq (GVNum a) (GVNum b).
Proof.  intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_VBoolC: forall a b, geq a b -> geq (GVBool a) (GVBool b).
Proof.  intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_toNatC: forall a b, geq a b -> geq (toNatG a) (toNatG b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_toBoolC: forall a b, geq a b -> geq (toBoolG a) (toBoolG b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_toLocC: forall a b, geq a b -> geq (toLocG a) (toLocG b).
Proof. intros. unfold geq in *. simpl. rewrite H. simpl. auto. Qed.

Lemma GEQ_BindC: forall a1 a2 f1 f2,
    geq a1 a2 -> fgeq f1 f2 ->
    geq (a1 >>g= f1) (a2 >>g= f2).
Proof.
  intros.
  unfold GMatch. eapply GEQ_IfC. eapply GEQ_GetC. eauto. reflexivity. eapply H0. eapply GEQ_GetC. eauto. reflexivity. reflexivity.
Qed.

Lemma GEQ_GVSelectC : forall a1 a2 b1 b2,
    geq a1 a2 -> geq b1 b2 -> geq (GVSelect a1 b1) (GVSelect a2 b2).
Proof.
  intros. unfold GVSelect. eapply GEQ_IfC; eauto; try reflexivity. apply GEQ_HasFieldC; auto.
  apply GEQ_SomeC. apply GEQ_GetC; eauto; try reflexivity.
Qed.

(* ----- and reduction rules ----- *)


Lemma GEQ_PlusR: forall a1 a2 n1 n2,
    geq a1 (GNum n1) ->
    geq a2 (GNum n2) ->
    geq (GPlus a1 a2) (GNum (n1 + n2)).
Proof.
  intros. eapply GEQ_trans. eapply GEQ_PlusC; eauto.  unfold geq in *. simpl. reflexivity.
Qed.

Lemma GEQ_MinusR : forall a1 a2 n1 n2,
    geq a1 (GNum n1) ->
    geq a2 (GNum n2) ->
    geq (GMinus a1 a2) (GNum (n1 - n2)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_MinusC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.


Lemma GEQ_MultR : forall a1 a2 n1 n2,
    geq a1 (GNum n1) ->
    geq a2 (GNum n2) ->
    geq (GMult a1 a2) (GNum (n1 * n2)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_MultC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.

Lemma GEQ_LtR : forall a1 a2 n1 n2,
    geq a1 (GNum n1) ->
    geq a2 (GNum n2) ->
    geq (GLt a1 a2) (GBool (n1 <? n2)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_LtC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.

Lemma GEQ_EqR : forall a1 a2 n1 n2,
    geq a1 (GNum n1) ->
    geq a2 (GNum n2) ->
    geq (GEq a1 a2) (GBool (n1 =? n2)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_EqC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.

Lemma GEQ_AndR : forall a1 a2 n1 n2,
    geq a1 (GBool n1) ->
    geq a2 (GBool n2) ->
    geq (GAnd a1 a2) (GBool (andb n1 n2)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_AndC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.

Lemma GEQ_NotR : forall a1 n1,
    geq a1 (GBool n1) ->
    geq (GNot a1) (GBool (negb n1)).
Proof.
  intros. eapply GEQ_trans.
  - eapply GEQ_NotC; eauto.
  - unfold geq in *. simpl. reflexivity.
Qed.

(* Lemma GEQ_GetSomeR: forall s1 l1 m v x,
   geq s1 (GMap m) ->
   geq l1 (GLoc v) ->
   m v = Some x -> 
   geq (GGet s1 l1) x.
Proof.
  Admitted. *)
  (* intros. unfold geq. simpl. rewrite H. simpl. rewrite H0. simpl. rewrite H1.
  destruct x. *)


Lemma GEQ_PutObjR: forall s1 l1 m n x y,
   geq s1 (GObj m) ->
   geq l1 (GNum n) ->
   y = sms_eval_exp x ->
   geq (GPut s1 l1 x) (GObj (t_update beq_nat m n (Some y))).
Proof.
 intros.
 unfold geq. simpl. rewrite H. rewrite H0. simpl. subst. reflexivity.
Qed.

(* Lemma GEQ_GetNoneR: forall s1 l1 m v,
   geq s1 (GMap m) ->
   geq l1 (GLoc v) ->
   m v = None -> 
   geq (GGet s1 l1) GNone.
Proof.
intros. unfold geq. simpl. rewrite H. simpl. rewrite H0. simpl. rewrite H1.
unfold GNone.  reflexivity.
Qed. *)

(* Lemma GEQ_GetSomeObjR: forall s1 l1 m n x,
   geq s1 (GObj m) ->
   geq l1 (GNum n) ->
   m n = Some x -> 
   geq (GGet s1 l1) x.
Proof.
  Admitted. *)


Lemma GEQ_SomeR: forall a b,
    geq a (GSome b) -> geq (GGet a fdata) b.
Proof.
  intros. eapply GEQ_trans. eapply GEQ_GetC; eauto. reflexivity. unfold GSome.
  unfold geq in *. simpl. reflexivity.
Qed. 

Lemma GEQ_BindSomeR: forall a b c f,
    geq a (GSome b) ->
    geq (f b) c ->
    fgeq f f ->
    geq (a >>g= f) c.
Proof. intros. eapply GEQ_trans. eapply GEQ_BindC; eauto.
       unfold GMatch. unfold fgeq in *. unfold geq in *. simpl. rewrite <-H0. 
       eapply H1. eapply GEQ_SomeR. reflexivity. Qed.

Lemma GEQ_BindNoneR: forall a f,
    geq a GNone -> geq (a >>g= f) GNone.
Proof.
  intros. unfold GMatch. unfold geq in *. simpl. rewrite H. simpl. reflexivity. 
Qed.

Lemma GEQ_toNatR: forall a b,
    geq a (GVNum b) -> geq (toNatG a) (GSome b).
Proof. intros. eapply GEQ_trans. eapply GEQ_toNatC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toNatBoolR: forall a b,
    geq a (GVBool b) -> geq (toNatG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toNatC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toNatLocR: forall a b,
    geq a (GVLoc b) -> geq (toNatG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toNatC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toBoolR: forall a b,
    geq a (GVBool b) -> geq (toBoolG a) (GSome b).
Proof. intros. eapply GEQ_trans. eapply GEQ_toBoolC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toBoolNatR: forall a b,
    geq a (GVNum b) -> geq (toBoolG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toBoolC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toBoolLocR: forall a b,
    geq a (GVLoc b) -> geq (toBoolG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toBoolC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toLocR: forall a b,
    geq a (GVLoc b) -> geq (toLocG a) (GSome b).
Proof. intros. eapply GEQ_trans. eapply GEQ_toLocC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toLocNatR: forall a b,
    geq a (GVNum b) -> geq (toLocG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toLocC. eauto. unfold geq in *. simpl. reflexivity. Qed.

Lemma GEQ_toLocBoolR: forall a b,
    geq a (GVBool b) -> geq (toLocG a) GNone.
Proof. intros. eapply GEQ_trans. eapply GEQ_toLocC. eauto. unfold geq in *. simpl. reflexivity. Qed.

(* ----- equivalence between IMP and FUN ----- *)

Inductive veq : val -> gxp -> Prop :=
| VEQ_Num : forall n r,
    geq r (GVNum (GNum n)) ->
    veq (VNum n) r
| VEQ_Bool : forall n r,
    geq  r (GVBool (GBool n)) ->
    veq (VBool n) r
| VEQ_Loc : forall l r,
    geq  r (GVLoc (GLoc l)) ->
    veq (VLoc l) r.

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
Definition beq (n1: bool) (n2: gxp) := n2 = (GBool n1).
Definition leq (n1: loc) (n2: gxp) := n2 = (GLoc n1).

Inductive objeq : obj -> gxp -> Prop :=
| OBJEQ_Init : forall o1 o2,
        (forall n1 n2, neq n1 n2 -> oeq veq (o1 n1) (GVSelect o2 n2)) -> objeq o1 o2.

Inductive seq : store -> gxp -> Prop := 
  | SEQ_Init : forall s1 s2,
        (forall l1 l2, leq l1 l2 -> oeq objeq (s1 l1) (GVSelect s2 l2)) -> seq s1 s2.

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
  - eapply REQ_None. eapply GEQ_toNatLocR. eauto.
Qed.

Lemma REQ_toBoolC: forall (b0 : val) (b3 : gxp), veq b0 b3 -> oeq beq (toBool b0) (toBoolG b3).
Proof.
  intros. inversion H; subst b0 r.
  - eapply REQ_None. eapply GEQ_toBoolNatR. eauto.
  - eapply REQ_Some. reflexivity. eapply GEQ_toBoolR. eauto. 
  - eapply REQ_None. eapply GEQ_toBoolLocR. eauto.
Qed.

Lemma REQ_toLocC: forall (b0 : val) (b3 : gxp), veq b0 b3 -> oeq leq (toLoc b0) (toLocG b3).
Proof.
  intros. inversion H; subst b0 r.
  - eapply REQ_None. eapply GEQ_toLocNatR. eauto.
  - eapply REQ_None. eapply GEQ_toLocBoolR. eauto.
  - eapply REQ_Some. reflexivity. eapply GEQ_toLocR. eauto. 
Qed.

Lemma OEQ_toNatC: forall (a1 : option val) (b1: gxp),
    oeq veq a1 b1 -> oeq neq (a1 >>= toNat) (b1 >>g= toNatG).
Proof.
  intros.
  eapply REQ_BindC with (peq := veq). try assumption.
  intros.
  - eapply REQ_toNatC. assumption.
  - intros. eapply GEQ_toNatC. assumption.
Qed.

Definition test22 := sms_eval_exp (GGet (GMap (t_empty None)) fvalid >>g= (λ o : gxp, GGet o ftpe)).
Compute test22.

Definition empty_store : store :=
  t_empty None.

Theorem soundness_exp: forall e s1 s2,
    seq s1 s2 ->
    req (evalExp e s1) (trans_exp e s2).
Proof.
  intros. induction e.
  (*- (* var *) simpl. unfold req. eapply REQ_None. unfold geq.
    admit. (* fixme *) *)
  - (* num *) simpl. eapply REQ_Some. eapply VEQ_Num. reflexivity. reflexivity. 
  - (* bool *) simpl. eapply REQ_Some. eapply VEQ_Bool. reflexivity. reflexivity.
  - (* loc *) simpl. eapply REQ_Some. eapply VEQ_Loc. reflexivity. reflexivity.
  - (* plus *)
    (* eapply REQ_BindC. eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    intros. eapply REQ_BindC. eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC.
    intros. eapply REQ_Some. eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_PlusR. reflexivity. reflexivity. rewrite H. rewrite H0. reflexivity.
    intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. reflexivity. eauto.
    intros. eapply GEQ_BindC. eapply GEQ_BindC. reflexivity. intros ? ? ?. eapply GEQ_toNatC. eauto. intros ? ? ?.
    eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. eauto. eauto. 
    simpl eval_exp. simpl trans_exp. *)
    simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_PlusR. reflexivity. reflexivity.
        ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_PlusC. reflexivity. apply H3. 
    + intros. eapply GEQ_BindC.
      * reflexivity.
      * intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VNumC.
        eapply GEQ_PlusC. eauto. eauto.
  - (* minus *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_MinusR. reflexivity. reflexivity.
           ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_MinusC. reflexivity. apply H3.
    + intros. eapply GEQ_BindC.
      ** reflexivity.
      ** intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VNumC.
         eapply GEQ_MinusC. eauto. eauto.
  - (* mult *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Num. eapply GEQ_VNumC. eapply GEQ_MultR. reflexivity. reflexivity.
           ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VNumC. eapply GEQ_MultC. reflexivity. apply H3.
    + intros. eapply GEQ_BindC.
      ** reflexivity.
      ** intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VNumC.
         eapply  GEQ_MultC. eauto. eauto.
  - (* lt *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Bool. eapply GEQ_VBoolC. eapply GEQ_LtR. reflexivity. reflexivity.
           ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VBoolC. eapply GEQ_LtC. reflexivity. apply H3.
    + intros. eapply GEQ_BindC.
      ** reflexivity.
      ** intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VBoolC.
         eapply  GEQ_LtC. eauto. eauto.
  - (* eq *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq neq (a1 >>= toNat) (b1 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Bool. eapply GEQ_VBoolC. eapply GEQ_EqR. reflexivity. reflexivity.
           ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VBoolC. eapply GEQ_EqC. reflexivity. eauto.
    + intros. eapply GEQ_BindC.
      ** reflexivity.
      ** intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VBoolC.
         eapply  GEQ_EqC. eauto. eauto.
  - (* and *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq beq (a1 >>= toBool) (b1 >>g= toBoolG)).
    { eapply REQ_BindC. eauto. eapply REQ_toBoolC. eapply GEQ_toBoolC. }
    assert (oeq beq (a2 >>= toBool) (b2 >>g= toBoolG)).
    { eapply REQ_BindC. eauto. eapply REQ_toBoolC. eapply GEQ_toBoolC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_Some.
        ** eapply VEQ_Bool. eapply GEQ_VBoolC. eapply GEQ_AndR. reflexivity. reflexivity.
          ** rewrite H2. rewrite H3. reflexivity.
      * intros. eapply GEQ_SomeC. eapply GEQ_VBoolC. eapply GEQ_AndC. reflexivity. eauto.
    + intros. eapply GEQ_BindC.
      ** reflexivity.
      ** intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VBoolC.
         eapply  GEQ_AndC. eauto. eauto.
  - (* not *) simpl.
    remember (evalExp e s1) as a1.
    remember (trans_exp e s2) as b1.
    assert (oeq beq (a1 >>= toBool) (b1 >>g= toBoolG)).
    { eapply REQ_BindC. eauto. eapply REQ_toBoolC. eapply GEQ_toBoolC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_Some.
       ** eapply VEQ_Bool. eapply GEQ_VBoolC. eapply GEQ_NotR. reflexivity.
       ** eapply GEQ_SomeC. eapply GEQ_VBoolC. rewrite H1. reflexivity.
    + intros ? ? ?. eapply GEQ_SomeC. eapply GEQ_VBoolC.
         eapply  GEQ_NotC. eauto.
  - (* field read *) simpl.
    remember (evalExp e1 s1) as a1.
    remember (evalExp e2 s1) as a2.
    remember (trans_exp e1 s2) as b1.
    remember (trans_exp e2 s2) as b2.
    assert (oeq leq (a1 >>= toLoc) (b1 >>g= toLocG)).
    { eapply REQ_BindC. eauto. eapply REQ_toLocC. eapply GEQ_toLocC. }
    assert (oeq neq (a2 >>= toNat) (b2 >>g= toNatG)).
    { eapply REQ_BindC. eauto. eapply REQ_toNatC. eapply GEQ_toNatC. }
    eapply REQ_BindC.
    + eauto.
    + intros. eapply REQ_BindC.
      * eauto.
      * intros. eapply REQ_BindC.
        ++ inversion H; subst. eapply H4. assumption.
        ++ intros. inversion H4; subst. eapply H5. assumption.
        ++ intros. eapply GEQ_GVSelectC; eauto; try reflexivity.
      * intros. eapply GEQ_BindC.
        ++ eapply GEQ_GVSelectC; eauto; try reflexivity.
        ++ intros ? ? ?. eapply GEQ_GVSelectC; eauto; try reflexivity.
    + intros. eapply GEQ_BindC; eauto; try reflexivity.
      intros ? ? ?. eapply GEQ_BindC; eauto; try reflexivity.
      * eapply GEQ_GVSelectC; eauto; try reflexivity.
      * intros ? ? ?. eapply GEQ_GVSelectC; eauto; try reflexivity.
Qed.



End Translation.
