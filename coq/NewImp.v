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

  Lemma t : forall m p q,
      (forall i, 0 <= i /\ i < m -> p i = q i) ->
      idx m p = idx m q.

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
    -
      assert (∀ m σ' σ'', (σ, p)⊢ (e, s) m ⇓∞ σ' →
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

  Lemma idx_more_err_inv : ∀ m n p x, m >= n → idx1 x n p = Some None → idx1 x m p = Some None.
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

  Definition bool_monotonic (p : nat → option (option bool)) :=
    ∀ (i : nat), p i = Some (Some true) → p (S i) = Some None.

  Lemma stmt_eval_more_val_Sn : ∀ s n σ c v,
      evalStmt s σ c n = Some (Some v) →
      evalStmt s σ c (S n) = Some (Some v).
  Proof.
    intro s. induction s; intros.
    - simpl in H; simpl; auto.
    - simpl in H; simpl; auto.
    - simpl in H; simpl; auto.
      destruct (〚 e 〛 (σ) >>= toBool). destruct b.
      eapply IHs1. apply H. eapply IHs2. apply H. inversion H.
    - simpl in H. simpl.
      replace (match match 〚 e 〛 (σ) >>= toBool with
                     | Some b => Some (Some (negb b))
                     | None => Some None
                     end with
               | Some (Some true) => Some (Some 0)
               | Some (Some false) =>
                 idx1 1 n
                      (λ i : nat,
                             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
                                IN match 〚 e 〛 (σ') >>= toBool with
                                   | Some b0 => Some (Some (negb b0))
                                   | None => Some None
                                   end)
               | Some None => Some None
               | None => None
               end) with (idx (S n) 
                              (λ i : nat,
                                     σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
                                        IN match 〚 e 〛 (σ') >>= toBool with
                                           | Some b => Some (Some (negb b))
                                           | None => Some None
                                           end)).
      2: simpl; reflexivity.
      destruct (idx n
          (λ i : nat,
             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
             IN match 〚 e 〛 (σ') >>= toBool with
                | Some b => Some (Some (negb b))
                | None => Some None
                end)) eqn:Idxn.
      + destruct o.
        * assert (idx (S n)
                      (λ i : nat,
                             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
                                IN match 〚 e 〛 (σ') >>= toBool with
                                   | Some b => Some (Some (negb b))
                                   | None => Some None
                                   end) = Some (Some n0)).
          { assert (S n >= n) by omega. eapply (@idx_more_val_inv (S n) n _ _ H0 Idxn). }
          assert (idx (S n)
                      (λ i : nat,
                             σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
                                IN match 〚 e 〛 (σ') >>= toBool with
                                   | Some b => Some (Some (negb b))
                                   | None => Some None
                                   end) = Some (Some n0)).
          { rewrite <- H0. 
            { intros.

            f_equal. apply functional_extensionality.
          intro. 

          induction x.
          simpl. reflexivity.
          simpl. 

        * inversion H.
      + inversion H.

      
      simpl in H. simpl.
      
      simpl in H; simpl; auto.
      induction n.
      destruct (〚 e 〛 (σ) >>= toBool).
      + destruct b.
        * simpl. admit.
        * simpl.

      
  (* Lemma stmt_eval_more_val_Sn : ∀ n m s σ c v, *)
  Lemma stmt_eval_more_val_Sn : ∀ s n m σ c v,
      n <= m →
      evalStmt s σ c n = Some (Some v) →
      evalStmt s σ c m = Some (Some v).
  Proof.
    intro s. induction s; intros; simpl in H0; simpl; auto.
    - destruct (〚 e 〛 (σ) >>= toBool).
      destruct b. eapply IHs1. apply H. apply H0.
      eapply IHs2. apply H. apply H0. inversion H0.
    - (* assert (idx n
                  (λ i : nat,
                         σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
                            IN match 〚 e 〛 (σ') >>= toBool with
                               | Some b => Some (Some (negb b))
                               | None => Some None
                               end) <> None).
      { unfold not. intros. rewrite H1 in H0. inversion H0. }
      assert (idx n
           (λ i : nat,
              σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
              IN match 〚 e 〛 (σ') >>= toBool with
                 | Some b => Some (Some (negb b))
                 | None => Some None
                 end) <> Some None).
      { unfold not. intros. rewrite H2 in H0. inversion H0. }
      *)
      assert (∃ i, i < n ∧ idx n
           (λ i : nat,
              σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
              IN match 〚 e 〛 (σ') >>= toBool with
                 | Some b => Some (Some (negb b))
                 | None => Some None
                 end) = Some (Some i)).
      { admit. } 
      admit.
    - destruct (〚 s1 〛 (σ, PFst c)(n)) eqn:Eqs1n.
      destruct o eqn:Eqo.
      + assert (〚 s1 〛 (σ, PFst c)(m) = Some (Some s)). eapply IHs1. apply H. apply Eqs1n.
        rewrite H1. eapply IHs2. apply H. apply H0.
      + inversion H0.
      + inversion H0.
   Admitted.
      
  (*
  Theorem exp_adequacy_error : ∀ e σ,
    ¬ (exists v, σ ⊢ e ⇓ₑ v) <-> 〚 e 〛(σ) = None.
  Theorem exp_adequacy_error : ∀ e σ v,
    ¬ (σ ⊢ e ⇓ₑ v) <-> 〚 e 〛(σ) = None.
  Theorem loop_number_adequacy : ∀ n,
   *)

  Definition make_stmt_eval (s : stmt) (n : nat) := fun σ c => 〚s〛(σ, c)(n).

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
    intros. generalize dependent p. generalize dependent σ.
    generalize dependent σ'. induction s; intros; inversion H; subst; simpl; auto.
    - exists 1. reflexivity.
    - exists 1. simpl. eapply exp_adequacy in H3. eapply exp_adequacy in H6.
      eapply exp_adequacy in H8. rewrite H3. rewrite H6. rewrite H8.
      simpl. rewrite H9. reflexivity.
    - eapply exp_adequacy in H6. rewrite H6. simpl.
      eapply IHs1. apply H7.
    - eapply exp_adequacy in H6. rewrite H6. simpl.
      eapply IHs2. apply H7.
    - exists (S n).
      simpl. induction n.
      * simpl. inversion H4. subst. eapply exp_adequacy in H6. rewrite H6.
        simpl. reflexivity.
      * assert (σ ⊢ e ⇓ₑ (VBool true)). eapply loop_Sn_cond_true. eapply H4.
        eapply exp_adequacy in H0. rewrite H0. simpl. rewrite H0. simpl.
        rewrite H0 in IHn. simpl in IHn.
        
    
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
    - destruct x eqn:IHx.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (〚 e 〛 (σ) >>= toBool).
        * subst.
        
        destruct x eqn:EqX.
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
        
End Adequacy.
