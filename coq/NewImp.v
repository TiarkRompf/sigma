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

Notation "x 'obj↦' v ; m" := (obj_update m x v) (at level 60, v at next level, right associativity).
Notation "x 'obj↦' v" := (obj_update mt_obj x v) (at level 60).

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
                                (at level 60, v at next level, right associativity).
Notation "x 'st↦' v" := (store_update mt_store x v) (at level 60).

(* IMP Relational big-step semantics *)

Module IMPRel.
  (* Evaluation relation for expressions *)

  (*
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
   *)

  Reserved Notation "st '⊢' e '⇓ₑ' v" (at level 90, left associativity).

  Inductive evalExpR : store → exp → val → Prop :=
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
  where "st '⊢' e '⇓ₑ' v" := (evalExpR st e v) : type_scope.

  Reserved Notation "( st1 , c ) '⊢' ( e , s ) n '⇓∞' st2" (at level 90, left associativity).
  Reserved Notation "( st1 , c ) '⊢' s '⇓' st2" (at level 90, left associativity).

  Inductive evalLoopR : store → path → exp → stmt → nat → store → Prop :=
  | RWhileZero : ∀ σ c e s,
      (σ, c) ⊢ (e, s) 0 ⇓∞ σ
  (* 
  | RWhileFalse : ∀ σ c e s n,
      σ ⊢ e ⇓ₑ (VBool false) → (* Note: is it necessary? *)
      (σ, c) ⊢ (e, s) n ⇓∞ σ
   *)
  | RWhileFalse : ∀ σ σ' c e s n,
      (σ, c) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      (σ, c) ⊢ (e, s) 1+n ⇓∞ σ'
  | RWhileMore : ∀ (σ σ' σ'' : store) c n e s,
      (σ, c) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool true) →
      (σ', PWhile c n) ⊢ s ⇓ σ'' →
      (σ, c) ⊢ (e, s) 1+n ⇓∞ σ''
  where "( st1 , c ) ⊢ ( e , s ) n '⇓∞' st2" := (evalLoopR st1 c e s n st2) : type_scope
  with evalStmtR : store → path → stmt → store → Prop :=
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
  (* | RAbort : ∀ σ p, (σ, p) ⊢ ABORT ⇓ σ0 *)
  where "( st1 , c ) '⊢' s '⇓' st2" := (evalStmtR st1 c s st2) : type_scope.

  Lemma alter_while_false : ∀ σ c e s n,
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, c) ⊢ (e, s) n ⇓∞ σ.
  Proof.
    intros. induction n.
    - eapply RWhileZero.
    - eapply RWhileFalse. eauto. eauto.
  Qed.

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

  Lemma succ_eq : forall x y : nat, x + 1 = y + 1 <-> x = y.
  Proof.
    intros. split.
    - intros. induction x. inversion H. omega. omega.
    - intros. subst. reflexivity.
  Qed.

  

  Lemma loop0_store_inv : ∀ σ σ' p e s,
      (σ, p) ⊢ (e, s) 0 ⇓∞ σ' →
      σ = σ'.
  Proof.
    intros. inversion H. auto. auto. Qed.

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

  Lemma loop_false_store_inv2 : ∀ σ p e s n,
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ (e, s) n ⇓∞ σ.
  Proof.
    intros. induction n.
    - eapply RWhileZero.
    - eapply RWhileFalse. eauto.
  Qed.

  Lemma loop_false_inv : ∀ σ σ' p e s n v,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ ⊢ e ⇓ₑ (VBool false) →
      σ' ⊢ e ⇓ₑ (VBool v) →
      false = v.
  Proof.
    intros. induction n.
    - eapply loop0_store_inv in H. subst.
      assert (VBool false = VBool v). eapply exp_deterministic.
      eauto. eauto. inversion H. reflexivity.
    - assert (σ = σ'). eapply loop_false_store_inv.
      eauto. eauto. subst.
      assert (VBool false = VBool v). eapply exp_deterministic.
      eauto. eauto. inversion H2. reflexivity.
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

  Lemma loop_false_deterministic : ∀ σ p e s n1 n2 σ' σ'',
      σ ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ (e, s) n1 ⇓∞ σ'  →
      (σ, p) ⊢ (e, s) n2 ⇓∞ σ'' →
      σ' = σ''.
  Proof.
    intros. generalize dependent n2. induction H0.
    - intros. inversion H1; subst.
      + reflexivity.
      + reflexivity.
      + assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H4.
    - intros. inversion H1; subst.
      + reflexivity.
      + reflexivity.
      + assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H5.
    - intros. assert (false = true). eapply loop_false_inv. eauto. eauto.
      eapply IHevalLoopR in H. 2: eauto. subst. auto. inversion H4.
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

  Lemma store_dec : ∀ (σ σ' : store), σ = σ' ∨ σ <> σ'.
  Proof.
    Admitted.

  Lemma loop_sigma_exists : ∀ n σ p e s,
      ∃ σ', (σ, p) ⊢ (e, s) n ⇓∞ σ'.
  Proof.
    intros. induction n.
    - exists σ. apply RWhileZero.
    - destruct IHn. assert (σ = x ∨ σ <> x). apply store_dec.
      destruct H0.
      + induction H; subst.
        * assert (∃ v, σ ⊢ e ⇓ₑ (VBool v)). admit.
          destruct H. destruct x.
          ** assert ((σ, c) ⊢ (e, s) 0 ⇓∞ σ). eapply RWhileZero.
            assert (∃ σ'', (σ, PWhile c 0) ⊢ s ⇓ σ''). admit.
            destruct H2. exists x. eapply RWhileMore. eauto. eauto. eauto.
          ** exists σ. eapply RWhileFalse.  eauto.
        * exists σ.  eapply RWhileFalse. eauto.
        * exists σ''. eapply RWhileMore in H. 2: eauto. 2: eauto.
          assert (∃ σ''', (σ'', PWhile c (1 + n)) ⊢ s ⇓ σ'''). admit.
          destruct H0.
          Admitted.
         
  Theorem loop_false_store_inv3' : ∀ σ σ' σ'' σ''' p e s n,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      (σ', p) ⊢ (e, s) 1 ⇓∞ σ'' →
      (σ, p) ⊢ (e, s) 1+n ⇓∞ σ''' →
      σ'' = σ'''.
  Proof.
    intros. induction n.
    - assert (σ = σ'). eapply loop0_store_inv. eauto. subst. simpl in H1.
      admit.

  Lemma loop_false_inv2 : ∀ n σ σ' σ'' p e s v,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      n <= S n →
      (σ, p) ⊢ (e, s) S n ⇓∞ σ'' →
      σ'' ⊢ e ⇓ₑ (VBool v) →
      false = v.
  Proof.
    intros n. induction n; intros.
    - assert (σ = σ'). eapply loop0_store_inv. eauto. subst.
      eapply loop_false_inv. eauto. eauto. eauto.
    - assert (∃ σ0, (σ, p) ⊢ (e, s) n ⇓∞ σ0). eapply loop_sigma_exists.
      destruct H4. eapply (@IHn σ x σ'' _ _ _ _).
      eauto. 2: eauto. 3: eauto.
      Admitted.
      
    
  Lemma loop_false_inv2_m : ∀ σ σ' σ'' p e s n m v,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      n <= m →
      (σ, p) ⊢ (e, s) m ⇓∞ σ'' →
      σ'' ⊢ e ⇓ₑ (VBool v) →
      false = v.
  Proof.
    intros. induction H1.
    - subst. admit.

    intros. generalize dependent n. induction m; intros.
    - assert (n = 0). omega. subst. assert (σ' = σ''). eapply loop0_deterministic. eauto. eauto.
      subst. assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto. inversion H4.
      reflexivity.
    - induction H2.
      + assert (n = 0). omega. subst. assert (σ = σ'). eapply loop0_store_inv. eauto. subst.
        assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto. inversion H2.
        reflexivity.
      + assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto. inversion H4.
        reflexivity.
      +  


    generalize dependent m. induction H.
    - intros. destruct m.
      + assert (σ = σ''). eapply loop0_store_inv. eauto. subst.
        assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto.
        inversion H. reflexivity.
      + assert (σ = σ''). eapply loop_false_store_inv. eauto. eauto. subst.
        assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto.
        inversion H. reflexivity.
    - intros. assert (σ = σ''). eapply loop_false_store_inv. eauto. eauto. subst.
      assert (VBool false = VBool v). eapply exp_deterministic. eauto. eauto.
      inversion H4. reflexivity.
    - intros. destruct m.
      + omega.
      + assert (n <= m). omega.
        

  (*
  Theorem loop_determinisitc : ∀ σ p e s n1 n2 σ' σ'',
      σ'  ⊢ e ⇓ₑ (VBool false) →
      σ'' ⊢ e ⇓ₑ (VBool false) →
      (σ, p) ⊢ (e, s) n1 ⇓∞ σ'  →
      (σ, p) ⊢ (e, s) n2 ⇓∞ σ'' →
      σ' = σ''
  with stmt_deterministic : ∀ σ p s σ' σ'',
      (σ, p) ⊢ s ⇓ σ'  →
      (σ, p) ⊢ s ⇓ σ'' →
      σ' = σ''.
  Proof.
    (* loop determinisitc *)
    - intros σ p e s n1 n2 σ' σ'' E1 E2 F1 F2.
      generalize dependent σ''. generalize dependent n2.
      induction n1.
      + intros. destruct n2. eapply loop0_deterministic. eauto. eauto. eauto.
      + intros. destruct n2.
        * assert (σ = σ''). eapply loop0_store_inv. eauto. subst.
          eapply loop_false_deterministic. eauto. eauto. eauto.
        * admit.
          (*
          inversion E1. inversion E2. subst. reflexivity. subst.
          assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H0.
          subst. assert (n = n1). omega. subst.
          *)

        (* can not pass the termination check: *)
        (*
      intros σ p e s n1 n2 σ' σ'' E1 E2 F1 F2.
      generalize dependent σ''. generalize dependent n2.
      induction E1.
      + intros. inversion E2. subst. reflexivity. subst. reflexivity. subst.
        eapply loop_false_store_inv. eauto. eauto.
      + intros. inversion E2. reflexivity. reflexivity.
        subst. eapply loop_false_store_inv. eauto. eauto.
      + intros. inversion E2; subst.
        * assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H1.
        * assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H2.
        * apply (@RWhileMore σ σ'0 σ''0 _ _ _ _) in H1. 2: eauto. 2: eauto.
          apply (@RWhileMore σ σ' σ'' _ _ _ _) in E1. 2: eauto. 2: eauto.
          eapply RWhile in E1. 2: eauto. eapply RWhile in E2. 2: eauto.
          apply (@stmt_deterministic _ _ _ σ'' σ''0 E1 E2).
          *)
    (* stmt determinisitc *)
   *)

  Theorem loop_false_store_inv3 : ∀ σ σ' σ'' p e s n m,
      (σ, p) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool false) →
      m >= n →
      (σ', p) ⊢ (e, s) m ⇓∞ σ'' →
      (σ', p) ⊢ (e, s) m+1 ⇓∞ σ'' →
      σ' = σ''.
  Proof.
    intros. induction H2.
    - reflexivity.
    - reflexivity.
    - assert (false = true). apply (@loop_false_inv _ _ _ _ _ _ _ H2 H0 H4).
      inversion H6.
  Qed.

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

  Theorem loop_false_store_inv4' : ∀ σ σ1 σ2 p e s n m,
      (σ, p) ⊢ (e, s) n ⇓∞ σ1 →
      σ1 ⊢ e ⇓ₑ (VBool false) →
      m > n →
      (σ, p) ⊢ (e, s) m ⇓∞ σ2 →
      σ2 ⊢ e ⇓ₑ (VBool false) →
      σ1 = σ2.
    Proof.
      intros. generalize dependent σ1. induction H2.
      - intros. assert ((σ, c) ⊢ (e, s) n ⇓∞ σ). eapply RWhileFalse. eauto.
        apply (@loop_false_deterministic _ _ _ _ _ _ _ _ H3 H H2).
      - intros. assert ((σ, c) ⊢ (e, s) n ⇓∞ σ). eapply RWhileFalse. eauto.
        apply (@loop_false_deterministic _ _ _ _ _ _ _ _ H H0 H4).
      - intros. assert (n <= n0). omega.
        assert (false = true). apply (@loop_false_inv2 _ _ _ _ _ _ _ _ _ H4 H5 H6 H2 H).
        inversion H7.
    Qed.

  Theorem loop_same_n_deterministic : ∀ σ p e s n σ' σ'',
      (σ, p) ⊢ (e, s) n ⇓∞ σ'  →
      (σ, p) ⊢ (e, s) n ⇓∞ σ'' →
      σ' = σ''
  with stmt_deterministic : ∀ σ p s σ' σ'',
      (σ, p) ⊢ s ⇓ σ'  →
      (σ, p) ⊢ s ⇓ σ'' →
      σ' = σ''.
  Proof. {
    intros σ p e s n σ' σ'' E1 E2. generalize dependent σ''.
    induction E1.
    - intros. eapply loop0_store_inv. eauto.
    - intros. eapply loop_false_store_inv. eauto. eauto.
    - intros. inversion E2.
      + subst. omega.
      + subst. assert (false = true). eapply loop_false_inv. eauto. eauto. eauto. inversion H2.
      + subst. assert (n0 = n). omega. subst.
        assert (σ' = σ'0). eapply IHE1. eauto. subst.
        eapply stmt_deterministic. eauto. eauto.
    } {
    intros σ p s σ' σ'' E1 E2.
      generalize dependent σ''.
      induction E1; intros; inversion E2; auto.
      + assert (VLoc l = VLoc l0) as LEq. { eapply exp_deterministic. eauto. auto. } inversion LEq.
        assert (VNum idx = VNum idx0) as NEq. { eapply exp_deterministic. eauto. auto. } inversion NEq.
        assert (v = v0). { eapply exp_deterministic. eauto. auto. } subst.
        remember (σ l0) as σl. rewrite H12 in H2. inversion H2. subst. reflexivity.
      + assert (VBool true = VBool false) as BEq.
        { eapply exp_deterministic. eauto. auto. } inversion BEq.
      + assert (VBool true = VBool false) as BEq.
        { eapply exp_deterministic. eauto. auto. } inversion BEq.
      + subst. bdestruct (n =? n0).
        * subst. eapply loop_same_n_deterministic. eauto. eauto.
        * bdestruct (n <? n0).
          apply (loop_false_store_inv4' _ _ _ _ _ _ _ _ H H0 H2 H5 H7).
          assert (n > n0). omega. symmetry.
          apply (loop_false_store_inv4' _ _ _ _ _ _ _ _ H5 H7 H3 H H0).
      + specialize IHE1_1 with (σ'' := σ'0).
        specialize IHE1_2 with (σ''0 := σ''0).
        assert (σ' = σ'0). { apply IHE1_1. apply H3. } subst.
        assert (σ'' = σ''0). { apply IHE1_2. apply H5. } apply H.
    }
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

  Fixpoint eval_exp (e: exp) (σ: store) : option val :=
    match e with
    (* | EId x  => o ← (σ (LId x)) IN o 0 *)
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

  (* TODO: distinguish divergence and runtime error *)

  Fixpoint eval_loop (b1: exp) (s: stmt) (σ: store) (c: path) (n: nat)
           (evstmt: store -> path -> option (option store)) : option (option store) :=
    match n with
    | O => Some (Some σ)
    | S n' =>
      σ' ↩ eval_loop b1 s σ c n' evstmt IN
      b ← eval_exp b1 σ' >>= toBool IN
      if b then evstmt σ' (PWhile c n') else None (* error or timeout ??? *)
    end.

  Fixpoint eval_stm (s: stmt) (σ: store) (c: path) (m: nat) : option (option store) :=
    match s with
    | x ::= ALLOC =>
      Some (Some (LNew c st↦ mt_obj ;
            LId x st↦ (0 obj↦ (VLoc (LNew c))) ;
            σ))
    | e1[[e2]] ::= e3 =>
      l ← eval_exp e1 σ >>= toLoc IN
      n ← eval_exp e2 σ >>= toNat IN
      v ← eval_exp e3 σ IN
      o ← σ l IN
      Some (Some (l st↦ (n obj↦ v ; o) ; σ))
    | IF b THEN s1 ELSE s2 FI =>
      b ← eval_exp b σ >>= toBool IN
      if b
      then eval_stm s1 σ (PThen c) m
      else eval_stm s2 σ (PElse c) m
    | WHILE b1 DO s1 END =>
      n ← idx m (fun i =>
                   match (σ' ↩ eval_loop b1 s1 σ c i (fun σ'' c1 => eval_stm s1 σ'' c1 m) IN
                          b ← eval_exp b1 σ' >>= toBool IN
                          Some (Some (negb b))) with
                   | Some (Some b) => Some b
                   | Some None => Some true
                   | None => None
                   end
                (* TODO: cleanup slightly. inline eval_loop? *)
                ) IN
      eval_loop b1 s1 σ c n (fun σ' c1 => eval_stm s1 σ' c1 m)
    | s1 ;; s2 =>
      σ' ↩ eval_stm s1 σ (PFst c) m IN
      eval_stm s2 σ' (PSnd c) m
    | SKIP =>
      Some (Some σ)
    | SAbort => Some None
    end.

End IMPEval.
