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

(* IMP Syntax (Figure 3) *)

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
| SAlloc : id -> stmt
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

Definition obj := nat ⇀ val.

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

Lemma nat_dec : forall (n1 n2 : nat), n1 = n2 \/ n1 <> n2.
Proof. intros. omega. Qed.

Lemma id_dec : forall (i1 i2 : id), i1 = i2 \/ i1 <> i2.
Proof.
  intros i1 i2.
  destruct i1; destruct i2; auto.
  destruct (nat_dec n n0); auto.
  right. intro contra. apply H. inversion contra. auto.
Qed.

Lemma path_dec : forall (p1 p2 : path), p1 = p2 \/ p1 <> p2.
  induction p1; destruct p2; try (right; discriminate); auto;
    try (destruct (IHp1 p2); [ subst; auto | right; intro contra; apply H; inversion contra; auto ]).
  destruct (nat_dec n n0); [ subst; auto | right; intro contra; apply H; inversion contra; auto ].
Qed.

Lemma loc_dec : forall (l1 l2 : loc), l1 = l2 \/ l1 <> l2.
Proof.
  intros l1 l2.
  destruct l1; destruct l2; auto; try (right; discriminate).
  destruct (id_dec i i0); subst; auto. right. intro contra. apply H. inversion contra. auto.
  destruct (path_dec p p0); subst; auto. right. intro contra. apply H. inversion contra. auto.
Qed.

Lemma beq_loc_eq: forall l, beq_loc l l = true.
Proof.
  intro l. destruct l; simpl.
  - destruct i. apply Nat.eqb_refl.
  - induction p; auto. simpl. rewrite IHp. simpl. apply Nat.eqb_refl.
Qed.

Lemma beq_id_neq : forall i1 i2, i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros. destruct i1; destruct i2; auto.
  destruct (nat_dec n n0); subst; auto. apply False_rec; auto.
  simpl. apply Nat.eqb_neq; auto.
Qed.

Lemma beq_path_neq : forall p1 p2, p1 <> p2 -> beq_path p1 p2 = false.
Proof.
  induction p1; destruct p2; auto; intros; try (apply IHp1; intro contra; subst; auto).
  - apply False_rec. auto.
  - destruct (nat_dec n n0); subst.
    + simpl. replace (beq_path p1 p2) with false; auto; try (symmetry; apply IHp1; intro contra; subst; auto).
    + simpl. replace (beq_nat n n0) with false.
      apply andb_false_r.
      symmetry. apply Nat.eqb_neq. assumption.
Qed.

Lemma beq_loc_neq: forall l1 l2, l1 <> l2 -> beq_loc l1 l2 = false.
Proof.
  intros. destruct l1; destruct l2; auto. 
  - destruct (id_dec i i0); subst. apply False_rec. auto.
    simpl. apply beq_id_neq; auto.
  - destruct (path_dec p p0); subst. apply False_rec. auto.
    simpl. apply beq_path_neq. auto.
Qed.

Lemma update_eq_loc : forall { A : Type } (m : total_map loc A) x v,
  (t_update beq_loc m x v) x = v.
Proof.
  intros. unfold t_update.
  rewrite beq_loc_eq. reflexivity.
Qed.

Lemma update_neq_loc : forall { A : Type } (m : total_map loc A) x y v,
  x <> y ->
  (t_update beq_loc m x v) y = m y.
Proof.
  intros. unfold t_update. 
  rewrite beq_loc_neq; auto.
Qed.

Lemma update_eq_nat : forall { A : Type } (m : total_map nat A) x v,
  (t_update Nat.eqb m x v) x = v.
Proof.
  intros. unfold t_update.
  replace (x =? x) with true; auto; symmetry; apply Nat.eqb_eq; auto.
Qed.

Lemma update_neq_nat : forall { A : Type } (m : total_map nat A) x y v,
  x <> y ->
  (t_update Nat.eqb m x v) y = m y.
Proof.
  intros. unfold t_update.
  replace (x =? y) with false; auto; symmetry; apply Nat.eqb_neq; auto.
Qed.

(* IMP Relational big-step semantics *)

Module IMPRel.
  (* Evaluation relation for expressions *)

  Reserved Notation "st '⊢' e '⇓ₑ' v" (at level 15).

  Inductive evalExpRel : store → exp → val → Prop :=
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
  where "st '⊢' e '⇓ₑ' v" := (evalExpRel st e v) : type_scope.

  Reserved Notation "'(' st1 , c ')' '⊢' '(' e , s ')' n '⇓∞' st2" (at level 15).
  Reserved Notation "( st1 , c ) '⊢' s '⇓' st2" (at level 15).

  Inductive evalLoopRel : store → path → exp → stmt → nat → store → Prop :=
  | RWhileZero : ∀ σ c e s,
      (σ, c) ⊢ (e, s) 0 ⇓∞ σ
  | RWhileMore : ∀ (σ σ' σ'' : store) c n e s,
      (σ, c) ⊢ (e, s) n ⇓∞ σ' →
      σ' ⊢ e ⇓ₑ (VBool true) →
      (σ', PWhile c n) ⊢ s ⇓ σ'' →
      (σ, c) ⊢ (e, s) 1+n ⇓∞ σ''
  where "( st1 , c ) ⊢ ( e , s ) n '⇓∞' st2" := (evalLoopRel st1 c e s n st2) : type_scope
  with evalStmt : store → path → stmt → store → Prop :=
  | RAlloc x : ∀ σ p,
      (σ, p) ⊢ x ::= ALLOC ⇓ (LId x  st↦ (0 obj↦ VLoc (LNew p)) ;
                              LNew p st↦ mt_obj ;
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

  Scheme evalLoopRelMut := Induction for evalLoopRel Sort Prop
    with evalStmtRelMut := Induction for evalStmt Sort Prop.

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
      { intro m. induction m; intros; inversion H1; inversion H2; subst; auto.
        assert (σ'1 = σ'2). eapply IHm; eauto. subst. eauto.
      }
      assert (∀ m σ' σ'', (σ, p) ⊢ (e, s) m ⇓∞ σ' →
                          σ' ⊢ e ⇓ₑ (VBool false) →
                          (σ, p) ⊢ (e, s) S m ⇓∞ σ'' →
                          False) as loop_false_mSm_contra.
      { intros. remember (S m) as sm. induction H3; subst.
        - omega.
        - inversion Heqsm; subst.
          assert (σ'0 = σ'1). eapply loop_deterministic; eauto. subst.
          assert (VBool false = VBool true). eapply exp_deterministic; eauto.
          inversion H6. }
      assert (∀ n m σ' σ'', (σ, p) ⊢ (e, s) n ⇓∞ σ' →
                            σ' ⊢ e ⇓ₑ (VBool false) →
                            (σ, p) ⊢ (e, s) m ⇓∞ σ'' →
                            n < m →
                            False) as loop_false_nm_contra.
      { intros. generalize dependent σ''0. induction H4; intros.
        - eapply loop_false_mSm_contra. apply H1. apply H2. apply H3.
        - inversion H3; subst. eapply IHle. apply H6.
      }
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

  (* Fixpoint idx1 (i : nat) (m : nat) (p : nat -> option (option bool)) : option (option nat) := *)
  Fixpoint idx1 (i : nat) (m : nat) (p : nat -> option bool) : option nat :=
    match m with
    | O => None (* out of fuel *)
    | S m' =>
      match p i with
      | Some true => Some i
      | Some false => idx1 (i + 1) m' p
      | None => Some i
      end
    end.

  (* idx finds the least index *)
  Definition idx (m : nat) (p : nat -> option bool) : option nat := idx1 0 m p.

  Fixpoint evalLoop (cnd : exp) (s : stmt) (σ : store) (c : path) (n : nat)
           (evstmt : store → path → option (option store)) : option (option store) :=
    match n with
    | O => Some (Some σ)
    | S n' =>
      σ' ↩ evalLoop cnd s σ c n' evstmt IN
      bv ↩ Some (〚cnd〛(σ') >>= toBool) IN
      if bv
      then evstmt σ' (PWhile c n') (* continue evaluation *)
      else Some None
    end.

  Reserved Notation "'〚' s '〛' ( st , c ) ( m )" (at level 90, left associativity).

  Fixpoint evalStmt (s: stmt) (σ: store) (c: path) (m: nat) : option (option store) :=
    match s with
    | x ::= ALLOC =>
      Some (Some (LId x st↦ (0 obj↦ (VLoc (LNew c))) ;
            LNew c st↦ mt_obj ;
            σ))
    | e1[[e2]] ::= e3 =>
      l ↩ Some (〚e1〛(σ) >>= toLoc) IN
      n ↩ Some (〚e2〛(σ) >>= toNat) IN
      v ↩ Some (〚e3〛(σ)) IN
      o ↩ Some( σ l )  IN
      Some (Some (l st↦ (n obj↦ v ; o) ; σ))

    | IF b THEN s1 ELSE s2 FI =>
      b ↩ Some (〚b〛(σ) >>= toBool) IN
      if b
      then 〚s1〛(σ, PThen c)(m)
      else 〚s2〛(σ, PElse c)(m)
    | WHILE cnd DO s END =>
      n ← idx m (fun i => match (σ' ↩ evalLoop cnd s σ c i (fun σ'' c1 => 〚s〛(σ'', c1)(m)) IN
                                 b  ← 〚cnd〛(σ') >>= toBool IN
                                 Some (Some (negb b))) with
                          | Some (Some b) => Some b
                          | Some None => Some true
                          | None => None
                          end) IN
      σ' ↩ evalLoop cnd s σ c n (fun σ' c1 => 〚s〛(σ', c1)(m)) IN
      b2 ↩ Some (〚cnd〛(σ') >>= toBool) IN
      Some (Some σ')
    | s1 ;; s2 =>
      σ' ↩ 〚s1〛(σ, PFst c)(m) IN
     〚s2〛(σ', PSnd c)(m)
    | SKIP => Some (Some σ)
    | SAbort => Some None
    end
  where "'〚' s '〛' ( st , c ) ( m )" := (evalStmt s st c m) : type_scope.

  Definition eval (s: stmt) :=〚s〛(σ0, PRoot)(500).

End IMPEval.

Module Adequacy.

  Import IMPRel.
  Import IMPEval.

  Theorem exp_adequacy : ∀ e σ v,
    σ ⊢ e ⇓ₑ v <->〚 e 〛(σ) = Some v.
  Proof.
    intros. split.
    - intros. induction H; simpl; auto; try (rewrite IHevalExpRel1; rewrite IHevalExpRel2; simpl; reflexivity).
      + rewrite IHevalExpRel. simpl.  reflexivity.
      + rewrite IHevalExpRel1. rewrite IHevalExpRel2. simpl. rewrite H1. auto.
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
      idx1 x n p = Some i →
      idx1 x m p = Some i.
  Proof.
    intro m. induction m; intros.
    - inversion H. subst. simpl in H0. inversion H0.
    - simpl. destruct n.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (p x) eqn:Hpx.
        destruct b eqn:Hb.
        apply H0. assert (m >= n). omega. eapply IHm. apply H1.
        apply H0. apply H0.
  Qed.

  Lemma stmt_eval_more_val_Sn : ∀ s n σ c v,
      evalStmt s σ c n = Some v →
      evalStmt s σ c (S n) = Some v.
  Proof.
    intro s. induction s; intros; simpl; simpl in H; auto.
    - destruct (〚 e 〛 (σ) >>= toBool); auto. destruct b; eauto.
    - unfold idx.
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
            destruct o; auto.
            destruct (〚 e 〛 (s0) >>= toBool); auto.
            destruct b; eauto.
          + inversion H0.
      }
     assert (∀ x a n m o,
          idx1 a x
            (λ i : nat,
              match
                 σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n)) IN
                 b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
              with
              | Some (Some b) => Some b
              | Some None => Some true
              | None => None
              end) = Some m →
          evalLoop e s σ c m (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n)) = Some o ->
          idx1 a (S x)
            (λ i : nat,
              match
                 σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n)) IN
                 b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
              with
              | Some (Some b) => Some b
              | Some None => Some true
              | None => None
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
            destruct o1; auto.
            destruct (〚 e 〛 (s0) >>= toBool); auto.
            destruct b; auto.
            eapply IHx. apply H0. eassumption.
          + inversion H0; subst. rewrite <- Heqloopn in H1. inversion H1.
      }
      unfold idx in *.
      remember (idx1 0 n (λ i : nat,
                match
                  σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))
                  IN b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
                with
                | Some (Some b) => Some b
                | Some None => Some true
                | None => None
                end)) as ix0.
      remember (idx1 0 (S n) (λ i : nat,
            match
              σ' ↩ evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S n))
              IN b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
            with
            | Some (Some b) => Some b
            | Some None => Some true
            | None => None
            end)) as ix1.
      destruct ix0; inversion H; clear H.
      assert (∃ v, evalLoop e s σ c n0 (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(n)) = Some v).
      { remember (evalLoop e s σ c n0 (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(n))) as l.
        destruct l. exists o. reflexivity. inversion H1. }
      destruct H. rewrite H.
      symmetry in Heqix0.
      eapply idxMoreStep in Heqix0; try eassumption. rewrite Heqix0 in Heqix1. subst.
      apply evalLoopMoreStep in H. rewrite H. reflexivity.
    - simpl in H. simpl.
      destruct (〚 s1 〛 (σ, PFst c)(n)) eqn:Eqs1.
      eapply IHs1 in Eqs1.
      + destruct o.
        * eapply IHs2 in H. rewrite Eqs1. apply H.
        * rewrite Eqs1. apply H.
      + inversion H.
  Qed.

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

  Lemma loop_eval_more_val_nm : ∀ i e s n m σ c v,
      n <= m →
      evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n)) = Some v →
      evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(m)) = Some v.
  Proof.
    intro i. induction i.
    - intros. simpl. inversion H0; subst. reflexivity.
    - intros.
      remember (evalLoop e s σ c i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(n))) as hyp.
      destruct hyp.
      + simpl. symmetry in Heqhyp. simpl in H0. rewrite Heqhyp in H0; simpl in H0.
        eapply IHi in Heqhyp; eauto. rewrite Heqhyp.
        destruct o; eauto. destruct (〚 e 〛 (s0)); eauto. destruct v0; eauto. destruct b; eauto.
        simpl. simpl in H0. eapply stmt_eval_more_val_nm; eauto.
      + simpl. simpl in H0. rewrite <- Heqhyp in H0; simpl in H0. inversion H0.
  Qed.


  Definition evalLoop_monotone_lower (e : exp) (s : stmt) (sigma : store) (p: path) (k n m : nat): Prop :=
   forall i, k <= i -> i < n ->
    exists sigma', evalLoop e s sigma p i (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m)) =
    Some (Some sigma') /\ evalExp e sigma' = Some (VBool true).

  Definition evalLoop_monotone (e : exp) (s : stmt) (sigma : store) (p: path) (k : nat) (m : nat): Prop :=
    evalLoop_monotone_lower e s sigma p 0 k m.

  Lemma evalLoop_monotone_Sk : forall e s sigma p k m sigma',
    evalLoop_monotone e s sigma p k m ->
    evalLoop e s sigma p k (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') /\ evalExp e sigma' = Some (VBool true) ->
    evalLoop_monotone e s sigma p (S k) m.
  Proof.
    intro e. intros. intro i. intros.
    bdestruct (i =? k).
    + subst i. exists sigma'. eauto.
    + eapply H; omega.
  Qed.

  Lemma evalLoop_monotone_more_val_nm : forall e s sigma p k n m,
    n <= m ->
    evalLoop_monotone e s sigma p k n ->
    evalLoop_monotone e s sigma p k m.
  Proof.
    intro e. intros. intro i. intros.
    destruct (H0 i) as [sigma' H0i]; eauto.
    destruct H0i as [H0il H0ic].
    exists sigma'. split; eauto.
    eapply loop_eval_more_val_nm; eauto.
  Qed.

  Definition idx1_constant (n m : nat) (p : nat -> option bool): Prop :=
    forall k, k <= n -> idx1 (n - k) (m + k) p = Some n.

  Lemma idx1_evalLoop_terminate : forall e s sigma sigma' p n m,
    evalLoop_monotone e s sigma p n (S m) ->
    evalLoop e s sigma p n (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S m)) = Some (Some sigma') ->
    evalExp e sigma' = Some(VBool false) ->
    idx1_constant n (S m) (λ i : nat,
                match
                  σ' ↩ evalLoop e s sigma p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S m + n))
                  IN b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
                with
                | Some (Some b) => Some b
                | Some None => Some true
                | None => None
                end).
  Proof.
   intros. unfold idx1_constant.
   intro k. induction k.
   - intros. replace (n - 0) with n; try omega. simpl.
     assert (evalLoop e s sigma p n (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S (m + n))) = Some (Some sigma')). {
       eapply loop_eval_more_val_nm with (n := S m); eauto. omega.
     }
     rewrite H3. rewrite H1. reflexivity.
   - intros. simpl.
     destruct (H (n - S k)); try omega.
     destruct H3 as [Hs Hc].
     assert (evalLoop e s sigma p (n - S k) (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S (m + n))) = Some (Some x)). {
       eapply loop_eval_more_val_nm with (n := S m); eauto. omega.
     }
     rewrite H3. rewrite Hc. simpl.
     replace (n - S k + 1) with (n - k); try omega.
     replace (m + S k) with (S m + k); try omega.
     apply IHk. omega.
  Qed.

  Lemma idx_evalLoop_terminate : forall e s sigma sigma' p n m,
    evalLoop_monotone e s sigma p n m ->
    evalLoop e s sigma p n (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(m)) = Some (Some sigma') ->
    evalExp e sigma' = Some(VBool false) ->
    idx (S m + n) (λ i : nat,
                match
                  σ' ↩ evalLoop e s sigma p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S m + n))
                  IN b ← 〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
                with
                | Some (Some b) => Some b
                | Some None => Some true
                | None => None
                end) = Some n.
  Proof.
   intros. unfold idx.
   assert (n - n = 0) as Hz. omega.
   rewrite <- Hz.
   eapply idx1_evalLoop_terminate; eauto.
   eapply evalLoop_monotone_more_val_nm with (n := m); eauto.
   eapply loop_eval_more_val_nm with (n := m); eauto.
  Qed.

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
    - assert (forall k sigma, (σ, p)⊢ (e, s) k ⇓∞ sigma ->
        exists m, evalLoop_monotone e s σ p k m
          /\ evalLoop e s σ p k (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(m))
          = Some (Some sigma)). {
      intro k. induction k.
      + intros sigma Hlo. inversion Hlo; subst. exists 1. split.
        unfold evalLoop_monotone. unfold evalLoop_monotone_lower. intros. apply False_rec. omega.  reflexivity.
      + intros. simpl. inversion H0; subst.
        eapply IHk in H2. destruct H2 as [w2 H2].
        eapply IHs in H10. destruct H10 as [w10 H10].
        exists (w2 + w10).
        destruct H2 as [H2mon H2].
        split.
        * eapply evalLoop_monotone_Sk. eapply evalLoop_monotone_more_val_nm with (n := w2); eauto; try omega.
          split. eapply loop_eval_more_val_nm with (n := w2); eauto; try omega.
          apply exp_adequacy in H3. rewrite H3. reflexivity.
        * eapply loop_eval_more_val_nm with (m := w2 + w10) in H2; try omega. rewrite H2.
          apply exp_adequacy in H3. rewrite H3. simpl.
          eapply stmt_eval_more_val_nm with (n := w10); try omega.
          apply H10.
      }
      simpl.
      assert (Hloop := H4).
      apply H0 in H4. destruct H4 as [w H4].
      destruct H4 as [H4mon H4].
      clear H0.
      exists (S w + n). (* max 1, w, n *)
      assert (idx (S w + n)
        (λ i : nat,
          match
            σ'0 ↩ evalLoop e s σ p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(S w + n))
            IN b ← 〚 e 〛 (σ'0) >>= toBool IN Some (Some (negb b))
          with
          | Some (Some b) => Some b
          | Some None => Some true
          | None => None
          end) = Some n) as idxVal. {
            eapply idx_evalLoop_terminate; eauto.
            apply exp_adequacy; eauto. }
      rewrite idxVal.
      eapply loop_eval_more_val_nm with (m := S w + n) in H4; try omega. rewrite H4.
      apply exp_adequacy in H6. rewrite H6. reflexivity.
    - apply IHs1 in H4. apply IHs2 in H6.
      destruct H4 as [ms1 Hs1].
      destruct H6 as [ms2 Hs2].
      exists (ms1 + ms2).
      simpl.
      apply stmt_eval_more_val_nm with (m:= ms1 + ms2) in Hs1; try omega.
      rewrite Hs1. eapply stmt_eval_more_val_nm with (n := ms2).
      omega.
      assumption.
    - exists 1. inversion H; subst. reflexivity.
   Qed.

  Lemma idx1_val_min : forall m i p n,
    idx1 i m p = Some n -> n >= i.
  Proof.
    intro m.
    induction m.
    - intros. inversion H.
    - intros. simpl in H.
      destruct (p i); try inversion H; clear H; auto.
      destruct b; try inversion H1; clear H1.
      auto.
      assert (n >= i + 1). eapply IHm; eauto. omega.
  Qed.

  Lemma idx1_evalLoop_some : forall k e s sigma p n m,
    k <= n ->
    idx1 (n - k) (m + k) (fun i =>
                            match sigma' ↩ evalLoop e s sigma p i (fun σ'' c1 => evalStmt s σ'' c1 m) IN
                                   b  ← evalExp e sigma' >>= toBool IN
                                   Some (Some (negb b)) with
                              | Some (Some b) => Some b
                              | Some None => Some true
                              | None => None
                              end) = Some n ->
    and (evalLoop_monotone_lower e s sigma p (n - k) n m)
        (or (or (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = None)
                (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = Some None))
            (exists sigma', and (or (evalExp e sigma' = Some (VBool false)) (match evalExp e sigma' with Some v => toBool v | None => None end = None))
                                (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = Some (Some sigma')))).
  Proof.
    intro k.
    induction k.
    - intros.
      split.
      + intros k Hk Hn. apply False_rec. omega.
      + destruct m. inversion H0. simpl in H0.
        replace (n - 0) with n in H0; try omega.
        remember (evalLoop e s sigma p n (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(S m))) as loop.
        destruct loop; auto.
        destruct o; auto.
        right. exists s0; split; auto.
        remember (〚 e 〛 (s0)) as cond.
        destruct cond; auto.
        destruct v; try (right; reflexivity).
        destruct b; inversion H0.
        assert (n >= n + 1). eapply idx1_val_min; eauto. apply False_rec. omega.
        auto.
    - intros. replace (m + S k) with (S m + k) in H0; try omega.
      simpl in H0.
      remember (evalLoop e s sigma p (n - S k) (fun (σ'' : store) (c1 : path) => 〚 s 〛 (σ'', c1)(m))) as loop.
      destruct loop; inversion H0; clear H0; try (apply False_rec; omega).
      destruct o; inversion H2; clear H2; try (apply False_rec; omega).
      remember (〚 e 〛 (s0)) as cond.
      destruct cond; inversion H1; clear H1; try (apply False_rec; omega).
      destruct v; inversion H2; clear H2; try (apply False_rec; omega).
      destruct b; simpl in H1; inversion H1; clear H1; try (apply False_rec; omega).
      replace (n - S k + 1) with (n - k) in H2; try omega.
      apply IHk in H2; try omega.
      destruct H2 as [ Hmon Hlast ].
      split; auto.
      intros j Hj Hn.
      inversion Hj; subst.
      + exists s0. split; auto.
      + unfold evalLoop_monotone_lower in Hmon.
        destruct (Hmon (S m0)); try omega.
        destruct H1.
        exists x; split; auto.
  Qed.

  Lemma idx_more_val_inv : forall m n p i x,
      m >= n ->
      idx1 x n p = Some i ->
      idx1 x m p = Some i.
  Proof.
    intro m. induction m; intros.
    - inversion H. subst. simpl in H0. inversion H0.
    - simpl. destruct n.
      + simpl in H0. inversion H0.
      + simpl in H0. destruct (p x) eqn:Hpx.
        destruct b eqn:Hb.
        apply H0. assert (m >= n). omega. eapply IHm. apply H1.
        apply H0. apply H0.
  Qed.

  Lemma idx_evalLoop_some : forall e s sigma p n m,
    idx m (fun i =>
                  match sigma' ↩ evalLoop e s sigma p i (fun σ'' c1 => evalStmt s σ'' c1 m) IN
                         b  ← evalExp e sigma' >>= toBool IN
                         Some (Some (negb b)) with
                    | Some (Some b) => Some b
                    | Some None => Some true
                    | None => None
                    end) = Some n ->
    and (evalLoop_monotone e s sigma p n m)
        (or (or (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = None)
                (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = Some None))
            (exists sigma', and (or (evalExp e sigma' = Some (VBool false)) (match evalExp e sigma' with Some v => toBool v | None => None end = None))
                                (evalLoop e s sigma p n (fun (sigma'' : store) (c1 : path) => evalStmt s sigma'' c1 m) = Some (Some sigma')))).
  Proof.
    intros.
    destruct (idx1_evalLoop_some n e s sigma p n m); eauto.
    replace (n - n) with 0; eauto; try omega.
    eapply idx_more_val_inv with (n := m); eauto; try omega.
    split; auto.
    replace (n - n) with 0 in H0; auto; omega.
  Qed.

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
    - assert (forall k sigma,
        evalLoop e s σ p k (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(x)) = Some (Some sigma) ->
        (σ, p)⊢ (e, s) k ⇓∞ sigma). {
         intro k. induction k.
         + intros. inversion H1; subst. constructor.
         + intros.
           simpl in H1.
           remember (evalLoop e s σ p k (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(x))) as loop.
           destruct loop; try inversion H1; clear H1.
           destruct o; try inversion H3; clear H3.
           remember (〚 e 〛 (s0)) as cond.
           destruct cond; try inversion H2; clear H2.
           destruct v; try inversion H3; clear H3.
           destruct b; try inversion H2; clear H2.
           econstructor.
           - eapply IHk. eauto.
           - eapply exp_adequacy. rewrite Heqcond. reflexivity.
           - eapply IHs. exists x. apply H3. apply H3.
      }
      simpl in H0.
      remember (idx x
           (λ i : nat,
               match
                 σ' ↩ evalLoop e s σ p i (λ (σ'' : store) (c1 : path), 〚 s 〛 (σ'', c1)(x))
                 IN b ←〚 e 〛 (σ') >>= toBool IN Some (Some (negb b))
               with
               | Some (Some b) => Some b
               | Some None => Some true
               | None => None
               end) ) as idxx.
      destruct idxx; inversion H0; clear H0.
      eapply RWhile with (n := n).
      + assert (evalLoop e s σ p n (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(x)) = Some (Some σ')). {
          destruct (evalLoop e s σ p n (λ (σ' : store) (c1 : path), 〚 s 〛 (σ', c1)(x))); inversion H3; clear H3.
          destruct o; inversion H2; clear H2.
          destruct (〚 e 〛 (s0) >>= toBool); inversion H3; clear H3.
          reflexivity.
        }
        auto.
      + symmetry in Heqidxx. eapply idx_evalLoop_some in Heqidxx; eauto.
        destruct Heqidxx as [ _ [ [ Hloop | Hloop ] | [ sigma [ [ Hcsome | Hcnone ] Hloop ] ] ] ]; rewrite Hloop in H3; inversion H3; subst.
        * eapply exp_adequacy. rewrite Hcsome in H3; inversion H3; subst. auto.
        * rewrite Hcnone in H3; inversion H3.
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
    split. apply stmt_adequacy_1. apply stmt_adequacy_2.
  Qed.

End Adequacy.