Require Import NewImp.

Module IMPEvalTest.

  Import NewImp.IMPEval.
  
  Definition W : id := Id 10.
  Definition X : id := Id 11.
  Definition Y : id := Id 12.
  Definition Z : id := Id 13.
  
  Definition deref (σ : store) (x : id) :=
    o ← σ (LId x) IN
    o 0.

  Definition test_eval_stmt (σ: store) (s: stmt) :=
    match evalStmt s σ PRoot 500 with
    | Some (Some σ') => Some (Some (deref σ' W, deref σ' X, deref σ' Y, deref σ' Z))
    | Some None => Some None
    | None    => None
    end.

  Example testcase_1:
    (test_eval_stmt σ0
                   (ELoc X ::= ENum 2;;
                    ELoc Y ::= σ[X])) = Some (Some (None, Some (VNum 2), Some (VNum 2), None)).
  Proof. reflexivity. Qed.

  Example testcase_2:
    (test_eval_stmt σ0
                   (ELoc X ::= ENum 2;;
                    ELoc X ::= EPlus (σ[X]) (ENum 3))) = Some (Some (None, Some (VNum 5), None, None)).
  Proof. reflexivity. Qed.

  Example testcase_3:
    (test_eval_stmt σ0
                   (X ::= ALLOC;;
                    ELoc X ::= ENum 2;;
                    ELoc Y ::= σ[X])) = Some (Some (None, Some (VNum 2), Some (VNum 2), None)).
  Proof. reflexivity. Qed.

  Example testcase_4:
    (test_eval_stmt σ0
                   (X ::= ALLOC;;
                    ELoc X ::= ENum 2;;
                    Y ::= ALLOC;;
                    ELoc Y ::= EPlus (σ[X]) (ENum 3))) = Some (Some (None, Some (VNum 2), Some (VNum 5), None)).
  Proof. reflexivity. Qed.

  Example testcase_5:
    (test_eval_stmt σ0
                   (X ::= ALLOC;;
                    ELoc X[[ENum 0]] ::= ENum 2;;
                    ELoc X[[ENum 1]] ::= ENum 3;;
                    ELoc Y ::= ELoc X[[ENum 1]])) = Some (Some (None, Some (VNum 2), Some (VNum 3), None)).
  Proof. reflexivity. Qed.

  Definition while1 : stmt :=
    ELoc X ::= ENum 4;;
    ELoc Z ::= σ[X];;
    ELoc Y ::= ENum 1;;
    WHILE ENeg (EEq (σ[Z]) (ENum 0)) DO
      ELoc Y ::= EMult (σ[Y]) (σ[Z]);;
      ELoc Z ::= EMinus (σ[Z]) (ENum 1)
    END.

  Definition while_ill : stmt :=
    ELoc X ::= ENum 4;;
    ELoc Z ::= σ[X];;
    ELoc Y ::= ENum 1;;
    WHILE (ENum 0) DO
      ELoc Y ::= EMult (σ[Y]) (σ[Z]);;
      ELoc Z ::= EMinus (σ[Z]) (ENum 1)
    END.

  Example while_ill_case :
    (test_eval_stmt σ0 while_ill) = Some None.
  Proof. reflexivity. Qed.

  Definition if_ill : stmt :=
    ELoc X ::= ENum 4;;
    ELoc Z ::= σ[X];;
    ELoc Y ::= ENum 1;;
    IF (ENum 0) THEN
        ELoc Y ::= EMult (σ[Y]) (σ[Z])
        ELSE ELoc Z ::= EMinus (σ[Z]) (ENum 1)
    FI.

  Example if_ill_case :
    (test_eval_stmt σ0 if_ill) = Some None.
  Proof. reflexivity. Qed.

  Example testcase_6:
    (test_eval_stmt σ0 while1) = Some (Some (None, Some (VNum 4), Some (VNum 24), Some (VNum 0))).
  Proof. reflexivity. Qed.

  Definition while2 : stmt :=
    X ::= ALLOC;;
    ELoc Y ::= ENum 0;;
    WHILE ELt (σ[Y]) (ENum 5) DO
      ELoc X[[ σ[Y] ]] ::= σ[Y];;
      ELoc Y ::= EPlus (σ[Y]) (ENum 1)
    END;;
    ELoc Z ::= ENum 0;;
    ELoc W ::= ENum 0;;
    WHILE ELt (σ[Z]) (σ[Y]) DO
      ELoc W ::= EPlus (σ[W]) (ELoc X[[ σ[Z] ]]);;
      ELoc Z ::= EPlus (σ[Z]) (ENum 1)
    END.

  Example testcase_7:
    (test_eval_stmt σ0 while2) = Some (Some (Some (VNum 10), Some (VNum 0), Some (VNum 5), Some (VNum 5))).
  Proof. reflexivity. Qed.

  Example testcase_8:
    (test_eval_stmt σ0
                (ELoc X ::= ENum 2;;
                IF ELt (σ[X]) (ENum 1)
                THEN ELoc Y ::= ENum 3
                ELSE ELoc Z ::= ENum 4
                FI)) = Some (Some (None, Some (VNum 2), None, Some (VNum 4))).
  Proof. reflexivity. Qed.

  Example testcase_9:
    (test_eval_stmt σ0
                   (ELoc X ::= σ[Z])) = Some None.
  Proof. reflexivity. Qed.

  Example testcase_10:
    (test_eval_stmt σ0
                   (WHILE (EBool true) DO SKIP END)) = None.
  Proof. reflexivity. Qed.

  Example testcase_11:
    (test_eval_stmt σ0
                   (X ::= ALLOC;;
                    ELoc X[[ENum 0]] ::= ENum 2;;
                    ELoc Y ::= ELoc X[[ENum 1]])) = Some None.
  Proof. reflexivity. Qed.

  Example testcase_12:
    (test_eval_stmt σ0
                   (ELoc X[[ENum 1]] ::= ENum 2)) = Some (Some (None, None, None, None)). (* error or allowed ??? *)
  Proof. reflexivity. Qed.


End IMPEvalTest.
