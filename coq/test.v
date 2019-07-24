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

  Definition test_eval_stm (σ: store) (s: stmt) :=
    match eval_stm s σ PRoot 500 with
    | Some (Some σ') => Some (Some (deref σ' W, deref σ' X, deref σ' Y, deref σ' Z))
    | Some None => Some None
    | None    => None
    end.
  
  Compute
    (test_eval_stm σ0
                   (ELoc X ::= ENum 2;; ELoc Y ::= σ[X])).
  (*   ====>
       Some (None, Some 2, Some 2, None)   *)

  Compute
    (test_eval_stm σ0
                   (ELoc X ::= ENum 2;; ELoc X ::= EPlus (σ[X]) (ENum 3))).
  (*   ====>
       Some (None, Some 5, None, None)   *)

  Compute
    (test_eval_stm σ0
                   (X ::= ALLOC;; ELoc X ::= ENum 2;; ELoc Y ::= σ[X])).
  (*   ====>
       Some (None, Some 2, Some 2, None)   *)

  Compute
    (test_eval_stm σ0
                   (X ::= ALLOC ;; ELoc X ::= ENum 2;;
                    Y ::= ALLOC ;; ELoc Y ::= EPlus (σ[X]) (ENum 3))).
  (*   ====>
       Some (None, Some 2, Some 5, None)   *)

  Compute
    (test_eval_stm σ0
                   (X ::= ALLOC ;; ELoc X[[ENum 0]] ::= ENum 2;;
                    ELoc X[[ENum 1]] ::= ENum 3;; ELoc Y ::= ELoc X[[ENum 1]])).
  (*   ====>
       Some (None, Some 2, Some 5, None)   *)    

  Definition while1 : stmt :=
    ELoc X ::= ENum 4;;
    ELoc Z ::= σ[X];;
    ELoc Y ::= ENum 1;;
    WHILE ENeg (EEq (σ[Z]) (ENum 0)) DO
      ELoc Y ::= EMult (σ[Y]) (σ[Z]);;
      ELoc Z ::= EMinus (σ[Z]) (ENum 1)
    END.

  Compute
    (test_eval_stm σ0 while1).
  (*   ====>
       Some (None, Some 4, Some 24, 0)   *)

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

  Compute
    (test_eval_stm σ0 while2).
  (*   ====>
       Some (Some 10, Some 0, Some 5, 0)   *)

  Compute
    (test_eval_stm σ0
                (ELoc X ::= ENum 2;;
                IF ELt (σ[X]) (ENum 1)
                THEN ELoc Y ::= ENum 3
                ELSE ELoc Z ::= ENum 4
                FI)).
  (*   ====>
       Some (None, 2, None, 4)   *)

  Compute
    (test_eval_stm σ0
                   (ELoc X ::= σ[Z])).
  (*   ====>
       Some None (* error *) *) (* TODO: differentiate timeout and runtime error *)

  Compute
    (test_eval_stm σ0
                   (WHILE (EBool true) DO SKIP END)).
  (*   ====>
       None (* timeout *)   *)

End IMPEvalTest.
