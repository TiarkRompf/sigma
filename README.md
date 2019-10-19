Precise Reasoning with Structured Time, Structured Heaps, and Collective Operations
==============================

Program analysis by optimizing for clarity.

## Coq Proof

### Definition and modelization

#### IMP

 - IMP language [(Figure 3)](coq/IMP.v#L74)
 - IMP Relational big-step semantic (Figure 4)
   * [Expression Evaluation](coq/IMP.v#L325)
   * [Loop Evaluation](coq/IMP.v#L368)
   * [Statement Evaluation](coq/IMP.v#L377)
 - IMP functonal semantics (Figure 5)
   * [Expression Evaluation](coq/IMP.v#L592)
   * [Loop Evaluation](coq/IMP.v#L654)
   * [Statement Evaluation](coq/IMP.v#L668)

#### FUN

 - FUN language [(Figure 6)](coq/FUN.v#L14)
 - FUN value representation for Option Monad [(Figure 7)](coq/FUN.v#L39)
 - FUN small [step semantics](coq/FUN.v#L258)

#### IMP to FUN transformation

   * [Expression Transformation](coq/FUN.v#L137)
   * [Statement Transformation](coq/FUN.v#L169)
   * [Equivalence](coq/FUN.v#L435)

### Theorems

 - IMP is deterministic
    * [Expression Deterministic](coq/IMP.v#L410)
    * [Proposition 3.3](coq/IMP.v#L466)

 - Adequacy between big-step semantics and functional semantics.
    * [Expression Adequacy](coq/IMP.v#L714)
    * [Statement Adequacy (1st half)](coq/IMP.v#L1009)
    * [Statement Adequacy (2nd half)](coq/IMP.v#L1182)
    * [Proposition 3.9](coq/IMP.v#1255)

  - Soundness of the IMP to FUN transformation
    * [Expression Soundness](coq/FUN.v#L1316)
    * [Statement Soundness](coq/FUN.v#L2066)
    * [Theorem 3.14](coq/FUN.v#L2299)
