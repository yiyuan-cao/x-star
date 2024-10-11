Require Import goal proof_auto proof_manual.

Module VC_Correctness : VC_Correct.
  Include example_strategy_proof.
  Include proof_auto.
  Include proof_manual.
End VC_Correctness.
