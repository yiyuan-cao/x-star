Require Import example_strategy_goal example_strategy_proof.

Module example_Strategy_Correctness : example_Strategy_Correct.
  Include example_strategy_proof.
End example_Strategy_Correctness.
