# Models.lean Notes

## Goal

Keep fixed-chart tensor model representative facts in the fixed-chart model
layer, so higher tensor/nabla proofs do not unfold chart transport by hand.

## 2026-05-13: Center Model Identity

- Added `tensor0SModelInChart_center_eq_tensor0SModelAt`.
- The lemma identifies the chart-local model representative at the chart center
  with the fiber model representative at that same point.
- This was the final reusable rewrite needed by the total-nabla contraction
  proof in `HigherOrder.lean`.
- Verification passed.
