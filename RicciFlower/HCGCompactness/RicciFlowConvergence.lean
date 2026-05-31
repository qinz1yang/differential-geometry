import RicciFlower.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-Flow Convergence Conclusion

This file packages the limit side of Hamilton--Cheeger--Gromov compactness in
RicciFlower-native terms.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- The compactness conclusion: a strictly increasing subsequence and a smooth
pointed Cheeger--Gromov--Hamilton limit flow on the same time interval. -/
def CompactnessConclusion (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop :=
  exists L : PointedFlowData.{u, uE, uH} (I := I) X.D, exists subseq : Nat -> Nat,
    StrictMono subseq /\
      Nonempty.{max (max uE uH) u + 1} (SmoothCGHConverges (I := I) X L subseq)

end HCGCompactness
end RicciFlower
