import DifferentialGeometry.Analysis.ODE.InvariantSet
import DifferentialGeometry.Analysis.Convex.NormalCone
import DifferentialGeometry.Analysis.ODE.Flow.Defs
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_contDiffAt
    [CompleteSpace E] {f : ℝ → E → E} {C : Set E}
    (hC : IsForwardInvariantForODE f C)
    (hf : ∀ t x, x ∈ C → ContDiffAt ℝ 1 (Function.uncurry f) (t, x)) :
    VectorFieldTangentTo f C := by
  apply hC.vectorFieldTangentTo_of_exists_isIntegralCurveAt
  intro t x hx
  exact Flow.exists_isIntegralCurveAt_of_contDiffAt (hf t x hx)

theorem IsForwardInvariantForODE.vectorFieldTangentTo_of_contDiff
    [CompleteSpace E] {f : ℝ → E → E} {C : Set E}
    (hC : IsForwardInvariantForODE f C)
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    VectorFieldTangentTo f C :=
  hC.vectorFieldTangentTo_of_contDiffAt (fun _ _ _ => hf.contDiffAt)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem IsIntegralCurveOn.inner_nonpos_of_mapsTo_Icc
    {f : ℝ → V → V} {γ : ℝ → V} {a b : ℝ} {C : Set V} {ν : V}
    (hγ : IsIntegralCurveOn γ f (Icc a b)) (hab : a < b)
    (hC : MapsTo γ (Icc a b) C)
    (hnormal : ν ∈ DifferentialGeometry.Analysis.Convex.normalCone C (γ a)) :
    inner ℝ ν (f a (γ a)) ≤ 0 := by
  have hmax : IsMaxOn (fun y : V => inner ℝ ν y) C (γ a) := by
    intro y hy
    have h := hnormal.2 y hy
    rwa [inner_sub_right, sub_nonpos] at h
  have hderiv : HasFDerivAt (fun y : V => inner ℝ ν y) (innerSL ℝ ν) (γ a) :=
    (innerSL ℝ ν).hasFDerivAt
  exact hmax.localize.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt
    (IsIntegralCurveOn.mem_posTangentConeAt_of_mapsTo_Icc hγ hab hC)

end DifferentialGeometry.Analysis.ODE
