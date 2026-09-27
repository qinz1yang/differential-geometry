import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve

set_option autoImplicit false

open Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Riemannian.MFDerivAlongCurve

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

theorem chartGramOp_inner_deriv
    (G : MetricConnectionFamilyOn (I := I) (M := M) D)
    {gamma : ℝ → M} {r : ℝ} (p : M) (t : ℝ)
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r)
    (hsrc : gamma r ∈ (chartAt H p).source) :
    inner ℝ (chartGramOp G p (t, extChartAt I p (gamma r))
      (deriv ((extChartAt I p) ∘ gamma) r))
      (deriv ((extChartAt I p) ∘ gamma) r) =
      (G.metric t).inner (gamma r)
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ))
        ((mfderiv 𝓘(ℝ, ℝ) I gamma r : ℝ →L[ℝ] _) (1 : ℝ)) := by
  rw [chartGramOp_inner, (extChartAt I p).left_inv (by
    simpa only [extChartAt_source] using hsrc)]
  rw [raw_mfderiv_eq_symmL_apply_fderiv_of_mdifferentiableAt hgamma p hsrc]
  rfl

end DifferentialGeometry.Geometry.Curvature
