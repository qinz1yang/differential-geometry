import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionCurvatureFibreIdentities
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionInsertFibreIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMixedFibreIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionRiemannFibreIdentity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorr0Split
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Operator-product refolds of the zeroth-order DeTurck correction

The fibre-defined `VB`, mixed, and curvature pieces agree with the canonical
operator-field compositions used for low-regularity product estimates.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The fibre-defined insertion correction is its canonical symmetric
endomorphism-insertion field. -/
theorem lc0Insert_eq_lc0InsertField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0Insert (I := I) (M := M) g₀ g₁ g_bg =
      lc0InsertField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  exact (lc0b_insert_fiber (I := I) (M := M) g₀ g₁ g_bg x D m).symm

/-- The fibre-defined vector--bilinear correction is its canonical nested
operator-field composition. -/
theorem lc0VB_eq_lc0VBField (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0VB (I := I) (M := M) g₀ g₁ =
      lc0VBField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorr0VBFib (I := I) g₀ g₁ x D = _
  exact (lc0b_vb_fiber (I := I) (M := M) g₀ g₁ x D).symm

omit [NeZero (Module.finrank ℝ E)] in
/-- The fibre-defined mixed connection correction is its canonical
operator-field composition. -/
theorem lc0AMix_eq_lc0AMixField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lc0AMix (I := I) (M := M) g₀ g₁ g_bg =
      lc0AMixField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorr0AMixFib (I := I) g₀ g₁ g_bg x D = _
  exact (lc0b_amix_fiber (I := I) (M := M) g₀ g₁ g_bg x D).symm

omit [NeZero (Module.finrank ℝ E)] in
/-- The fibre-defined curvature correction is its canonical fixed-passenger
operator-field composition. -/
theorem lc0Riem_eq_lc0RiemField (g₀ g₁ : SmoothRiemannianMetric I M) :
    lc0Riem (I := I) (M := M) g₀ g₁ =
      lc0RiemField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change TensorRSSpace.ofCLM (lieCorr0RiemFib (I := I) g₀ g₁ x) D = _
  exact (lc0b_riem_fiber (I := I) (M := M) g₀ g₁ x D).symm

end DifferentialGeometry.Analysis.Spectral

end
