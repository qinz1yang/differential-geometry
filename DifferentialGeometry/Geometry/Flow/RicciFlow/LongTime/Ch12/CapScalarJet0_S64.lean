import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapWindowZCMain_S64

/-!
# CH12-S64, group 2b: `R ≤ 9 |K|` from the order-0 jet `|Rm|² ≤ K²` (public re-proof of the private
`metricScalarAt_le_of_curvDerivNormSq_zero_le` of `TracedRegionAncientLimitTimeControl.lean`).
Used by K-cap step (iii): the kernel's jets at order 0 (`curvDerivNormSq 0 L.metric (φ w) ≤ q² B₂`,
`‖w‖ ≤ r`) give `R(z) ≤ 9 √B₂ q` on the flowed window image.
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

theorem metricScalarAt_le_nine_abs_of_curvDerivNormSq_zero_S64 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x : M) {K : ℝ}
    (h : curvDerivNormSq 0 g x ≤ K ^ 2) :
    metricScalarAt g x ≤ 9 * |K| := by
  have hsq : Real.sqrt (normSq0S g x 4 (metricRm04At g x)) ≤ |K| := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  have hrank0 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hrank : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := hrank0
  have h1 := (le_abs_self _).trans ((scalar_abs_le_rm g x).trans
    (mul_le_mul_of_nonneg_left hsq (by positivity)))
  rw [hrank] at h1
  norm_num at h1
  exact h1

end GC.LongTime.Ch12
