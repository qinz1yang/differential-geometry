import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter

theorem exists_forall_rescalePinchingFunction_le_of_tendsto {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : ℕ → ℝ} (hQ : Tendsto Q atTop atTop)
    (B δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ B → rescalePinchingFunction (Q n) Phi u ≤ δ := by
  obtain ⟨Q0, hQ0, hle⟩ := exists_forall_rescalePinchingFunction_le hPhi (B := max B 0) hδ
  filter_upwards [hQ.eventually_ge_atTop Q0] with n hn u hu
  have hpos : 0 < Q n := hQ0.trans_le hn
  calc
    rescalePinchingFunction (Q n) Phi u ≤ rescalePinchingFunction (Q n) Phi (max B 0) :=
      mul_le_mul_of_nonneg_left
        (hPhi.mono (mul_le_mul_of_nonneg_left (hu.trans (le_max_left B 0)) hpos.le))
        (inv_nonneg.mpr hpos.le)
    _ ≤ δ := hle (Q n) hn (max B 0) ⟨le_max_right B 0, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff

theorem neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ)
    (u : TangentSpace I3 x) :
    -(2 * δ) * g.inner x u u ≤ metricRicciAt g x (vec2 u u) := by
  have hric := neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt g x h u
  have hdim : Module.finrank ℝ ThreeSpace = 3 := finrank_euclideanSpace_fin
  rw [hdim] at hric
  norm_num at hric
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
