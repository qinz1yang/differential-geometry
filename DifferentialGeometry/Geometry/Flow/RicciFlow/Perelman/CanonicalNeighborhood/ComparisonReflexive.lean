import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

def metricComparisonOnSelf (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (id : M → M) U times order eps where
  pullback s := metricTensorField (I := I3) (g s)
  pullback_eq := by
    intro s y hy v
    rw [metricTensorField_apply, mfderiv_id]
    rfl
  jet _ _ := 0
  jet_zero := by
    intro s y v
    simp [metricTensorField_apply, sub_self]
  jet_succ := by
    intro b s hs y hy v
    simp
  equivalence := by
    intro s hs y hy v
    have hnn := inner_self_nonneg (g s) y v
    simp only [metricTensorField_apply]
    constructor <;> nlinarith
  close := by
    intro a b hab s hs y hy
    have hz : tensor02CovDerivNormWith (I := I3) a 0 (g s) (g s) y = 0 := by
      rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
        covDerivOfField_zero_tensor]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero]
    exact hz.le.trans heps.le

def metricComparisonOnRefl (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (PartialDiffeomorph.refl (I := I3) M : M → M) U times order eps := by
  have hid : (↑(PartialDiffeomorph.refl (I := I3) M) : M → M) = id := by
    funext x
    rfl
  rw [hid]
  exact metricComparisonOnSelf g U times order heps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
