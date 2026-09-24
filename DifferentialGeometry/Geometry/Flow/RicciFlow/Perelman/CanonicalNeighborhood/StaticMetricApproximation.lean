import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTransport
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

def MetricComparisonOn.ofMapMetricApproximation
    {K : Set N} {eps : ℝ} {order : ℕ} {F : N → M}
    {g : SmoothRiemannianMetric I3 N} {h : SmoothRiemannianMetric I3 M}
    (D : MapMetricApproximationOn (I := I3) K eps order F g h) (times : Set ℝ) :
    MetricComparisonOn (fun _ => g) (fun _ => h) F K times order eps := by
  let A := D.pullback - metricTensorField g
  have hbound (a : ℕ) (ha : a ≤ order) (y : N) (hy : y ∈ K) :
      tensor02CovDerivNormWith a A g g y ≤ eps := by
    cases a with
    | zero =>
        change metricTensorErrorNorm D.pullback g y ≤ eps
        exact D.c0_small y hy
    | succ a =>
        unfold tensor02CovDerivNormWith
        dsimp only [A]
        rw [tensor02CovDeriv_sub_metricTensorField]
        exact D.cov_deriv_small (a + 1) (by omega) ha y hy
  refine {
    pullback := fun _ => D.pullback
    pullback_eq := fun _ => D.pullback_apply
    jet := fun b _ => if b = 0 then A else 0
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro s y v
    change D.pullback y v - metricTensorField g y v = _
    rw [metricTensorField_apply]
  · intro b s _hs y _hy v
    simp only [if_neg (Nat.add_one_ne_zero b)]
    change 0 = derivWithin (fun _ => (if b = 0 then A else 0) y v) times s
    simp only [derivWithin_fun_const, Pi.zero_apply]
  · intro s _hs y hy v
    exact tensor_apply_bounds_of_metricTensorErrorNorm_le D.pullback g (D.c0_small y hy) v
  · intro a b hab s _hs y hy
    by_cases hb : b = 0
    · simpa only [if_pos hb] using hbound a (by omega) y hy
    · rw [if_neg hb, tensor02CovDerivNormWith,
        tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
      simpa only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero] using D.eps_pos.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
