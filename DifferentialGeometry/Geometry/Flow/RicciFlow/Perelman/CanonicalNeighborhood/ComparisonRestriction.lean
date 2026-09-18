import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.CovariantTwoTensor
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

def MetricComparisonOn.restrictTimeSingleton
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps) {t : ℝ} (ht : t ∈ times)
    (heps : 0 ≤ eps) : MetricComparisonOn h g F U {t} order eps where
  pullback := C.pullback
  pullback_eq := C.pullback_eq
  jet := fun b s => if b = 0 then C.jet 0 s else 0
  jet_zero := by simpa using C.jet_zero
  jet_succ := by
    intro b s hs y _hy v
    have hst : s = t := hs
    subst s
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    change 0 = derivWithin _ {t} t
    symm
    apply derivWithin_zero_of_not_accPt
    rw [accPt_iff_clusterPt, inf_principal]
    simp [ClusterPt]
  equivalence := by
    intro s hs y hy v
    have hst : s = t := hs
    subst s
    exact C.equivalence t ht y hy v
  close := by
    intro a b hab s hs y hy
    have hst : s = t := hs
    subst s
    split_ifs with hb
    · subst b
      exact C.close a 0 hab t ht y hy
    · have hz : tensor02CovDerivNormWith (I := I) a 0 (h t) (h t) y = 0 := by
        rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
          covDerivOfField_zero_tensor]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
          MetricFiberData.inner, map_zero, Real.sqrt_zero]
      exact hz.le.trans heps

def MetricComparisonOn.freezeTime
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U times order eps) {t : ℝ} (ht : t ∈ times)
    (heps : 0 ≤ eps) (T : Set ℝ) :
    MetricComparisonOn (fun _ => h t) (fun _ => g t) F U T order eps where
  pullback := fun _ => C.pullback t
  pullback_eq := fun _ => C.pullback_eq t
  jet := fun b _ => if b = 0 then C.jet 0 t else 0
  jet_zero := by
    intro s y v
    exact C.jet_zero t y v
  jet_succ := by
    intro b s _ y _ v
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    simp
  equivalence := fun _ _ => C.equivalence t ht
  close := by
    intro a b hab _ _ y hy
    split_ifs with hb
    · subst b
      exact C.close a 0 hab t ht y hy
    · have hz : tensor02CovDerivNormWith (I := I) a 0 (h t) (h t) y = 0 := by
        rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
          covDerivOfField_zero_tensor]
        simp only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
          MetricFiberData.inner, map_zero, Real.sqrt_zero]
      exact hz.le.trans heps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
