import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

omit [SigmaCompactSpace N] in
private theorem tensor_metric_cov_norm_le (g : SmoothRiemannianMetric I N) (a : ℕ) (y : N) :
    tensor02CovDerivNormWith a (metricTensorField g) g g y ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) := by
  change metricCovDerivNorm a g g y ≤ _
  cases a with
  | zero => exact le_of_eq (metricCovDerivNorm_self_zero g y)
  | succ a => rw [covNorm_self_succ]; exact Real.sqrt_nonneg _

def MetricComparisonOn.staticRescale
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {J : Set ℝ} {order : ℕ} {eps delta : ℝ}
    (C : MetricComparisonOn h g F U J order eps) {t : ℝ} (ht : t ∈ J)
    (q c : ℝ) (hq : 0 < q) (hc : 0 < c) (hdelta : 0 ≤ delta)
    (hweight : ∀ a ≤ order,
      Real.sqrt (q⁻¹ ^ (a + 2)) * c * eps +
        |c / q - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) ≤ delta) :
    MetricComparisonOn (fun _ => scaleMetric q hq (h t))
      (fun _ => scaleMetric c hc (g t)) F U {0} order delta := by
  let A := c • C.jet 0 t + (c / q - 1) • metricTensorField (scaleMetric q hq (h t))
  have hA (y : N) (v : Fin 2 → TangentSpace I y) :
      A y v = (c • C.pullback t) y v - (scaleMetric q hq (h t)).inner y (v 0) (v 1) := by
    simp only [A, ContMDiffSection.coe_add, ContMDiffSection.coe_smul, Pi.add_apply,
      Pi.smul_apply, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul,
      C.jet_zero, metricTensorField_apply, scaleMetric_inner]
    field_simp
    ring
  have hbound (a : ℕ) (ha : a ≤ order) (y : N) (hy : y ∈ U) :
      tensor02CovDerivNormWith a A (scaleMetric q hq (h t)) (scaleMetric q hq (h t)) y ≤
        delta := by
    have hmetric : tensor02CovDerivNormWith a
        ((c / q - 1) • metricTensorField (scaleMetric q hq (h t)))
        (scaleMetric q hq (h t)) (scaleMetric q hq (h t)) y ≤
        |c / q - 1| * Real.sqrt (Module.finrank ℝ E : ℝ) := by
      unfold tensor02CovDerivNormWith
      rw [tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_smul]
      simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
      rw [sqrt_normSq0S_smul, ← tensor02_cov_deriv_eq_cov_deriv_of_field]
      exact mul_le_mul_of_nonneg_left (tensor_metric_cov_norm_le _ a y) (abs_nonneg _)
    have herr : tensor02CovDerivNormWith a (c • C.jet 0 t)
        (scaleMetric q hq (h t)) (scaleMetric q hq (h t)) y ≤
        Real.sqrt (q⁻¹ ^ (a + 2)) * c * eps := by
      rw [tensor02CovDerivNormWith_smul_scaleMetric, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (C.close a 0 (by simpa using ha) t ht y hy)
        (mul_nonneg (Real.sqrt_nonneg _) hc.le)
    exact ((tensor02CovDerivNormWith_add_le a _ _ _ _ y).trans
      (add_le_add herr hmetric)).trans (hweight a ha)
  let jet := fun b (_s : ℝ) => if b = 0 then A else 0
  refine {
    pullback := fun _ => c • C.pullback t
    pullback_eq := ?_
    jet := jet
    jet_zero := fun _ y v => hA y v
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro s y hy v
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, C.pullback_eq t y hy v, scaleMetric_inner]
  · intro b s hs y _hy v
    obtain rfl := mem_singleton_iff.mp hs
    simp only [jet, if_neg (Nat.add_one_ne_zero b)]
    change 0 = derivWithin (fun _ => (if b = 0 then A else 0) y v) {0} 0
    simp only [derivWithin_fun_const, Pi.zero_apply]
  · intro s _hs y hy v
    exact quadratic_comparison_of_error_norm _ _ A y (hA y) (hbound 0 (by omega) y hy) v
  · intro a b hab s _hs y hy
    by_cases hb : b = 0
    · simpa only [jet, if_pos hb] using hbound a (by omega) y hy
    · simp only [jet, if_neg hb]
      rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
        covDerivOfField_zero_tensor]
      simpa only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero] using hdelta

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M]
  [ChartedSpace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace M]
  [IsManifold I3 ∞ M]

def MetricComparisonOn.staticRescaleOfOneLe
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {J : Set ℝ} {order : ℕ} {eps eta delta : ℝ}
    (C : MetricComparisonOn h g F U J order eps) {t : ℝ} (ht : t ∈ J)
    (q c : ℝ) (hq : 1 ≤ q) (hc : 0 < c) (heps : 0 ≤ eps)
    (hratio : |c / q - 1| ≤ eta)
    (hbudget : (1 + eta) * eps + eta * Real.sqrt (Module.finrank ℝ E : ℝ) ≤ delta) :
    MetricComparisonOn (fun _ => scaleMetric q (zero_lt_one.trans_le hq) (h t))
      (fun _ => scaleMetric c hc (g t)) F U {0} order delta := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have heta : 0 ≤ eta := (abs_nonneg _).trans hratio
  have hdelta : 0 ≤ delta := (add_nonneg
    (mul_nonneg (by linarith : 0 ≤ 1 + eta) heps)
    (mul_nonneg heta (Real.sqrt_nonneg _))).trans hbudget
  have hratio' : c / q ≤ 1 + eta := by linarith [(abs_le.mp hratio).2]
  refine C.staticRescale ht q c hqpos hc hdelta ?_
  intro a _ha
  have hinv : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hpower : Real.sqrt (q⁻¹ ^ a) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact pow_le_one₀ (inv_nonneg.mpr hqpos.le) hinv
  have hroot : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ q⁻¹ := by
    rw [pow_add, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hqpos.le) a),
      Real.sqrt_sq (inv_nonneg.mpr hqpos.le)]
    exact (mul_le_mul_of_nonneg_right hpower (inv_nonneg.mpr hqpos.le)).trans_eq
      (one_mul _)
  have hfactor : Real.sqrt (q⁻¹ ^ (a + 2)) * c ≤ 1 + eta := by
    calc
      _ ≤ q⁻¹ * c := mul_le_mul_of_nonneg_right hroot hc.le
      _ = c / q := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ _ := hratio'
  exact (add_le_add (mul_le_mul_of_nonneg_right hfactor heps)
    (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _))).trans hbudget

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
