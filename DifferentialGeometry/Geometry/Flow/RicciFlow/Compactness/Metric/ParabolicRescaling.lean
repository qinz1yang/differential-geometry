import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.TimeLipschitz
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open Perelman.CanonicalNeighborhood

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem scale_metric_deriv_norm
    (c : ℝ) (hc : 0 < c) (g R : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    metricDerivNorm m (scaleMetric c hc g) g R x =
      |c - 1| * metricCovDerivNorm m g R x := by
  have hdiff : metricDiffCovDerivAt m (scaleMetric c hc g) g R x =
      (c - 1) • metricCovDeriv g R m x := by
    simp only [metricDiffCovDerivAt, metricCovDeriv_scaleMetric_left,
      ContMDiffSection.coe_smul, Pi.smul_apply, sub_smul, one_smul]
  rw [metricDerivNorm, hdiff, sqrt_normSq0S_smul]
  rfl

theorem parabolicRescale_metricDerivNormSupOn_tendsto_zero
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (c : ℕ → ℝ) (hc : ∀ i, 0 < c i) (hctop : Tendsto c atTop (𝓝 1))
    (R : SmoothRiemannianMetric I M) (T : ℝ) (hT : 0 < T)
    (K : Set M) (hK : IsCompact K) (order : ℕ) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ i in atTop, ∀ s ∈ Icc (-T) 0,
      metricDerivNormSupOn K order (scaleMetric (c i) (hc i) (S.base.metric (s / c i)))
        (S.base.metric s) R < eps := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  classical
  obtain ⟨L, hL, hlip⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
    S hS (by linarith : -2 * T < 0) (by intro s hs; exact hs.2)
      (by intro s hs; exact hs.2) R hK order
  have hbounded (q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ x ∈ K, metricCovDerivNorm q (S.base.metric 0) R x ≤ B := by
    obtain ⟨B, hB⟩ := metricCovDerivNorm_bddOn hK q (S.base.metric 0) R
    exact ⟨max B 0, le_max_right _ _, fun x hx => (hB x hx).trans (le_max_left _ _)⟩
  choose B hB hbound using hbounded
  let A := (∑ q ∈ Finset.range (order + 1), B q) + L * (2 * T)
  have hA : 0 ≤ A := add_nonneg (Finset.sum_nonneg fun q _ => hB q) (by positivity)
  have hcov : ∀ q ≤ order, ∀ t ∈ Icc (-2 * T) 0, ∀ x ∈ K,
      metricCovDerivNorm q (S.base.metric t) R x ≤ A := by
    intro q hq t ht x hx
    have htime := hlip q hq t ht 0 ⟨by linarith, le_rfl⟩ x hx
    have habs : |t - 0| ≤ 2 * T := by rw [sub_zero, abs_of_nonpos ht.2]; linarith [ht.1]
    have hBsum : B q ≤ ∑ j ∈ Finset.range (order + 1), B j :=
      Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega))
    exact (covNorm_le_add q (S.base.metric t) (S.base.metric 0) R x).trans
      (add_le_add ((hbound q x hx).trans hBsum)
        (htime.trans (mul_le_mul_of_nonneg_left habs hL)))
  have herror : Tendsto (fun i => |c i - 1| * A + L * T * |(c i)⁻¹ - 1|)
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun i => (c i)⁻¹) atTop (𝓝 1) := by
      simpa only [inv_one] using hctop.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [sub_self, abs_zero, zero_mul, mul_zero, add_zero] using
      (((hctop.sub_const 1).abs.mul_const A).add (((hinv.sub_const 1).abs).const_mul (L * T)))
  have hhalf : ∀ᶠ i in atTop, (1 / 2 : ℝ) ≤ c i :=
    ((tendsto_order.1 hctop).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  intro eps heps
  filter_upwards [hhalf, herror.eventually (gt_mem_nhds heps)] with i hi herr
  intro s hs
  have ht : s / c i ∈ Icc (-2 * T) 0 := by
    refine ⟨(le_div_iff₀ (hc i)).mpr ?_, div_nonpos_of_nonpos_of_nonneg hs.2 (hc i).le⟩
    nlinarith [hs.1]
  have hs' : s ∈ Icc (-2 * T) 0 := ⟨by linarith [hs.1], hs.2⟩
  have hdelta : |s / c i - s| ≤ T * |(c i)⁻¹ - 1| := by
    have heq : s / c i - s = s * ((c i)⁻¹ - 1) := by rw [div_eq_mul_inv]; ring
    rw [heq, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos hs.2]
    linarith [hs.1]
  apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall K order _ _ R
    (|c i - 1| * A + L * T * |(c i)⁻¹ - 1|) (by positivity) ?_) herr
  intro q hq x hx
  have hh := metricDerivNorm_triangle q (scaleMetric (c i) (hc i) (S.base.metric (s / c i)))
    (S.base.metric (s / c i)) (S.base.metric s) R x
  rw [scale_metric_deriv_norm] at hh
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hcov q hq _ ht x hx) (abs_nonneg _))
    ((hlip q hq _ ht s hs' x hx).trans (by nlinarith [mul_le_mul_of_nonneg_left hdelta hL])))

end DifferentialGeometry.PDE.RicciFlow

end

end
