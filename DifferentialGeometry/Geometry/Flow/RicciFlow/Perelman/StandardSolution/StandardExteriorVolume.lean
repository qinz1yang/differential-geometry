import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSpatialBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricComparison

noncomputable section
open Set Filter Manifold MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private local instance : MeasurableSpace E3 := borel E3
private local instance : BorelSpace E3 := ⟨rfl⟩

theorem standard_uniform_exterior_volume_comparison
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime) :
    ∃ R Λ : ℝ, 0 < R ∧ 0 < Λ ∧ ∀ (S : StandardSolution) (t : ℝ),
      t ∈ Ico 0 T → ∀ A : Set E3, MeasurableSet A → (∀ x ∈ A, R ≤ ‖x‖) →
        riemannianVolumeMeasure (𝓡 3) E3 StandardCap.metric A ≤
          ENNReal.ofReal Λ * riemannianVolumeMeasure (𝓡 3) E3 (S.val.metric t) A := by
  obtain ⟨R, K, hR, hK, hscalar⟩ := standard_uniform_exterior_scalar_bound hT hT1 hTLife
  let Λ := Real.sqrt ((Real.exp (1800 * K * T)) ^ 3)
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  refine ⟨R, Λ, hR, hΛ, ?_⟩
  intro S t ht A hA hAR
  have hdom : Icc 0 t ⊆ S.val.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos s).mpr
      ⟨hs.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr (hs.2.trans_lt ht.2)).trans_le
        (hTLife.trans (uniformStandardLifetime_le_lifetime S))⟩
  have hRic : ∀ s ∈ Icc 0 t, ∀ x ∈ A, ∀ v : TangentSpace (𝓡 3) x,
      |ricciTensor (S.val.metric s) x v v| ≤ (900 * K) * (S.val.metric s).inner x v v := by
    intro s hs x hx v
    have hsc := hscalar S s ⟨hs.1, hs.2.trans_lt ht.2⟩ x (hAR x hx)
    have hnonneg := S.val.one_le_scalar s (hdom hs) x
    have hrm : Real.sqrt (normSq0S (S.val.metric s) x 4 (metricRm04 (S.val.metric s) x)) ≤ 100 * K := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, by nlinarith [S.val.normSq_rm_le_scalar_sq s (hdom hs) x]⟩
    have hq := S.val.ricci_quadratic_bound (by positivity : 0 ≤ 100 * K) x hrm v
    change |ricciTensor (S.val.metric s) x v v| ≤ _ at hq
    exact hq.trans_eq (by ring)
  have hmetric := metricEquiv_Icc_on S.val.metric A
    (fun s hs x v w => (S.val.equation s (hdom hs) x v w).mono Icc_subset_Ici_self) hRic
  have hquad : ∀ x ∈ A, ∀ v : TangentSpace (𝓡 3) x,
      StandardCap.metric.inner x v v ≤ Real.exp (1800 * K * T) * (S.val.metric t).inner x v v := by
    intro x hx v
    have hlow := (hmetric t ⟨ht.1, le_rfl⟩ x hx v).1
    rw [S.val.initial] at hlow
    have hh := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (1800 * K * t)).le
    have he : Real.exp (1800 * K * t) * Real.exp (-(2 * (900 * K) * (t - 0))) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, he, one_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le (by positivity))) (metric_inner_self_nonneg _ _ _))
  have hμ := volumeMeasure_restrict_le (S.val.metric t) StandardCap.metric
    (Real.exp_pos (1800 * K * T)) hA hquad
  have hmeas := hμ univ
  simpa only [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul,
    finrank_euclideanSpace, Fintype.card_fin, Λ] using hmeas


theorem exists_standard_uniform_fixed_ball_volume_lower
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime) :
    ∃ (p : E3) (v : ℝ), 0 < v ∧ ∀ (S : StandardSolution) (t : ℝ),
      t ∈ Ico 0 T → ENNReal.ofReal v ≤
        riemannianVolumeMeasure (𝓡 3) E3 (S.val.metric t) (Metric.ball p 1) := by
  obtain ⟨R, Λ, hR, hΛ, hcomp⟩ := standard_uniform_exterior_volume_comparison hT hT1 hTLife
  let p : E3 := EuclideanSpace.single 0 (R + 2)
  have hpn : ‖p‖ = R + 2 := by
    simp only [p, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  have hball : ∀ x ∈ Metric.ball p 1, R ≤ ‖x‖ := by
    intro x hx
    have hd : dist x p < 1 := hx
    have hn := norm_le_norm_add_norm_sub x p
    rw [← dist_eq_norm] at hn
    rw [hpn] at hn
    linarith
  let μ := riemannianVolumeMeasure (𝓡 3) E3 StandardCap.metric
  let _ : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure _
  have hpos : 0 < μ (Metric.ball p 1) := Metric.isOpen_ball.measure_pos μ ⟨p, Metric.mem_ball_self zero_lt_one⟩
  obtain ⟨c, _, hc, hcμ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hcpos : 0 < c := ENNReal.ofReal_pos.mp hc
  refine ⟨p, c / Λ, div_pos hcpos hΛ, ?_⟩
  intro S t ht
  have hmul := hcμ.le.trans (hcomp S t ht (Metric.ball p 1) Metric.isOpen_ball.measurableSet hball)
  rw [ENNReal.ofReal_div_of_pos hΛ]
  exact (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hΛ).ne' ENNReal.ofReal_ne_top).mpr
    (by simpa only [mul_comm] using hmul)

end DifferentialGeometry.PDE.RicciFlow
