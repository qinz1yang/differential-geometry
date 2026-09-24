import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarHarnack
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardParabolicNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates

noncomputable section
open Set
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem PartialStandardSolution.sqrt_rm_le_scalar
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain) (x : E3) :
    Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤
      100 * metricScalarAt (S.metric t) x := by
  have hR := S.one_le_scalar t ht x
  apply (Real.sqrt_le_iff).2
  refine ⟨by linarith, ?_⟩
  simpa only [mul_pow] using S.normSq_rm_le_scalar_sq t ht x

private theorem PartialStandardSolution.sqrt_rm_le_sqrt_rm_of_half_time_le_pos
    (S : PartialStandardSolution) {s t : ℝ}
    (htpos : 0 < t) (ht : t ∈ S.domain) (hst : s ≤ t) (hs : t / 2 ≤ s) (x : E3) :
    Real.sqrt (normSq0S (S.metric s) x 4 (metricRm04 (S.metric s) x)) ≤
      1800 * Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) := by
  have hspos : 0 < s := (half_pos htpos).trans_le hs
  have hstime : s ∈ S.domain := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
    ⟨hspos.le, (ENNReal.ofReal_le_ofReal hst).trans_lt
      ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).2⟩
  have harnack := S.scalar_time_mul_le hspos.le hst ht x
  have hRs := S.one_le_scalar s hstime x
  have hRt := S.one_le_scalar t ht x
  have hscalar : metricScalarAt (S.metric s) x ≤ 2 * metricScalarAt (S.metric t) x := by
    have hmul := mul_le_mul_of_nonneg_right hs (by linarith : 0 ≤ metricScalarAt (S.metric s) x)
    nlinarith
  have hnorm := scalar_abs_le_rm (S.metric t) x
  have hd : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ E3 = 3
    exact finrank_euclideanSpace_fin
  norm_num only [hd] at hnorm
  change |metricScalarAt (S.metric t) x| ≤ 9 * Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) at hnorm
  have hcurv := S.sqrt_rm_le_scalar s hstime x
  nlinarith [le_abs_self (metricScalarAt (S.metric t) x)]


theorem PartialStandardSolution.sqrt_rm_le_sqrt_rm_of_half_time_le
    (S : PartialStandardSolution) {s t : ℝ}
    (ht : t ∈ S.domain) (hst : s ≤ t) (hs : t / 2 ≤ s) (x : E3) :
    Real.sqrt (normSq0S (S.metric s) x 4 (metricRm04 (S.metric s) x)) ≤
      1800 * Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) := by
  have ht0 := ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).1
  rcases ht0.eq_or_lt with rfl | htp
  · have hs0 : s = 0 := by linarith
    rw [hs0]
    nlinarith [Real.sqrt_nonneg (normSq0S (S.metric 0) x 4 (metricRm04 (S.metric 0) x))]
  · exact S.sqrt_rm_le_sqrt_rm_of_half_time_le_pos htp ht hst hs x

private theorem shrink_volume_noncollapsed
    (S : PartialStandardSolution)
    (time : (lifetimeInterval S.lifetime S.lifetime_pos).FlowTime)
    (B : FlowMetricBall S.toSolutionOn time) {q κ : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hB : (B.shrink q hq).IsKappaNoncollapsed κ) :
    B.IsKappaNoncollapsed (κ * q ^ 3) := by
  refine ⟨mul_pos hB.1 (pow_pos hq _), ?_⟩
  have hvol := FlowMetricBall.volume_mono (FlowMetricBall.shrink_nested B hq hq1)
  have hn : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  change ENNReal.ofReal (κ * q ^ 3) * ENNReal.ofReal B.radius ^ Module.finrank ℝ E3 ≤ _
  rw [hn]
  have hsmall := hB.2
  change ENNReal.ofReal κ * ENNReal.ofReal (q * B.radius) ^ Module.finrank ℝ E3 ≤ _ at hsmall
  rw [hn, ENNReal.ofReal_mul hq.le, mul_pow] at hsmall
  rw [ENNReal.ofReal_mul hB.1.le, ENNReal.ofReal_pow hq.le, mul_assoc]
  exact hsmall.trans hvol

theorem PartialStandardSolution.spatially_noncollapsed_of_radius_sq_le_half_time
    (S : PartialStandardSolution)
    (time : (lifetimeInterval S.lifetime S.lifetime_pos).FlowTime)
    (htone : (time : ℝ) < 1)
    (B : FlowMetricBall S.toSolutionOn time)
    (hdepth : (B.radius / 100) ^ 2 ≤ (time : ℝ) / 2) :
    B.IsSpatiallyKappaNoncollapsed (standardParabolicNoncollapseCoeff / 1000000) := by
  intro hspatial
  have htpos : 0 < (time : ℝ) := by
    have hp : 0 < (B.radius / 100) ^ 2 := sq_pos_of_pos (div_pos B.radius_pos (by norm_num))
    linarith
  let small := B.shrink (1 / 100 : ℝ) (by norm_num)
  have hsmallRadius : small.radius = B.radius / 100 := by
    dsimp only [small, FlowMetricBall.shrink]
    ring
  have hsmall_le : small.radius ≤ 1 := by
    rw [hsmallRadius]
    nlinarith [sq_nonneg (B.radius / 100 - 1)]
  have hdom : Icc ((time : ℝ) - small.radius ^ 2) (time : ℝ) ⊆ S.domain := by
    intro s hs
    exact (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨by rw [hsmallRadius] at hs; linarith [hs.1],
        (ENNReal.ofReal_le_ofReal hs.2).trans_lt
          ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos (time : ℝ)).mp time.property).2⟩
  have hRm : ∀ s ∈ Icc ((time : ℝ) - small.radius ^ 2) (time : ℝ), ∀ x ∈ small.set,
      Real.sqrt (FlowMetricBall.rmNormSq S.toSolutionOn s x) ≤ (small.radius ^ 2)⁻¹ := by
    intro s hs x hx
    have hxB : x ∈ B.set := FlowMetricBall.shrink_nested B (by norm_num : (0 : ℝ) < 1 / 100)
      (by norm_num : (1 / 100 : ℝ) ≤ 1) hx
    have hterm := hspatial x hxB
    have htermSqrt : Real.sqrt (FlowMetricBall.rmNormSq S.toSolutionOn (time : ℝ) x) ≤
        (B.radius ^ 2)⁻¹ := by
      apply (Real.sqrt_le_iff).2
      refine ⟨by positivity, ?_⟩
      have hbr : 0 < B.radius ^ 4 := pow_pos B.radius_pos _
      have hh : FlowMetricBall.rmNormSq S.toSolutionOn (time : ℝ) x ≤ 1 / B.radius ^ 4 :=
        (le_div_iff₀ hbr).mpr (by simpa only [mul_comm] using hterm)
      simpa only [one_div, ← pow_mul, inv_pow] using hh
    have hhalf : (time : ℝ) / 2 ≤ s := by rw [hsmallRadius] at hs; linarith [hs.1]
    have hback := S.sqrt_rm_le_sqrt_rm_of_half_time_le time.property hs.2 hhalf x
    change Real.sqrt (FlowMetricBall.rmNormSq S.toSolutionOn s x) ≤
      1800 * Real.sqrt (FlowMetricBall.rmNormSq S.toSolutionOn (time : ℝ) x) at hback
    calc
      _ ≤ 1800 * (B.radius ^ 2)⁻¹ := hback.trans (mul_le_mul_of_nonneg_left htermSqrt (by norm_num))
      _ ≤ (small.radius ^ 2)⁻¹ := by
        rw [hsmallRadius, div_pow, inv_div]
        norm_num
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr (sq_nonneg B.radius))
  have hsmall := standard_uniform_parabolic_noncollapse.2.2 S time htone small hsmall_le hdom hRm
  have hfull := shrink_volume_noncollapsed S time B (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num : (1 / 100 : ℝ) ≤ 1) hsmall
  convert hfull using 1
  norm_num
  ring


theorem PartialStandardSolution.spatially_noncollapsed_of_time_ge
    (S : PartialStandardSolution) {δ : ℝ}
    (time : (lifetimeInterval S.lifetime S.lifetime_pos).FlowTime)
    (hδt : δ ≤ (time : ℝ)) (htone : (time : ℝ) < 1)
    (B : FlowMetricBall S.toSolutionOn time)
    (hr : B.radius ≤ Real.sqrt (5000 * δ)) :
    B.IsSpatiallyKappaNoncollapsed (standardParabolicNoncollapseCoeff / 1000000) := by
  have hδ : 0 < δ := by
    have hp := Real.sqrt_pos.mp (B.radius_pos.trans_le hr)
    linarith
  have hsq : B.radius ^ 2 ≤ 5000 * δ := by
    have h := sq_le_sq₀ B.radius_pos.le (Real.sqrt_nonneg (5000 * δ)) |>.2 hr
    rwa [Real.sq_sqrt (by positivity)] at h
  apply S.spatially_noncollapsed_of_radius_sq_le_half_time time
    htone B
  rw [div_pow]
  norm_num
  nlinarith


end DifferentialGeometry.PDE.RicciFlow
