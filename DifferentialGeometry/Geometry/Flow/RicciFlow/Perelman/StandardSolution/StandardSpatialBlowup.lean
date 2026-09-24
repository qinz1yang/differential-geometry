import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Analysis.ODE.QuadraticCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarFamilyRegularity

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem scalar_crossing_bound
    (U : PartialStandardSolution) (y : E3) {a b A C τ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hτ : τ ≤ a) (hb1 : b < 1) (hA : 0 < A)
    (hdom : Icc a b ⊆ U.domain)
    (hstart : metricScalarAt (U.metric a) y ≤ A)
    (hfinish : 2 * A ≤ metricScalarAt (U.metric b) y)
    (hderiv : ∀ v ∈ U.domain, τ ≤ v → v < 1 → A < metricScalarAt (U.metric v) y →
      |deriv (fun r => metricScalarAt (U.metric r) y) v| ≤ C * metricScalarAt (U.metric v) y ^ 2) :
    A⁻¹ - (2 * A)⁻¹ ≤ C * (b - a) := by
  have hcont : ContinuousOn (fun v => metricScalarAt (U.metric v) y) (Icc a b) :=
    fun v hv => (U.scalarTime hv hdom y).continuousWithinAt
  apply DifferentialGeometry.Analysis.ODE.inv_sub_inv_le_mul_sub_of_deriv_le_sq
    hab hA (by linarith : A < 2 * A) hcont hstart hfinish
  intro v hv hAv
  have hvdom := hdom ⟨hv.1.le, hv.2.le⟩
  have hregular : v ∈ (lifetimeInterval U.lifetime U.lifetime_pos).regular :=
    (mem_lifetimeInterval_regular U.lifetime U.lifetime_pos v).mpr
      ⟨ha.trans hv.1, ((mem_lifetimeInterval_carrier U.lifetime U.lifetime_pos v).mp hvdom).2⟩
  have hdiff : DifferentiableAt ℝ (fun r => metricScalarAt (U.metric r) y) v :=
    (U.scalarTime hvdom (fun _ hv => hv) y).differentiableAt
      ((lifetimeInterval U.lifetime U.lifetime_pos).regular_mem_nhds hregular)
  exact ⟨hdiff, (le_abs_self _).trans (hderiv v hvdom (hτ.trans hv.1.le) (hv.2.trans hb1) hAv)⟩

theorem not_standard_scalar_blowup_at_spatial_infinity
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Ico 0 T) (htend : Tendsto t atTop (𝓝 T))
    (hx : Tendsto (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal)
      atTop atTop) :
    ¬ Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) atTop atTop := by
  intro hblow
  obtain ⟨C, hC, hderivative⟩ := exists_standard_high_scalar_time_derivative_bound
  obtain ⟨Q₀, hQ₀, hderiv⟩ := hderivative (T / 2) (half_pos hT)
  let A := max Q₀ ((1 - T)⁻¹) + 1
  have hA : 0 < A := by dsimp [A]; linarith [le_max_left Q₀ ((1 - T)⁻¹)]
  have hQA : Q₀ < A := by dsimp [A]; linarith [le_max_left Q₀ ((1 - T)⁻¹)]
  have hRA : (1 - T)⁻¹ < A := by dsimp [A]; linarith [le_max_right Q₀ ((1 - T)⁻¹)]
  let d := min (T / 4) (1 / (4 * C * A))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  let τ := T - d
  have hτ : 0 < τ := by dsimp [τ, d]; linarith [min_le_left (T / 4) (1 / (4 * C * A))]
  have hτT : τ < T := by dsimp [τ]; linarith
  have hτhalf : T / 2 ≤ τ := by dsimp [τ, d]; linarith [min_le_left (T / 4) (1 / (4 * C * A))]
  have hbudget : C * (T - τ) ≤ 1 / (4 * A) := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (T / 4) (1 / (4 * C * A))) hC.le
    dsimp only [d, τ]
    have he : C * (1 / (4 * C * A)) = 1 / (4 * A) := by field_simp
    rw [he] at hm
    linarith
  have hτLife : ENNReal.ofReal τ < uniformStandardLifetime :=
    ((ENNReal.ofReal_lt_ofReal_iff hT).mpr hτT).trans_le hTLife
  obtain ⟨ψ, hψ, hfixed⟩ := exists_standard_scalar_cylinder_subsequence hτ (hτT.trans hT1)
    hτLife S x hx
  have hτbound : (1 - τ)⁻¹ < A := by
    have hinv : (1 - τ)⁻¹ ≤ (1 - T)⁻¹ := inv_anti₀ (sub_pos.mpr hT1) (by linarith)
    exact hinv.trans_lt hRA
  have hsmall : ∀ᶠ n in atTop,
      metricScalarAt ((S (ψ n)).val.metric τ) (x (ψ n)) ≤ A :=
    (hfixed.eventually (Iio_mem_nhds hτbound)).mono fun _ h => h.le
  have hlarge : ∀ᶠ n in atTop,
      2 * A ≤ metricScalarAt ((S (ψ n)).val.metric (t (ψ n))) (x (ψ n)) :=
    (hblow.comp hψ.tendsto_atTop).eventually_ge_atTop (2 * A)
  have htime : ∀ᶠ n in atTop, τ < t (ψ n) :=
    (htend.comp hψ.tendsto_atTop).eventually (Ioi_mem_nhds hτT)
  obtain ⟨n, hnsmall, hnlarge, hntime⟩ := (hsmall.and (hlarge.and htime)).exists
  let U := (S (ψ n)).val
  let y := x (ψ n)
  have hdom : Icc τ (t (ψ n)) ⊆ U.domain := by
    intro v hv
    apply (mem_lifetimeInterval_carrier U.lifetime U.lifetime_pos v).mpr
    refine ⟨hτ.le.trans hv.1, ?_⟩
    have hvT : v < T := hv.2.trans_lt (ht (ψ n)).2
    exact ((ENNReal.ofReal_lt_ofReal_iff hT).mpr hvT).trans_le
      (hTLife.trans (uniformStandardLifetime_le_lifetime (S (ψ n))))
  have hcross := scalar_crossing_bound U y hτ hntime.le hτhalf ((ht (ψ n)).2.trans hT1) hA
    hdom hnsmall hnlarge (fun v hv htv hv1 hAv =>
      hderiv U y v hv htv hv1 (hQA.le.trans hAv.le))
  have htimeBound : C * (t (ψ n) - τ) ≤ 1 / (4 * A) :=
    (mul_le_mul_of_nonneg_left (by linarith [(ht (ψ n)).2]) hC.le).trans hbudget
  have hinverse : A⁻¹ - (2 * A)⁻¹ = 1 / (2 * A) := by field_simp; ring
  rw [hinverse] at hcross
  have hgap : 1 / (4 * A) < 1 / (2 * A) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  exact (not_le_of_gt hgap) (hcross.trans htimeBound)

end DifferentialGeometry.PDE.RicciFlow
