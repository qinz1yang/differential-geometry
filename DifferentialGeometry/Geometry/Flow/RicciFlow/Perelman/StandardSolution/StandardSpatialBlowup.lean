import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.HighCurvatureModels
import DifferentialGeometry.Analysis.ODE.QuadraticCrossing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ScalarFamilyRegularity

noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
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

theorem not_standard_scalar_blowup_at_spatial_infinity_of_tendsto
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ (S n).val.domain ∧ t n < 1) (htend : Tendsto t atTop (𝓝 T))
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
  have hbuffer : T < T + 1 / (8 * C * A) := by
    have hh : 0 < 1 / (8 * C * A) := by positivity
    linarith
  have hupper : ∀ᶠ n in atTop, t (ψ n) < T + 1 / (8 * C * A) :=
    (htend.comp hψ.tendsto_atTop).eventually (Iio_mem_nhds hbuffer)
  obtain ⟨n, hnsmall, hnlarge, hntime, hnupper⟩ := (hsmall.and (hlarge.and (htime.and hupper))).exists
  let U := (S (ψ n)).val
  let y := x (ψ n)
  have hdom : Icc τ (t (ψ n)) ⊆ U.domain := by
    intro v hv
    apply (mem_lifetimeInterval_carrier U.lifetime U.lifetime_pos v).mpr
    refine ⟨hτ.le.trans hv.1, ?_⟩
    exact (ENNReal.ofReal_le_ofReal hv.2).trans_lt
      ((mem_lifetimeInterval_carrier U.lifetime U.lifetime_pos (t (ψ n))).mp (ht (ψ n)).1).2
  have hcross := scalar_crossing_bound U y hτ hntime.le hτhalf (ht (ψ n)).2 hA
    hdom hnsmall hnlarge (fun v hv htv hv1 hAv =>
      hderiv U y v hv htv hv1 (hQA.le.trans hAv.le))
  have htimeBound : C * (t (ψ n) - τ) ≤ 3 / (8 * A) := by
    have he : C * (1 / (8 * C * A)) = 1 / (8 * A) := by field_simp
    have hu := mul_le_mul_of_nonneg_left hnupper.le hC.le
    have hpos : 0 < 8 * A := by positivity
    have hfour : 1 / (4 * A) + 1 / (8 * A) = 3 / (8 * A) := by field_simp; ring
    rw [mul_add, he] at hu
    rw [← hfour]
    linarith
  have hinverse : A⁻¹ - (2 * A)⁻¹ = 1 / (2 * A) := by field_simp; ring
  rw [hinverse] at hcross
  have hgap : 3 / (8 * A) < 1 / (2 * A) := by
    apply (div_lt_div_iff₀ (by positivity : 0 < 8 * A) (by positivity : 0 < 2 * A)).mpr
    linarith
  exact (not_le_of_gt hgap) (hcross.trans htimeBound)


theorem not_standard_scalar_blowup_at_spatial_infinity
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Ico 0 T) (htend : Tendsto t atTop (𝓝 T))
    (hx : Tendsto (fun n => (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal)
      atTop atTop) :
    ¬ Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) atTop atTop := by
  apply not_standard_scalar_blowup_at_spatial_infinity_of_tendsto hT hT1 hTLife S x t ?_ htend hx
  intro n
  refine ⟨?_, (ht n).2.trans hT1⟩
  exact (mem_lifetimeInterval_carrier (S n).val.lifetime (S n).val.lifetime_pos (t n)).mpr
    ⟨(ht n).1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr (ht n).2).trans_le
      (hTLife.trans (uniformStandardLifetime_le_lifetime (S n)))⟩

theorem standard_uniform_exterior_scalar_bound
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime) :
    ∃ R K : ℝ, 0 < R ∧ 0 < K ∧ ∀ (S : StandardSolution) (t : ℝ),
      t ∈ Ico 0 T → ∀ x : E3, R ≤ ‖x‖ → metricScalarAt (S.val.metric t) x ≤ K := by
  classical
  by_contra hnot
  have hbad (n : ℕ) : ∃ (S : StandardSolution) (t : ℝ) (x : E3),
      t ∈ Ico 0 T ∧ (n : ℝ) + 1 ≤ ‖x‖ ∧ (n : ℝ) + 1 < metricScalarAt (S.val.metric t) x := by
    by_contra h
    apply hnot
    refine ⟨(n : ℝ) + 1, (n : ℝ) + 1, by positivity, by positivity, ?_⟩
    intro S t ht x hx
    exact le_of_not_gt fun hh => h ⟨S, t, x, ht, hx, hh⟩
  choose S t x ht hx hR using hbad
  obtain ⟨b, hb, φ, hφ, hbconv⟩ := isCompact_Icc.tendsto_subseq
    (fun n => ⟨(ht n).1, (ht n).2.le⟩ : ∀ n, t n ∈ Icc 0 T)
  have hblow : Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith).trans (hR n).le)
      tendsto_natCast_atTop_atTop
  have hblow' := hblow.comp hφ.tendsto_atTop
  have hescape : Tendsto (fun n =>
      (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) atTop atTop := by
    have hn : Tendsto (fun n => ‖x n‖) atTop atTop := tendsto_atTop_mono
      (fun n : ℕ => (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith).trans (hx n)) tendsto_natCast_atTop_atTop
    apply hn.congr'
    filter_upwards with n
    rw [(S n).val.initial, StandardCap.distance_zero]
  have hbpos : 0 < b := by
    by_contra h
    have hbzero : b = 0 := le_antisymm (le_of_not_gt h) hb.1
    subst b
    obtain ⟨α, hα, K, hK, hlife, hcurv⟩ := standard_uniform_initial_window
    have hsmall : ∀ᶠ n in atTop, t (φ n) < α :=
      hbconv.eventually (Iio_mem_nhds hα)
    have hlarge : ∀ᶠ n in atTop, 9 * K < metricScalarAt ((S (φ n)).val.metric (t (φ n))) (x (φ n)) :=
      hblow'.eventually (eventually_gt_atTop (9 * K))
    obtain ⟨n, hn, hnlarge⟩ := (hsmall.and hlarge).exists
    have hs := scalar_abs_le_rm ((S (φ n)).val.metric (t (φ n))) (x (φ n))
    change |metricScalarAt ((S (φ n)).val.metric (t (φ n))) (x (φ n))| ≤
      (Module.finrank ℝ E3 : ℝ) ^ 2 * Real.sqrt
        (normSq0S ((S (φ n)).val.metric (t (φ n))) (x (φ n)) 4
          (metricRm04 ((S (φ n)).val.metric (t (φ n))) (x (φ n)))) at hs
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hs
    have hc := hcurv (S (φ n)) (t (φ n)) ⟨(ht (φ n)).1, hn.le⟩ (x (φ n))
    have hlo := le_abs_self (metricScalarAt ((S (φ n)).val.metric (t (φ n))) (x (φ n)))
    nlinarith
  apply not_standard_scalar_blowup_at_spatial_infinity_of_tendsto hbpos (hb.2.trans_lt hT1)
    ((ENNReal.ofReal_le_ofReal hb.2).trans hTLife) (S ∘ φ) (x ∘ φ) (t ∘ φ) ?_ hbconv
    (hescape.comp hφ.tendsto_atTop) hblow'
  intro n
  refine ⟨?_, (ht (φ n)).2.trans hT1⟩
  apply (mem_lifetimeInterval_carrier (S (φ n)).val.lifetime (S (φ n)).val.lifetime_pos (t (φ n))).mpr
  exact ⟨(ht (φ n)).1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr (ht (φ n)).2).trans_le
    (hTLife.trans (uniformStandardLifetime_le_lifetime (S (φ n))))⟩

end DifferentialGeometry.PDE.RicciFlow
