import DifferentialGeometry.Analysis.Integration.EntropyLp
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Integration

variable {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α}


theorem unifIntegrable_one_of_eLpNorm_bdd {f : ι → α → ℝ} {p : ℝ}
    (hp : 1 < p) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hbound : ∀ i, eLpNorm (f i) (ENNReal.ofReal p) μ ≤ C) :
    UnifIntegrable f 1 μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ha : 0 < 1 - 1 / p := sub_pos.mpr ((div_lt_one hp0).2 hp)
  intro ε hε
  have hlim : Tendsto (fun d : ℝ => C * (ENNReal.ofReal d) ^ (1 - 1 / p))
      (𝓝 0) (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC ha).comp
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0)
  have hsmall : {d : ℝ | C * (ENNReal.ofReal d) ^ (1 - 1 / p) < ENNReal.ofReal ε} ∈ 𝓝 0 :=
    hlim.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.1 hsmall
  have hdsmall : C * (ENNReal.ofReal (d / 2)) ^ (1 - 1 / p) ≤ ENNReal.ofReal ε := by
    apply (hball (show d / 2 ∈ Metric.ball (0 : ℝ) d by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg (half_pos hd).le]
      exact half_lt_self hd)).le
  refine ⟨d / 2, half_pos hd, fun i s hs hμs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  calc
    eLpNorm (f i) 1 (μ.restrict s) ≤ eLpNorm (f i) (ENNReal.ofReal p) (μ.restrict s) *
        μ s ^ (1 - 1 / p) := by
      simpa only [ENNReal.toReal_one, one_div_one, ENNReal.toReal_ofReal hp0.le,
        Measure.restrict_apply MeasurableSet.univ, univ_inter] using
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpE (hf i).restrict
    _ ≤ C * μ s ^ (1 - 1 / p) :=
      mul_le_mul_left ((eLpNorm_restrict_le _ _ _ _).trans (hbound i)) _
    _ ≤ C * (ENNReal.ofReal (d / 2)) ^ (1 - 1 / p) :=
      mul_le_mul_right (ENNReal.rpow_le_rpow hμs ha.le) C
    _ ≤ ENNReal.ofReal ε := hdsmall


theorem tendsto_integral_sq_mul_log_sq_of_eLpNorm_bdd [IsFiniteMeasure μ]
    {q : ℝ} (hq : 2 < q) {f : ℕ → α → ℝ} {u : α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hu : MemLp u (ENNReal.ofReal q) μ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hbound : ∀ n, eLpNorm (f n) (ENNReal.ofReal q) μ ≤ C)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (u x))) :
    Tendsto (fun n => ∫ x, f n x ^ 2 * Real.log (f n x ^ 2) ∂μ) atTop
      (𝓝 (∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂μ)) := by
  let a : ℝ := (q + 2) / 2
  have ha2 : 2 < a := by dsimp only [a]; linarith
  have haq : a < q := by dsimp only [a]; linarith
  have ha0 : 0 < a := by linarith
  let p : ℝ := q / a
  have hp : 1 < p := (one_lt_div ha0).2 haq
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpa : ENNReal.ofReal p * ENNReal.ofReal a = ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_mul hp0.le]
    congr 1
    exact div_mul_cancel₀ q ha0.ne'
  let D : ℝ := (a / 2 - 1)⁻¹
  have hD : 0 < D := inv_pos.mpr (by linarith)
  let F (n : ℕ) (x : α) : ℝ := f n x ^ 2 * Real.log (f n x ^ 2)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable ((hf n).pow 2)
  have hpow (n : ℕ) : AEStronglyMeasurable (fun x => ‖f n x‖ ^ a) μ :=
    (Real.continuous_rpow_const ha0.le).comp_aestronglyMeasurable (hf n).norm
  let B : ℝ≥0∞ := eLpNorm (fun _ : α => (1 : ℝ)) (ENNReal.ofReal p) μ + ENNReal.ofReal D * C ^ a
  have hB : B ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    exact ⟨(memLp_const (1 : ℝ)).eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg ha0.le hC)⟩
  have hFbound (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) μ ≤ B := by
    have hdom : eLpNorm (F n) (ENNReal.ofReal p) μ ≤
        eLpNorm (fun x => 1 + D * ‖f n x‖ ^ a) (ENNReal.ofReal p) μ := by
      apply eLpNorm_mono_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + D * ‖f n x‖ ^ a)]
      simpa only [F, D, div_eq_mul_inv, mul_comm] using abs_sq_mul_log_sq_le ha2 (f n x)
    have hmul : eLpNorm (fun x => D * ‖f n x‖ ^ a) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal D * C ^ a := by
      calc
        _ ≤ ‖D‖ₑ * eLpNorm (fun x => ‖f n x‖ ^ a) (ENNReal.ofReal p) μ := by
          change eLpNorm (D • fun x => ‖f n x‖ ^ a) (ENNReal.ofReal p) μ ≤ _
          exact eLpNorm_const_smul_le
        _ = ENNReal.ofReal D * eLpNorm (f n) (ENNReal.ofReal q) μ ^ a := by
          rw [Real.enorm_eq_ofReal hD.le, eLpNorm_norm_rpow _ ha0, hpa]
        _ ≤ ENNReal.ofReal D * C ^ a := by gcongr; exact hbound n
    apply hdom.trans
    calc
      _ ≤ eLpNorm (fun _ : α => (1 : ℝ)) (ENNReal.ofReal p) μ +
          eLpNorm (fun x => D * ‖f n x‖ ^ a) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le aestronglyMeasurable_const ((hpow n).const_mul D)
          (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le)
      _ ≤ B := add_le_add_right hmul _
  have hui : UnifIntegrable F 1 μ := unifIntegrable_one_of_eLpNorm_bdd hp hF hB hFbound
  have huF : Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) μ :=
    integrable_sq_mul_log_sq_of_memLp hq hu
  have hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop
      (𝓝 (u x ^ 2 * Real.log (u x ^ 2))) := by
    filter_upwards [hpoint] with x hx
    exact Real.continuous_mul_log.continuousAt.tendsto.comp (hx.pow 2)
  have hL1 := tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num)
    hF (memLp_one_iff_integrable.mpr huF) hui hFlim
  apply tendsto_integral_of_L1' _ huF.aestronglyMeasurable _ hL1
  apply Eventually.of_forall
  intro n
  exact (show MemLp (F n) (ENNReal.ofReal p) μ from
    ⟨hF n, (hFbound n).trans_lt hB.lt_top⟩).integrable
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le)

end DifferentialGeometry.Analysis.Integration
