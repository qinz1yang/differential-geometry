import DifferentialGeometry.Analysis.Sobolev.Interval.TraceCompactness
import DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private theorem norm_sub_sq_le_length_mul_integral_deriv_sq
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) :
    ‖f b - f a‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hd : MemLp (deriv f) 2 μ := MemLp.of_bound (aestronglyMeasurable_deriv f _) K
    (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf)
  have hac := hf.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have hnorm : ‖f b - f a‖ ≤ ∫ t, ‖deriv f t‖ ∂μ := by
    rw [← hac.integral_deriv_eq_sub_vector]
    calc
      _ ≤ ∫ t in uIoc a b, ‖deriv f t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ = ∫ t, ‖deriv f t‖ ∂μ := by
        rw [uIoc_of_le hab]
        exact integral_Icc_eq_integral_Ioc.symm
  have hholder : (∫ t, ‖deriv f t‖ ∂μ) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv f t‖ ^ 2 ∂μ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖deriv f t‖)
      (by simpa using (memLp_const (p := 2) (μ := μ) (1 : ℝ)))
      (by simpa using hd.norm)
    simpa only [norm_one, norm_norm, one_mul, one_pow, integral_const, Measure.real, μ,
      Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul, mul_one,
      Real.one_rpow, Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hnonneg : 0 ≤ ∫ t, ‖deriv f t‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    ‖f b - f a‖ ^ 2 ≤
        (Real.sqrt (b - a) * Real.sqrt (∫ t, ‖deriv f t‖ ^ 2 ∂μ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hholder) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hab), Real.sq_sqrt hnonneg]

theorem tendstoUniformlyOn_of_ae_tendsto_of_curve_energy_bound
    (γ : ℕ → ℝ → F) (v : ℝ → F)
    (hLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (γ n))
    {a b B : ℝ} (hab : a < b)
    (hbound : ∀ n, (∫ t in Icc a b, ‖deriv (γ n) t‖ ^ 2) ≤ B)
    (hv : ContinuousOn v (Icc a b))
    (hae : ∀ᵐ t ∂volume.restrict (Icc a b), Tendsto (fun n => γ n t) atTop (𝓝 (v t))) :
    TendstoUniformlyOn γ v atTop (Icc a b) := by
  have hordered (n : ℕ) (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      dist (γ n s) (γ n t) ≤ Real.sqrt (B * (t - s)) := by
    obtain ⟨K, hK⟩ := hLip n
    let : IsFiniteMeasure (volume.restrict (Icc a b)) :=
      isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
    have hint : IntegrableOn (fun t => ‖deriv (γ n) t‖ ^ 2) (Icc a b) :=
      (MemLp.of_bound (aestronglyMeasurable_deriv (γ n) _)
        K (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hK)).norm.integrable_sq
    have h := norm_sub_sq_le_length_mul_integral_deriv_sq hK hst
    have hmono : (∫ z in Icc s t, ‖deriv (γ n) z‖ ^ 2) ≤ B :=
      (setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall (Icc_subset_Icc hs.1 ht.2))).trans (hbound n)
    have hsq : dist (γ n s) (γ n t) ^ 2 ≤ B * (t - s) := by
      rw [dist_comm, dist_eq_norm]
      exact h.trans ((mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hst)).trans_eq
        (mul_comm _ _))
    have hsqrt := Real.sqrt_le_sqrt hsq
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg] using hsqrt
  apply MeasureTheory.tendstoUniformlyOn_Icc_of_ae_tendsto_of_sqrt_dist_bound (B := B) hab ?_ hv hae
  intro n s hs t ht
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] using hordered n s t hs ht hst
  · simpa only [dist_comm (γ n t) (γ n s), abs_of_nonneg (sub_nonneg.mpr hts)] using
      hordered n t s ht hs hts

end DifferentialGeometry.Analysis

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F]

theorem tendsto_integral_curve_gap_sq_of_uniform_convergence
    {u v : ℕ → ℝ → F} {f : ℝ → F}
    (hu : ∀ n, Continuous (u n)) (hv : ∀ n, Continuous (v n))
    (huf : TendstoUniformlyOn u f atTop (Icc (0 : ℝ) 1))
    (hvf : TendstoUniformlyOn v f atTop (Icc (0 : ℝ) 1)) :
    Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1, ‖u n t - v n t‖ ^ 2) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (integral_nonneg fun _ => sq_nonneg _)
  · intro ε hε
    have hδ : 0 < Real.sqrt ε / 3 := div_pos (Real.sqrt_pos.mpr hε) (by norm_num)
    have huε := Metric.tendstoUniformlyOn_iff.mp huf (Real.sqrt ε / 3) hδ
    have hvε := Metric.tendstoUniformlyOn_iff.mp hvf (Real.sqrt ε / 3) hδ
    filter_upwards [huε, hvε] with n hun hvn
    have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        ‖u n t - v n t‖ ^ 2 ≤ (2 * (Real.sqrt ε / 3)) ^ 2 := by
      have hdist : dist (u n t) (v n t) < 2 * (Real.sqrt ε / 3) := by
        have h := dist_triangle (u n t) (f t) (v n t)
        have h1 := hun t ht
        have h2 := hvn t ht
        rw [dist_comm (f t) (u n t)] at h1
        linarith
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [dist_eq_norm] using hdist.le) 2
    have hi : IntegrableOn (fun t => ‖u n t - v n t‖ ^ 2) (Icc (0 : ℝ) 1) :=
      (((hu n).sub (hv n)).norm.pow 2).integrableOn_Icc
    have hm := setIntegral_mono_on hi
      (integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)) measurableSet_Icc hb
    have hbound : (∫ t in Icc (0 : ℝ) 1, ‖u n t - v n t‖ ^ 2) ≤
        (2 * (Real.sqrt ε / 3)) ^ 2 := by
      simpa only [setIntegral_const, Measure.real, Real.volume_Icc, sub_zero,
        ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using hm
    exact hbound.trans_lt (by nlinarith [Real.sq_sqrt hε.le])

end DifferentialGeometry.Analysis

end

end
