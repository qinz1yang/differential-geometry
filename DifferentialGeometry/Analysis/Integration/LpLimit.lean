import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos


noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Integration

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ae_le_of_integral_rpow_le
    [IsFiniteMeasure μ]
    {f : X → ℝ} {p : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hp_pos : ∀ k, 0 < p k)
    (hp : Tendsto p atTop atTop)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_integrable : ∀ k, Integrable (fun x => f x ^ p k) μ)
    (hbound : ∀ k, (∫ x, f x ^ p k ∂μ) ≤ C ^ p k) :
    ∀ᵐ x ∂μ, f x ≤ C := by
  rw [ae_le_const_iff_forall_gt_measure_zero]
  intro c hc
  have hc_pos : 0 < c := hC.trans_lt hc
  have hratio_nonneg : 0 ≤ C / c := div_nonneg hC hc_pos.le
  have hratio_lt_one : C / c < 1 := (div_lt_one hc_pos).2 hc
  have hratio_tendsto :
      Tendsto (fun k => (C / c) ^ p k) atTop (nhds 0) :=
    (tendsto_rpow_atTop_of_base_lt_one (C / c)
      (by linarith) hratio_lt_one).comp hp
  have hmeasure_le : ∀ k, μ.real {x | c ≤ f x} ≤ (C / c) ^ p k := by
    intro k
    have hpk_nonneg : 0 ≤ p k := (hp_pos k).le
    have hc_rpow_pos : 0 < c ^ p k := Real.rpow_pos_of_pos hc_pos _
    have hmarkov :
        c ^ p k * μ.real {x | c ^ p k ≤ f x ^ p k} ≤
          ∫ x, f x ^ p k ∂μ := by
      exact mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (hf_nonneg x) _)
        (hf_integrable k) (c ^ p k)
    have hsubset : {x | c ≤ f x} ⊆ {x | c ^ p k ≤ f x ^ p k} := by
      intro x hx
      exact Real.rpow_le_rpow hc_pos.le hx hpk_nonneg
    have hmain :
        c ^ p k * μ.real {x | c ≤ f x} ≤ C ^ p k := by
      calc
        c ^ p k * μ.real {x | c ≤ f x} ≤
            c ^ p k * μ.real {x | c ^ p k ≤ f x ^ p k} := by
          exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hc_rpow_pos.le
        _ ≤ ∫ x, f x ^ p k ∂μ := hmarkov
        _ ≤ C ^ p k := hbound k
    have hdiv : μ.real {x | c ≤ f x} ≤ C ^ p k / c ^ p k := by
      rw [le_div_iff₀ hc_rpow_pos]
      simpa [mul_comm] using hmain
    rwa [← Real.div_rpow hC hc_pos.le] at hdiv
  have hmeasure_zero : μ.real {x | c ≤ f x} = 0 := by
    by_contra hne
    have hmeasure_pos : 0 < μ.real {x | c ≤ f x} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    rw [Metric.tendsto_atTop] at hratio_tendsto
    obtain ⟨k, hk⟩ := hratio_tendsto
      (μ.real {x | c ≤ f x} / 2) (by positivity)
    have hrpow_nonneg : 0 ≤ (C / c) ^ p k :=
      Real.rpow_nonneg hratio_nonneg _
    have hrpow_lt :
        (C / c) ^ p k < μ.real {x | c ≤ f x} / 2 := by
      have hdist := hk k le_rfl
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hrpow_nonneg] at hdist
    linarith [hmeasure_le k]
  exact (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hmeasure_zero

variable [TopologicalSpace X]

theorem le_of_ae_le_of_continuous
    [μ.IsOpenPosMeasure]
    {f : X → ℝ} {C : ℝ}
    (hf : Continuous f)
    (hbound : ∀ᵐ x ∂μ, f x ≤ C) :
    ∀ x, f x ≤ C := by
  have hmax_ae : (fun x => max (f x) C) =ᵐ[μ] fun _ => C := by
    filter_upwards [hbound] with x hx
    exact max_eq_right hx
  have hmax : (fun x => max (f x) C) = fun _ => C :=
    (Continuous.ae_eq_iff_eq μ (hf.max continuous_const) continuous_const).mp hmax_ae
  intro x
  have hx := congrFun hmax x
  exact (le_max_left (f x) C).trans_eq hx

theorem le_on_open_of_ae_le
    [μ.IsOpenPosMeasure]
    {U : Set X} {f : X → ℝ} {C : ℝ}
    (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hbound : ∀ᵐ x ∂μ.restrict U, f x ≤ C) :
    ∀ x ∈ U, f x ≤ C := by
  have hmax_ae : (fun x => max (f x) C) =ᵐ[μ.restrict U] fun _ => C := by
    filter_upwards [hbound] with x hx
    exact max_eq_right hx
  have hmax : Set.EqOn (fun x => max (f x) C) (fun _ => C) U :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hmax_ae hU
      (fun x hx => (hf x hx).max continuousWithinAt_const) continuousOn_const
  intro x hx
  exact (le_max_left (f x) C).trans_eq (hmax hx)

theorem le_of_integral_rpow_le
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : X → ℝ} {p : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hp_pos : ∀ k, 0 < p k)
    (hp : Tendsto p atTop atTop)
    (hf : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_integrable : ∀ k, Integrable (fun x => f x ^ p k) μ)
    (hbound : ∀ k, (∫ x, f x ^ p k ∂μ) ≤ C ^ p k) :
    ∀ x, f x ≤ C := by
  exact le_of_ae_le_of_continuous hf
    (ae_le_of_integral_rpow_le hC hp_pos hp hf_nonneg hf_integrable hbound)

theorem le_on_open_of_integral_rpow_le
    {U : Set X} [IsFiniteMeasure (μ.restrict U)] [μ.IsOpenPosMeasure]
    {f : X → ℝ} {p : ℕ → ℝ} {C : ℝ}
    (hU : IsOpen U)
    (hC : 0 ≤ C)
    (hp_pos : ∀ k, 0 < p k)
    (hp : Tendsto p atTop atTop)
    (hf : ContinuousOn f U)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_integrable : ∀ k, Integrable (fun x => f x ^ p k) (μ.restrict U))
    (hbound : ∀ k, (∫ x, f x ^ p k ∂μ.restrict U) ≤ C ^ p k) :
    ∀ x ∈ U, f x ≤ C := by
  exact le_on_open_of_ae_le hU hf
    (ae_le_of_integral_rpow_le hC hp_pos hp hf_nonneg hf_integrable hbound)

end DifferentialGeometry.Analysis.Integration

end
