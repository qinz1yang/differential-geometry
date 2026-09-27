import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.Analysis.Integration

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}


theorem tendsto_eLpNorm_one_of_two [IsFiniteMeasure μ] {f : ℕ → α → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hlim : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (measure_ne_top μ Set.univ)
  have hlim' : Tendsto (fun n => eLpNorm (f n) 2 μ * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun _ => bot_le) (fun n => eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hf n))

private lemma integral_mul_eq_inner_toLp {u v : α → ℝ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ x, u x * v x ∂μ) = inner ℝ (hu.toLp u) (hv.toLp v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hux hvx
  rw [hux, hvx]
  change u x * v x = v x * u x
  exact mul_comm _ _


theorem tendsto_integral_mul_of_eLpNorm_two {f : ℕ → α → ℝ} {u v : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * v x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).2 hlim
  simpa only [← integral_mul_eq_inner_toLp] using
    hLp.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hv.toLp v))


theorem tendsto_integral_sq_of_eLpNorm_two {f : ℕ → α → ℝ} {u : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 (∫ x, u x ^ 2 ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).2 hlim
  simpa only [← integral_mul_eq_inner_toLp, ← pow_two] using hLp.inner (𝕜 := ℝ) hLp


theorem tendsto_integral_mul_of_eLpNorm_two_two
    {f g : ℕ → α → ℝ} {u v : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hflim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0))
    (hglim : Tendsto (fun n => eLpNorm (fun x => g n x - v x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x * g n x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  have hfLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).2 hflim
  have hgLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg v hv).2 hglim
  simpa only [← integral_mul_eq_inner_toLp] using hfLp.inner (𝕜 := ℝ) hgLp


theorem exists_eLpNorm_bound_of_tendsto_two {f : ℕ → α → ℝ} {u : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, eLpNorm (f n) 2 μ ≤ C := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).2 hlim
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hLp).exists_norm_le
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n => ?_⟩
  calc
    eLpNorm (f n) 2 μ = ENNReal.ofReal ‖(hf n).toLp (f n)‖ := by
      rw [Lp.norm_toLp, ENNReal.ofReal_toReal (hf n).eLpNorm_ne_top]
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC _ ⟨n, rfl⟩)


theorem tendsto_integral_weighted_sq_of_eLpNorm_two
    {f : ℕ → α → ℝ} {u R : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ) (hR : MemLp R ⊤ μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, R x * f n x ^ 2 ∂μ) atTop
      (𝓝 (∫ x, R x * u x ^ 2 ∂μ)) := by
  have hRlim : Tendsto (fun n => eLpNorm (fun x => R x * f n x - R x * u x) 2 μ)
      atTop (𝓝 0) := by
    have hboundlim : Tendsto (fun n => eLpNorm R ⊤ μ *
        eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hR.eLpNorm_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim (fun _ => bot_le)
    intro n
    have hm : (R • (f n - u) : α → ℝ) = fun x => R x * f n x - R x * u x := by
      funext x
      change R x * (f n x - u x) = R x * f n x - R x * u x
      ring
    have hd : (f n - u : α → ℝ) = fun x => f n x - u x := rfl
    have h := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 ((hf n).sub hu).aestronglyMeasurable R
    rw [hm, hd] at h
    exact h
  have hprod := tendsto_integral_mul_of_eLpNorm_two_two hf (fun n => (hf n).mul' hR)
    hu (hu.mul' hR) hlim hRlim
  have heq (v : α → ℝ) : (∫ x, v x * (R x * v x) ∂μ) = ∫ x, R x * v x ^ 2 ∂μ := by
    congr 1
    funext x
    ring
  simpa only [heq] using hprod

end DifferentialGeometry.Analysis.Integration
