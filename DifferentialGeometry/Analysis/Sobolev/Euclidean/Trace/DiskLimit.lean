import DifferentialGeometry.Analysis.Sobolev.Euclidean.Trace.GreenLimit
import DifferentialGeometry.Analysis.Integration.Integral.UniformConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "diskRegion" => regionBetween (fun x : ℝ => -Real.sqrt (1 - x ^ 2))
  (fun x : ℝ => Real.sqrt (1 - x ^ 2)) (Ioo (-1 : ℝ) 1)
local notation "μ" => volume.restrict diskRegion

private theorem diskRegion_subset_square :
    diskRegion ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 := by
  intro p hp
  have hroot : Real.sqrt (1 - p.1 ^ 2) ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by nlinarith [sq_nonneg p.1]⟩
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩

private instance diskRegion_finiteMeasure : IsFiniteMeasure μ :=
  isFiniteMeasure_restrict.mpr
    ((measure_mono diskRegion_subset_square).trans_lt
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top).ne

private theorem memLp_diskRegion_of_continuous {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    MemLp g 2 μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    hg.continuousOn
  apply MemLp.of_bound hg.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_regionBetween (by fun_prop) (by fun_prop)
    measurableSet_Ioo)] with p hp
  exact hC p (diskRegion_subset_square hp)

private theorem memLp_fderiv_snd_diskRegion {K : ℝ≥0} {f : ℝ × ℝ → ℝ}
    (hf : LipschitzWith K f) : MemLp (fun p => fderiv ℝ f p (0, 1)) 2 μ := by
  apply MemLp.of_bound (measurable_fderiv_apply_const ℝ f (0, 1)).aestronglyMeasurable (K : ℝ)
  apply Eventually.of_forall
  intro p
  have h := (fderiv ℝ f p).le_opNorm (0, 1)
  have hn : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp
  rw [hn, mul_one] at h
  exact h.trans (norm_fderiv_le_of_lipschitz ℝ hf)

theorem integral_mul_weak_deriv_snd_add_unit_disk_eq_boundary_of_uniform_limit
    {K : ℕ → ℝ≥0} {f : ℕ → ℝ × ℝ → ℝ} (hf : ∀ n, LipschitzWith (K n) (f n))
    {v G : ℝ × ℝ → ℝ} (hv : MemLp v 2 μ) (hG : MemLp G 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun p => f n p - v p) 2 μ) atTop (𝓝 0))
    (hweak : ∀ z : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ
        ((memLp_fderiv_snd_diskRegion (hf n)).toLp (fun p => fderiv ℝ (f n) p (0, 1))) z)
        atTop (𝓝 (inner ℝ (hG.toLp G) z)))
    {ηa ηb : ℝ → ℝ}
    (haLim : TendstoUniformlyOn (fun n x => f n (x, -Real.sqrt (1 - x ^ 2))) ηa
      atTop (Icc (-1 : ℝ) 1))
    (hbLim : TendstoUniformlyOn (fun n x => f n (x, Real.sqrt (1 - x ^ 2))) ηb
      atTop (Icc (-1 : ℝ) 1))
    {L : ℝ≥0} {g : ℝ × ℝ → ℝ} (hg : LipschitzWith L g) :
    (∫ p in diskRegion, G p * g p + v p * fderiv ℝ g p (0, 1)) =
      ∫ x in Ioo (-1 : ℝ) 1,
        ηb x * g (x, Real.sqrt (1 - x ^ 2)) - ηa x * g (x, -Real.sqrt (1 - x ^ 2)) := by
  apply integral_mul_weak_deriv_snd_add_eq_boundary_of_tendsto hf
    (by fun_prop) (by fun_prop) measurableSet_Ioo
    (fun x _ => by linarith [Real.sqrt_nonneg (1 - x ^ 2)])
    (fun n => memLp_diskRegion_of_continuous (hf n).continuous)
    (fun n => memLp_fderiv_snd_diskRegion (hf n)) hv hG hlim hweak hg
    (memLp_diskRegion_of_continuous hg.continuous) (memLp_fderiv_snd_diskRegion hg)
  have hfa (n : ℕ) : Continuous (fun x : ℝ => f n (x, -Real.sqrt (1 - x ^ 2))) := by
    exact (hf n).continuous.comp (by fun_prop)
  have hfb (n : ℕ) : Continuous (fun x : ℝ => f n (x, Real.sqrt (1 - x ^ 2))) := by
    exact (hf n).continuous.comp (by fun_prop)
  have hga : Continuous (fun x : ℝ => g (x, -Real.sqrt (1 - x ^ 2))) := hg.continuous.comp (by fun_prop)
  have hgb : Continuous (fun x : ℝ => g (x, Real.sqrt (1 - x ^ 2))) := hg.continuous.comp (by fun_prop)
  have htop := tendsto_integral_mul_of_tendstoUniformlyOn_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (fun n => (hfb n).continuousOn) hgb.continuousOn hbLim
  have hbot := tendsto_integral_mul_of_tendstoUniformlyOn_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (fun n => (hfa n).continuousOn) hga.continuousOn haLim
  have hηa := haLim.continuousOn (Frequently.of_forall (fun n => (hfa n).continuousOn))
  have hηb := hbLim.continuousOn (Frequently.of_forall (fun n => (hfb n).continuousOn))
  have heq (n : ℕ) :
      (∫ x in Ioo (-1 : ℝ) 1, f n (x, Real.sqrt (1 - x ^ 2)) * g (x, Real.sqrt (1 - x ^ 2))) -
      (∫ x in Ioo (-1 : ℝ) 1, f n (x, -Real.sqrt (1 - x ^ 2)) * g (x, -Real.sqrt (1 - x ^ 2))) =
      ∫ x in Ioo (-1 : ℝ) 1,
        f n (x, Real.sqrt (1 - x ^ 2)) * g (x, Real.sqrt (1 - x ^ 2)) -
        f n (x, -Real.sqrt (1 - x ^ 2)) * g (x, -Real.sqrt (1 - x ^ 2)) := by
    exact (integral_sub
      (((hfb n).mul hgb).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (((hfa n).mul hga).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)).symm
  have heqLim :
      (∫ x in Ioo (-1 : ℝ) 1, ηb x * g (x, Real.sqrt (1 - x ^ 2))) -
      (∫ x in Ioo (-1 : ℝ) 1, ηa x * g (x, -Real.sqrt (1 - x ^ 2))) =
      ∫ x in Ioo (-1 : ℝ) 1,
        ηb x * g (x, Real.sqrt (1 - x ^ 2)) - ηa x * g (x, -Real.sqrt (1 - x ^ 2)) := by
    exact (integral_sub
      ((hηb.mul hgb.continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((hηa.mul hga.continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self)).symm
  simpa only [heq, heqLim] using htop.sub hbot

end DifferentialGeometry.Analysis
