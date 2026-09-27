import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

theorem exists_mul_le_integral_div_log_notMem_null
    {g : ℝ → ℝ} {r R : ℝ} {N : Set ℝ}
    (hr : 0 < r) (hrR : r < R) (hg : IntegrableOn g (Icc r R))
    (hN : (volume.restrict (Ioo r R)) N = 0) :
    ∃ ρ ∈ Ioo r R, ρ ∉ N ∧
      ρ * g ρ ≤ (∫ x in Icc r R, g x) / Real.log (R / r) := by
  let c := (∫ x in Icc r R, g x) / Real.log (R / r)
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Icc r R) :=
    (continuousOn_id.inv₀ (fun x hx => ne_of_gt (hr.trans_le hx.1))).integrableOn_compact
      isCompact_Icc
  have hg' : IntegrableOn g (Ioo r R) := hg.mono_set Ioo_subset_Icc_self
  have hinv' : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo r R) :=
    hinv.mono_set Ioo_subset_Icc_self
  have hdiff : IntegrableOn (fun x : ℝ => g x - c * x⁻¹) (Ioo r R) :=
    hg'.sub (hinv'.const_mul c)
  have hJ : (∫ x in Ioo r R, x⁻¹) = Real.log (R / r) := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hrR.le]
    exact integral_inv_of_pos hr (hr.trans hrR)
  have hzero : (∫ x in Ioo r R, g x - c * x⁻¹) = 0 := by
    rw [integral_sub hg' (hinv'.const_mul c), integral_const_mul, hJ,
      setIntegral_congr_set Ioo_ae_eq_Icc]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hlog.ne', sub_self]
  have hμ : volume.restrict (Ioo r R) ≠ 0 := by
    intro h
    have hvol : volume (Ioo r R) = 0 := Measure.restrict_eq_zero.mp h
    simp only [Real.volume_Ioo, ENNReal.ofReal_eq_zero,
      not_le.mpr (sub_pos.mpr hrR)] at hvol
  have hbad : (volume.restrict (Ioo r R)) (N ∪ (Ioo r R)ᶜ) = 0 := by
    apply measure_union_null
    · exact hN
    · simp
  obtain ⟨ρ, hρ, hle⟩ := exists_notMem_null_le_average hμ hdiff hbad
  have hρN : ρ ∉ N := fun h => hρ (Or.inl h)
  have hρs : ρ ∈ Ioo r R := by
    by_contra h
    exact hρ (Or.inr h)
  have hbound : g ρ - c * ρ⁻¹ ≤ 0 := by
    simpa only [average_eq, hzero, smul_zero] using hle
  refine ⟨ρ, hρs, hρN, ?_⟩
  have hρpos : 0 < ρ := hr.trans hρs.1
  calc
    ρ * g ρ ≤ ρ * (c * ρ⁻¹) := mul_le_mul_of_nonneg_left (sub_nonpos.mp hbound) hρpos.le
    _ = c := by field_simp

theorem exists_mul_le_div_log_notMem_null
    {g : ℝ → ℝ} {r R E : ℝ} {N : Set ℝ}
    (hr : 0 < r) (hrR : r < R) (hg : IntegrableOn g (Icc r R))
    (hN : (volume.restrict (Ioo r R)) N = 0) (hE : (∫ x in Icc r R, g x) ≤ E) :
    ∃ ρ ∈ Ioo r R, ρ ∉ N ∧ ρ * g ρ ≤ E / Real.log (R / r) := by
  obtain ⟨ρ, hρ, hρN, hbound⟩ := exists_mul_le_integral_div_log_notMem_null hr hrR hg hN
  refine ⟨ρ, hρ, hρN, hbound.trans ?_⟩
  exact div_le_div_of_nonneg_right hE
    (Real.log_pos ((one_lt_div hr).mpr hrR)).le

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis

private theorem integrable_toReal_liminf_of_integral_bound
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hpos : ∀ n, 0 ≤ᵐ[μ] f n)
    {B : ℝ} (hB : ∀ n, (∫ x, f n x ∂μ) ≤ B) :
    let F : X → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop
    Integrable (fun x => (F x).toReal) μ ∧
      (∫ x, (F x).toReal ∂μ) ≤ B ∧ (∀ᵐ x ∂μ, F x < ∞) := by
  let F : X → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop
  have hB0 : 0 ≤ B := (integral_nonneg_of_ae (hpos 0)).trans (hB 0)
  have hmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (f n x)) μ :=
    (hf n).aemeasurable.ennreal_ofReal
  have hm : AEMeasurable F μ := by
    simp only [F, liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup fun n => AEMeasurable.biInf (s := {i : ℕ | n ≤ i})
      (to_countable _) (fun i _ => hmeas i)
  have hb (n : ℕ) : (∫⁻ x, ENNReal.ofReal (f n x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (hpos n)]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have hfatou : (∫⁻ x, F x ∂μ) ≤ ENNReal.ofReal B :=
    (lintegral_liminf_le' hmeas).trans ((liminf_le_limsup).trans
      (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall hb)))
  have hfin : (∫⁻ x, F x ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou
  have hae := ae_lt_top' hm hfin
  refine ⟨integrable_toReal_of_lintegral_ne_top hm hfin, ?_, hae⟩
  rw [integral_toReal hm hae]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou).trans_eq
    (ENNReal.toReal_ofReal hB0)

theorem exists_radius_subseq_mul_le_div_log_of_integral_bound
    {f : ℕ → ℝ → ℝ} {r R B ε : ℝ} {P : ℝ → Prop}
    (hr : 0 < r) (hrR : r < R)
    (hf : ∀ n, IntegrableOn (f n) (Icc r R))
    (hpos : ∀ n, 0 ≤ᵐ[volume.restrict (Icc r R)] f n)
    (hB : ∀ n, (∫ x in Icc r R, f n x) ≤ B)
    (hP : ∀ᵐ x ∂volume.restrict (Icc r R), P x) (hε : 0 < ε) :
    ∃ ρ ∈ Ioo r R, P ρ ∧ ∃ σ : ℕ → ℕ,
      StrictMono σ ∧ ∀ n, ρ * f (σ n) ρ ≤ B / Real.log (R / r) + ε := by
  classical
  let F : ℝ → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop
  obtain ⟨hFi, hFB, hFfinite⟩ := integrable_toReal_liminf_of_integral_bound hf hpos hB
  let N : Set ℝ := {x | ¬ (P x ∧ F x < ∞)}
  have hN : (volume.restrict (Icc r R)) N = 0 := by
    apply ae_iff.mp
    exact hP.and hFfinite
  have hN' : (volume.restrict (Ioo r R)) N = 0 :=
    le_antisymm ((Measure.restrict_mono_set volume Ioo_subset_Icc_self N).trans_eq hN) bot_le
  obtain ⟨ρ, hρ, hρN, hbound⟩ := exists_mul_le_div_log_notMem_null hr hrR hFi hN' hFB
  have hp : P ρ ∧ F ρ < ∞ := by
    simpa only [N, mem_ofPred_eq, not_not] using hρN
  have hρ0 : 0 < ρ := hr.trans hρ.1
  have hδ : 0 < ε / ρ := div_pos hε hρ0
  have hlt : F ρ < ENNReal.ofReal ((F ρ).toReal + ε / ρ) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hδ.le, ENNReal.ofReal_toReal hp.2.ne]
    exact ENNReal.lt_add_right hp.2.ne (ENNReal.ofReal_pos.mpr hδ).ne'
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal (f n ρ) <
      ENNReal.ofReal ((F ρ).toReal + ε / ρ) :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
  obtain ⟨σ, hσ, hσbound⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨ρ, hρ, hp.1, σ, hσ, fun n => ?_⟩
  have hn : f (σ n) ρ ≤ (F ρ).toReal + ε / ρ :=
    le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp (hσbound n))
  calc
    ρ * f (σ n) ρ ≤ ρ * ((F ρ).toReal + ε / ρ) :=
      mul_le_mul_of_nonneg_left hn hρ0.le
    _ = ρ * (F ρ).toReal + ε := by field_simp
    _ ≤ B / Real.log (R / r) + ε := add_le_add hbound le_rfl

end DifferentialGeometry.Analysis

end
