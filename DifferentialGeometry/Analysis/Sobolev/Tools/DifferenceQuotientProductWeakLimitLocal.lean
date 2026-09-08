import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductWeakLimit
import DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotientProductCutoff

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "ν" => μ.prod (volume : Measure E)

private local instance : MeasurableSpace E := WithLp.measurableSpace 2 (Fin d → ℝ)

theorem exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω Ω' : Set E}, MeasurableSet Ω → IsOpen Ω' →
      (∀ x ∈ Ω', η x = 1) →
      ∀ {w : ℝ × E → ℝ}, MemLp w 2 (μ.prod (volume.restrict Ω)) →
      ∀ (k : Fin d) {C r : ℝ}, 0 < r → cthickening r (tsupport η) ⊆ Ω →
      (∀ h : ℝ, 0 < |h| → |h| ≤ r →
        (∫ t, ∫ x, (η x * diffQuot k h (fun y => w (t, y)) x)^2 ∂volume ∂μ) ≤ C) →
      ∃ v : Lp ℝ 2 (μ.prod (volume.restrict Ω')),
        ‖v‖ ≤ Real.sqrt C + L * (eLpNorm w 2 (μ.prod (volume.restrict Ω))).toReal ∧
        ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k (fun x => v (t, x)) (fun x => w (t, x)) Ω' := by
  obtain ⟨L, hL, hcutoff⟩ := exists_cutoff_toLp_spatial_diffQuot_uniform_bound_on (μ := μ) hη hηc
  refine ⟨L, hL, ?_⟩
  intro Ω Ω' hΩ hΩ' hηone w hw k C r hr hroom hbound
  obtain ⟨u, hu, hub⟩ := hcutoff hΩ hw k hroom hbound
  have hconst : 0 ≤ Real.sqrt C + L * (eLpNorm w 2 (μ.prod (volume.restrict Ω))).toReal :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hL ENNReal.toReal_nonneg)
  obtain ⟨v, hv, hvweak⟩ := exists_ae_hasWeakPartialDeriv_of_spatial_diffQuot_uniform_bound
    u k hconst hr hub
  have hm : μ.prod (volume.restrict Ω') ≤ ν := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hvlocal : MemLp v 2 (μ.prod (volume.restrict Ω')) := (Lp.memLp v).mono_measure hm
  let vlocal : Lp ℝ 2 (μ.prod (volume.restrict Ω')) := hvlocal.toLp v
  have heq : (vlocal : ℝ × E → ℝ) =ᵐ[μ.prod (volume.restrict Ω')] (v : ℝ × E → ℝ) := hvlocal.coeFn_toLp
  have hvnorm : ‖vlocal‖ ≤ ‖v‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ hm)
  refine ⟨vlocal, hvnorm.trans hv, ?_⟩
  filter_upwards [hvweak, Measure.ae_ae_of_ae_prod hu, Measure.ae_ae_of_ae_prod heq]
    with t ht htu htv
  have hweak := DeGiorgi.HasWeakPartialDeriv.restrict hΩ' (subset_univ Ω') ht
  intro φ hφ hφc hφs
  have hi := hweak φ hφ hφc hφs
  have hsource : (fun x => u (t, x)) =ᵐ[volume.restrict Ω'] fun x => w (t, x) := by
    filter_upwards [ae_restrict_of_ae htu, ae_restrict_mem hΩ'.measurableSet] with x hx hxΩ
    exact hx.trans (by rw [hηone x hxΩ, one_mul])
  have hl : (∫ x in Ω', u (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1)) =
      ∫ x in Ω', w (t, x) * fderiv ℝ φ x (EuclideanSpace.single k 1) := by
    apply integral_congr_ae
    filter_upwards [hsource] with x hx
    rw [hx]
  have hrr : (∫ x in Ω', vlocal (t, x) * φ x) = ∫ x in Ω', v (t, x) * φ x := by
    apply integral_congr_ae
    filter_upwards [htv] with x hx
    rw [hx]
  exact hl.symm.trans (hi.trans (congrArg Neg.neg hrr.symm))

end DifferentialGeometry.Analysis.Sobolev
