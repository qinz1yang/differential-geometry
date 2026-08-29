import DifferentialGeometry.External.DeGiorgi.StampacchiaTruncation

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem weakDeriv_primitive
    {a b : ℝ} (hab : a < b) {p q : ℝ → E}
    (hp : IntegrableOn p (Ioo a b) volume)
    (hq : IntegrableOn q (Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, deriv φ t • p t = -∫ t in Ioo a b, φ t • q t) :
    ∃ c : E, p =ᵐ[volume.restrict (Ioo a b)]
      fun t ↦ c + ∫ r in a..t, q r := by
  classical
  let B := Module.finBasis ℝ E
  let L (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (B.coord i)
  have hp_coord (i : Fin (Module.finrank ℝ E)) :
      IntegrableOn (fun t ↦ L i (p t)) (Ioo a b) volume :=
    (L i).integrable_comp hp
  have hq_coord (i : Fin (Module.finrank ℝ E)) :
      IntegrableOn (fun t ↦ L i (q t)) (Ioo a b) volume :=
    (L i).integrable_comp hq
  have hweak_coord (i : Fin (Module.finrank ℝ E)) :
      ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b →
        ∫ t in Ioo a b, L i (p t) * deriv φ t =
          -∫ t in Ioo a b, L i (q t) * φ t := by
    intro φ hφ hφ_comp hφ_supp
    have hpφ : Integrable (fun t ↦ deriv φ t • p t)
        (volume.restrict (Ioo a b)) :=
      (show Integrable p (volume.restrict (Ioo a b)) from hp).locallyIntegrable
        |>.integrable_smul_left_of_hasCompactSupport
        (hφ.continuous_deriv (by norm_cast)) hφ_comp.deriv
    have hqφ : Integrable (fun t ↦ φ t • q t)
        (volume.restrict (Ioo a b)) :=
      (show Integrable q (volume.restrict (Ioo a b)) from hq).locallyIntegrable
        |>.integrable_smul_left_of_hasCompactSupport
        hφ.continuous hφ_comp
    have h := congrArg (L i) (hweak φ hφ hφ_comp hφ_supp)
    rw [← (L i).integral_comp_comm hpφ, map_neg,
      ← (L i).integral_comp_comm hqφ] at h
    simpa only [map_smul, smul_eq_mul, mul_comm] using h
  choose C hC using fun i ↦
    DeGiorgi.w11_ae_eq_ac_representative hab (hp_coord i) (hq_coord i)
      (hweak_coord i)
  refine ⟨B.equivFun.symm C, ?_⟩
  have hC_all : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ i,
      L i (p t) = C i + ∫ r in a..t, L i (q r) :=
    Filter.eventually_all.mpr hC
  filter_upwards [hC_all, ae_restrict_mem measurableSet_Ioo] with t ht_coord ht
  have hq_int : IntervalIntegrable q volume a t := by
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    have hq_Icc : IntegrableOn q (Icc a b) volume := by
      rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hq_Icc.mono_set
      (uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
  apply B.equivFun.injective
  funext i
  change L i (p t) = L i (B.equivFun.symm C + ∫ r in a..t, q r)
  rw [map_add, show L i (B.equivFun.symm C) = C i by
    exact B.coord_equivFun_symm i C,
    ← (L i).intervalIntegral_comp_comm hq_int]
  exact ht_coord i

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
