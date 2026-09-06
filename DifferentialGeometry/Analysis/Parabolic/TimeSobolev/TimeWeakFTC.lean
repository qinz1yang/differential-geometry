import DifferentialGeometry.External.DeGiorgi.StampacchiaTruncation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

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

theorem exists_timeH1_of_integrated_weak_deriv
    {T : ℝ} (hT : 0 < T) {p q : ℝ → ℝ}
    (hp : MemLp p 2 (timeMeasure T))
    (hq : MemLp q 2 (timeMeasure T)) (p₀ : ℝ)
    (hweak : ∀ (η dη : ℝ → ℝ),
      ContinuousOn η (Icc (0 : ℝ) T) →
      ContinuousOn dη (Icc (0 : ℝ) T) →
      (∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivWithinAt η (dη t) (Ioi t) t) →
      η T = 0 →
      -(∫ t in (0 : ℝ)..T, dη t * p t) - η 0 * p₀ =
        ∫ t in (0 : ℝ)..T, η t * q t) :
    ∃ w : timeH1 ℝ T,
      w.init = p₀ ∧ p =ᵐ[timeMeasure T] w.toFun ∧
        w.deriv =ᵐ[timeMeasure T] q := by
  have hpIcc : IntegrableOn p (Icc (0 : ℝ) T) volume := by
    change Integrable p (volume.restrict (Icc (0 : ℝ) T))
    simpa only [timeMeasure] using hp.integrable (by norm_num)
  have hqIcc : IntegrableOn q (Icc (0 : ℝ) T) volume := by
    change Integrable q (volume.restrict (Icc (0 : ℝ) T))
    simpa only [timeMeasure] using hq.integrable (by norm_num)
  have hpIoo : IntegrableOn p (Ioo (0 : ℝ) T) volume :=
    hpIcc.mono_set Ioo_subset_Icc_self
  have hqIoo : IntegrableOn q (Ioo (0 : ℝ) T) volume :=
    hqIcc.mono_set Ioo_subset_Icc_self
  have hset (f : ℝ → ℝ) :
      (∫ t in Ioo (0 : ℝ) T, f t) = ∫ t in (0 : ℝ)..T, f t := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc
  obtain ⟨c, hc⟩ := weakDeriv_primitive (E := ℝ) hT hpIoo hqIoo (by
    intro φ hφ hφ_comp hφ_supp
    have hφ0 : φ 0 = 0 := by
      by_contra hne
      exact (lt_irrefl (0 : ℝ)) (hφ_supp (subset_tsupport φ hne)).1
    have hφT : φ T = 0 := by
      by_contra hne
      exact (lt_irrefl T) (hφ_supp (subset_tsupport φ hne)).2
    have hφderiv : ContinuousOn (deriv φ) (Icc (0 : ℝ) T) :=
      (hφ.continuous_deriv (by norm_cast)).continuousOn
    have hφwithin : ∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivWithinAt φ (deriv φ t) (Ioi t) t := by
      intro t _
      exact (hφ.differentiable (by norm_cast)).differentiableAt.hasDerivAt.hasDerivWithinAt
    have hid := hweak φ (deriv φ) hφ.continuous.continuousOn
      hφderiv hφwithin hφT
    have hscalar :
        (∫ t in Ioo (0 : ℝ) T, p t * deriv φ t) =
          -(∫ t in Ioo (0 : ℝ) T, q t * φ t) := by
      rw [hset, hset]
      have hleft :
          (∫ t in (0 : ℝ)..T, p t * deriv φ t) =
            ∫ t in (0 : ℝ)..T, deriv φ t * p t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      have hright :
          (∫ t in (0 : ℝ)..T, q t * φ t) =
            ∫ t in (0 : ℝ)..T, φ t * q t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      rw [hleft, hright]
      simp only [hφ0, zero_mul, sub_zero] at hid
      linarith
    calc
      (∫ t in Ioo (0 : ℝ) T, deriv φ t • p t) =
          ∫ t in Ioo (0 : ℝ) T, p t * deriv φ t := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        simp only [smul_eq_mul, mul_comm]
      _ = -(∫ t in Ioo (0 : ℝ) T, q t * φ t) := hscalar
      _ = -(∫ t in Ioo (0 : ℝ) T, φ t • q t) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        simp only [smul_eq_mul, mul_comm])
  let P : ℝ → ℝ := fun t ↦ c + ∫ r in (0 : ℝ)..t, q r
  have hqii : IntervalIntegrable q volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
    exact hqIcc
  have hPac : AbsolutelyContinuousOnInterval P 0 T := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ c) 0 T :=
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    have hprimitive :=
      hqii.absolutelyContinuousOnInterval_intervalIntegral
        (c := (0 : ℝ)) left_mem_uIcc
    change AbsolutelyContinuousOnInterval
      ((fun _ : ℝ ↦ c) + fun t ↦ ∫ r in (0 : ℝ)..t, q r) 0 T
    exact hconst.add hprimitive
  let η : ℝ → ℝ := fun t ↦ (T - t) / T
  let dη : ℝ → ℝ := fun _ ↦ -(1 / T)
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    (contDiff_const.sub contDiff_id).div_const T
  have hdη : ContDiff ℝ (⊤ : ℕ∞) dη := contDiff_const
  have hηwithin : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivWithinAt η (dη t) (Ioi t) t := by
    intro t _
    simpa only [η, dη, id_eq, neg_div, one_div] using
      (((hasDerivAt_id t).const_sub T).div_const T).hasDerivWithinAt
  have hη0 : η 0 = 1 := by
    dsimp only [η]
    rw [sub_zero, div_self hT.ne']
  have hηT : η T = 0 := by simp only [η, sub_self, zero_div]
  have hramp := hweak η dη hη.continuous.continuousOn
    hdη.continuous.continuousOn hηwithin hηT
  have hcIoc : p =ᵐ[volume.restrict (Ioc (0 : ℝ) T)] P := by
    simpa only [P, Measure.restrict_congr_set Ioo_ae_eq_Ioc] using hc
  have hmassIntegral :
      (∫ t in (0 : ℝ)..T, dη t * p t) =
        ∫ t in (0 : ℝ)..T, dη t * P t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hcIoc] with t ht
    intro htmem
    rw [uIoc_of_le hT.le] at htmem
    rw [ht htmem]
  have hηderiv : ∀ t, deriv η t = dη t := by
    intro t
    simpa only [η, dη, id_eq, neg_div, one_div] using
      (((hasDerivAt_id t).const_sub T).div_const T).deriv
  have hPderiv : ∀ᵐ t, t ∈ uIoc (0 : ℝ) T → deriv P t = q t := by
    filter_upwards [hqii.ae_hasDerivAt_integral] with t ht
    intro htmem
    have hprimitive := ht (uIoc_subset_uIcc htmem) 0 left_mem_uIcc
    change deriv (fun s ↦ c + ∫ r in (0 : ℝ)..s, q r) t = q t
    exact (hprimitive.const_add c).deriv
  have hderivPIntegral :
      (∫ t in (0 : ℝ)..T, deriv P t * η t) =
        ∫ t in (0 : ℝ)..T, q t * η t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hPderiv] with t ht
    intro htmem
    rw [ht htmem]
  have hibp := hPac.integral_mul_deriv_eq_deriv_mul
    ((hη.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval)
  have hderivηIntegral :
      (∫ t in (0 : ℝ)..T, P t * deriv η t) =
        ∫ t in (0 : ℝ)..T, P t * dη t := by
    apply intervalIntegral.integral_congr
    intro t _
    change P t * deriv η t = P t * dη t
    rw [hηderiv]
  rw [hderivηIntegral, hderivPIntegral, hηT, hη0, mul_zero, mul_one,
    zero_sub] at hibp
  have hcommMass :
      (∫ t in (0 : ℝ)..T, dη t * P t) =
        ∫ t in (0 : ℝ)..T, P t * dη t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hcommSource :
      (∫ t in (0 : ℝ)..T, η t * q t) =
        ∫ t in (0 : ℝ)..T, q t * η t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hmassIntegral, hcommMass, hη0, hcommSource] at hramp
  have hP0 : P 0 = c := by simp only [P, intervalIntegral.integral_same, add_zero]
  rw [hP0] at hibp
  have hc0 : c = p₀ := by linarith
  let qL2 : timeL2 ℝ T := hq.toLp q
  let w : timeH1 ℝ T := timeH1.mk p₀ qL2
  have hqrep : qL2 =ᵐ[timeMeasure T] q := hq.coeFn_toLp
  have hcw : p =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] w.toFun := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with t hct ht
    have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := by
      intro r hr
      rw [uIoc_of_le ht.1.le] at hr
      exact ⟨le_of_lt hr.1, hr.2.trans ht.2.le⟩
    have hqIccRep : qL2 =ᵐ[volume.restrict (Icc (0 : ℝ) T)] q := by
      simpa only [timeMeasure] using hqrep
    have hqInterval : qL2 =ᵐ[volume.restrict (uIoc (0 : ℝ) t)] q :=
      hqIccRep.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hint : (∫ r in (0 : ℝ)..t, qL2 r) = ∫ r in (0 : ℝ)..t, q r :=
      intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict hqInterval)
    rw [hct, show c = p₀ from hc0, timeH1.toFun_apply]
    simp only [w, timeH1.init_mk, timeH1.deriv_mk, hint]
  refine ⟨w, rfl, ?_, ?_⟩
  · simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc] using hcw
  · simpa only [w, timeH1.deriv_mk] using hqrep

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
