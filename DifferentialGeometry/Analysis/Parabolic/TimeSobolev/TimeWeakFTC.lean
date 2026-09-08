import DifferentialGeometry.External.DeGiorgi.StampacchiaTruncation
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

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
  have hqIcc : IntegrableOn q (Icc a b) volume := by
    rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  let Q : ℝ → E := fun t ↦ ∫ r in a..t, q r
  have hQcont : ContinuousOn Q (Icc a b) := by
    have h := continuousOn_primitive_interval (show IntegrableOn q (uIcc a b) volume by
      simpa only [uIcc_of_le hab.le] using hqIcc)
    simpa only [Q, uIcc_of_le hab.le] using h
  have hQ : IntegrableOn Q (Ioo a b) volume :=
    (hQcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  let d : ℝ → E := fun t ↦ p t - Q t
  have hd : IntegrableOn d (Ioo a b) volume := hp.sub hQ
  let c : E := (b - a)⁻¹ • ∫ t in Ioo a b, d t
  have hdual (L : StrongDual ℝ E) :
      (fun t ↦ L (d t - c)) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    have hpL : IntegrableOn (fun t ↦ L (p t)) (Ioo a b) volume :=
      L.integrable_comp hp
    have hqL : IntegrableOn (fun t ↦ L (q t)) (Ioo a b) volume :=
      L.integrable_comp hq
    have hweakL : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b →
        ∫ t in Ioo a b, L (p t) * deriv φ t =
          -∫ t in Ioo a b, L (q t) * φ t := by
      intro φ hφ hφ_comp hφ_supp
      have hpφ : Integrable (fun t ↦ deriv φ t • p t)
          (volume.restrict (Ioo a b)) :=
        (show Integrable p (volume.restrict (Ioo a b)) from hp).locallyIntegrable
          |>.integrable_smul_left_of_hasCompactSupport
          (hφ.continuous_deriv (by norm_cast)) hφ_comp.deriv
      have hqφ : Integrable (fun t ↦ φ t • q t)
          (volume.restrict (Ioo a b)) :=
        (show Integrable q (volume.restrict (Ioo a b)) from hq).locallyIntegrable
          |>.integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_comp
      have h := congrArg L (hweak φ hφ hφ_comp hφ_supp)
      rw [← L.integral_comp_comm hpφ, map_neg, ← L.integral_comp_comm hqφ] at h
      simpa only [map_smul, smul_eq_mul, mul_comm] using h
    obtain ⟨C, hC⟩ := DeGiorgi.w11_ae_eq_ac_representative hab hpL hqL hweakL
    have hdC : (fun t ↦ L (d t)) =ᵐ[volume.restrict (Ioo a b)] fun _ ↦ C := by
      filter_upwards [hC, ae_restrict_mem measurableSet_Ioo] with t ht htmem
      have hq_int : IntervalIntegrable q volume a t :=
        (hqIcc.mono_set
          (uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ⟨htmem.1.le, htmem.2.le⟩)).intervalIntegrable
      change L (p t - Q t) = C
      rw [map_sub, show L (Q t) = ∫ r in a..t, L (q r) from
        (L.intervalIntegral_comp_comm hq_int).symm, ht]
      exact add_sub_cancel_right C _
    have hLc : L c = C := by
      change L ((b - a)⁻¹ • ∫ t in Ioo a b, d t) = C
      rw [map_smul, ← L.integral_comp_comm hd, integral_congr_ae hdC,
        setIntegral_const, Real.volume_real_Ioo_of_le hab.le, smul_eq_mul, smul_eq_mul]
      exact inv_mul_cancel_left₀ (sub_ne_zero.mpr hab.ne') C
    filter_upwards [hdC] with t ht
    simp only [Pi.zero_apply, map_sub, ht, hLc, sub_self]
  have hdsub : IntegrableOn (fun t ↦ d t - c) (Ioo a b) volume := hd.sub (integrable_const c)
  obtain ⟨s, hs, hsmem⟩ := hdsub.aestronglyMeasurable.isSeparable_ae_range
  have hzero := ae_eq_zero_of_forall_dual_of_isSeparable ℝ hs hdual hsmem
  refine ⟨c, ?_⟩
  filter_upwards [hzero] with t ht
  change p t - Q t - c = 0 at ht
  change p t = c + Q t
  exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp ht)

theorem exists_timeH1_of_weak_deriv_on
    {a b : ℝ} (hab : a < b) {p q : ℝ → E}
    (hp : MemLp p 2 (volume.restrict (Icc a b)))
    (hq : MemLp q 2 (volume.restrict (Icc a b)))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, deriv φ t • p t = -∫ t in Ioo a b, φ t • q t) :
    ∃ w : timeH1 E (b - a),
      (fun t ↦ p (a + t)) =ᵐ[timeMeasure (b - a)] w.toFun ∧
      w.deriv =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) := by
  have hpIcc : IntegrableOn p (Icc a b) volume := hp.integrable (by norm_num)
  have hqIcc : IntegrableOn q (Icc a b) volume := hq.integrable (by norm_num)
  obtain ⟨c, hc⟩ := weakDeriv_primitive hab
    (hpIcc.mono_set Ioo_subset_Icc_self) (hqIcc.mono_set Ioo_subset_Icc_self) hweak
  have hcIcc : p =ᵐ[volume.restrict (Icc a b)]
      fun t ↦ c + ∫ r in a..t, q r := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Icc] using hc
  have hshift : MeasurePreserving (fun t : ℝ ↦ a + t) (timeMeasure (b - a))
      (volume.restrict (Icc a b)) := by
    have h := (measurePreserving_add_right volume a).restrict_image_emb
      (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding (Icc (0 : ℝ) (b - a))
    simpa only [timeMeasure, image_add_const_Icc, zero_add, sub_add_cancel, add_comm a]
      using h
  let qL2 : timeL2 E (b - a) := (hq.comp_measurePreserving hshift).toLp
    (fun t ↦ q (a + t))
  let w : timeH1 E (b - a) := timeH1.mk c qL2
  have hqrep : qL2 =ᵐ[timeMeasure (b - a)] fun t ↦ q (a + t) :=
    MemLp.coeFn_toLp _
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hshift.quasiMeasurePreserving.ae_eq_comp hcIcc,
      ae_restrict_mem measurableSet_Icc] with t hct ht
    have hsub : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) (b - a) := by
      intro r hr
      rw [uIoc_of_le ht.1] at hr
      exact ⟨le_of_lt hr.1, hr.2.trans ht.2⟩
    have hqInterval : qL2 =ᵐ[volume.restrict (uIoc (0 : ℝ) t)]
        fun t ↦ q (a + t) :=
      hqrep.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hint : (∫ r in (0 : ℝ)..t, qL2 r) = ∫ r in a..a + t, q r := by
      rw [intervalIntegral.integral_congr_ae (ae_imp_of_ae_restrict hqInterval),
        intervalIntegral.integral_comp_add_left, add_zero]
    change p (a + t) = c + ∫ r in (0 : ℝ)..t, qL2 r
    change p (a + t) = c + ∫ r in a..a + t, q r at hct
    rw [hint]
    exact hct
  · simpa only [w, timeH1.deriv_mk] using hqrep

theorem exists_timeH1_of_weak_deriv
    {T : ℝ} (hT : 0 < T) {p q : ℝ → E}
    (hp : MemLp p 2 (timeMeasure T))
    (hq : MemLp q 2 (timeMeasure T))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) T →
      ∫ t in Ioo (0 : ℝ) T, deriv φ t • p t =
        -∫ t in Ioo (0 : ℝ) T, φ t • q t) :
    ∃ w : timeH1 E T, p =ᵐ[timeMeasure T] w.toFun ∧
      w.deriv =ᵐ[timeMeasure T] q := by
  have h := exists_timeH1_of_weak_deriv_on hT hp hq hweak
  rw [sub_zero] at h
  simpa only [zero_add] using h

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
