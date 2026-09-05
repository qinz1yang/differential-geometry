import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set Topology

namespace DifferentialGeometry.Analysis.Integration

theorem neg_integral_mul_deriv_le
    {a b : ℝ} (hab : a ≤ b) {J ψ h : ℝ → ℝ}
    (hJ : AbsolutelyContinuousOnInterval J a b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hbdry : J a * ψ a ≤ J b * ψ b)
    (hψ0 : ∀ᵐ t ∂volume.restrict (uIcc a b), 0 ≤ ψ t)
    (hderiv : ∀ᵐ t ∂volume.restrict (uIcc a b),
      deriv J t ≤ h t * J t)
    (hint : IntervalIntegrable (fun t => h t * J t * ψ t) volume a b) :
    -(∫ t in a..b, J t * deriv ψ t) ≤
      ∫ t in a..b, h t * J t * ψ t := by
  have hleft : IntervalIntegrable (fun t => deriv J t * ψ t) volume a b :=
    hJ.intervalIntegrable_deriv.mul_continuousOn hψ.continuousOn
  have hpoint : ∀ᵐ t ∂volume.restrict (uIcc a b),
      deriv J t * ψ t ≤ h t * J t * ψ t := by
    filter_upwards [hderiv, hψ0] with t hderiv_t hψ_t
    exact mul_le_mul_of_nonneg_right hderiv_t hψ_t
  have hpoint' : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv J t * ψ t ≤ h t * J t * ψ t := by
    simpa only [uIcc_of_le hab] using hpoint
  have hmono :
      (∫ t in a..b, deriv J t * ψ t) ≤
        ∫ t in a..b, h t * J t * ψ t :=
    intervalIntegral.integral_mono_ae_restrict hab hleft hint hpoint'
  calc
    -(∫ t in a..b, J t * deriv ψ t) =
        (∫ t in a..b, deriv J t * ψ t) -
          (J b * ψ b - J a * ψ a) := by
      rw [hJ.integral_mul_deriv_eq_deriv_mul hψ]
      ring
    _ ≤ ∫ t in a..b, deriv J t * ψ t :=
      sub_le_self _ (sub_nonneg.mpr hbdry)
    _ ≤ ∫ t in a..b, h t * J t * ψ t := hmono

theorem neg_integral_mul_deriv_le_of_tsupport_subset
    {l a c b : ℝ} (ha : l < a) (hac : a ≤ c) (hc : c < b)
    {J ψ h : ℝ → ℝ}
    (hJ : AbsolutelyContinuousOnInterval J a c)
    (hψ : AbsolutelyContinuousOnInterval ψ a c)
    (hψsupp : tsupport ψ ⊆ Ioo a c)
    (hψ0 : ∀ᵐ t ∂volume.restrict (Ioo l b), 0 ≤ ψ t)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo l b),
      deriv J t ≤ h t * J t)
    (hint : IntegrableOn (fun t => h t * J t * ψ t) (Ioo l b)) :
    -(∫ t in Ioo l b, J t * deriv ψ t) ≤
      ∫ t in Ioo l b, h t * J t * ψ t := by
  have hsub : Icc a c ⊆ Ioo l b := by
    rintro t ⟨hat, htc⟩
    exact ⟨ha.trans_le hat, htc.trans_lt hc⟩
  have hψa : ψ a = 0 := by
    by_contra hne
    have ha_mem : a ∈ tsupport ψ :=
      subset_tsupport ψ (Function.mem_support.mpr hne)
    exact (lt_irrefl a) (hψsupp ha_mem).1
  have hψc : ψ c = 0 := by
    by_contra hne
    have hc_mem : c ∈ tsupport ψ :=
      subset_tsupport ψ (Function.mem_support.mpr hne)
    exact (lt_irrefl c) (hψsupp hc_mem).2
  have hψ0' : ∀ᵐ t ∂volume.restrict (uIcc a c), 0 ≤ ψ t := by
    rw [uIcc_of_le hac]
    exact ae_mono (Measure.restrict_mono hsub le_rfl) hψ0
  have hderiv' : ∀ᵐ t ∂volume.restrict (uIcc a c),
      deriv J t ≤ h t * J t := by
    rw [uIcc_of_le hac]
    exact ae_mono (Measure.restrict_mono hsub le_rfl) hderiv
  have hint' : IntervalIntegrable (fun t => h t * J t * ψ t) volume a c := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hac]
    exact hint.mono_set hsub
  have hfinite :
      -(∫ t in a..c, J t * deriv ψ t) ≤
        ∫ t in a..c, h t * J t * ψ t :=
    neg_integral_mul_deriv_le hac hJ hψ (by simp only [hψa, hψc, mul_zero, le_rfl])
      hψ0' hderiv' hint'
  have hleft :
      (∫ t in Ioo l b, J t * deriv ψ t) =
        ∫ t in a..c, J t * deriv ψ t := by
    calc
      (∫ t in Ioo l b, J t * deriv ψ t) =
          ∫ t in Icc a c, J t * deriv ψ t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
        intro t ht
        have ht_not : t ∉ tsupport ψ := by
          intro ht_mem
          exact ht.2 (Ioo_subset_Icc_self (hψsupp ht_mem))
        rw [deriv_of_notMem_tsupport ht_not, mul_zero]
      _ = ∫ t in Ioc a c, J t * deriv ψ t :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ t in a..c, J t * deriv ψ t := by
        rw [intervalIntegral.integral_of_le hac]
  have hright :
      (∫ t in Ioo l b, h t * J t * ψ t) =
        ∫ t in a..c, h t * J t * ψ t := by
    calc
      (∫ t in Ioo l b, h t * J t * ψ t) =
          ∫ t in Icc a c, h t * J t * ψ t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
        intro t ht
        have ht_not : t ∉ tsupport ψ := by
          intro ht_mem
          exact ht.2 (Ioo_subset_Icc_self (hψsupp ht_mem))
        have hψt : ψ t = 0 := by
          by_contra hne
          exact ht_not (subset_tsupport ψ (Function.mem_support.mpr hne))
        simp only [hψt, mul_zero]
      _ = ∫ t in Ioc a c, h t * J t * ψ t :=
        integral_Icc_eq_integral_Ioc
      _ = ∫ t in a..c, h t * J t * ψ t := by
        rw [intervalIntegral.integral_of_le hac]
  rw [hleft, hright]
  exact hfinite

theorem neg_integral_mul_deriv_le_of_eq_zero
    {l a b : ℝ} (ha : l < a) (hab : a ≤ b) {J ψ h : ℝ → ℝ}
    (hJ : AbsolutelyContinuousOnInterval J a b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψzero : EqOn ψ 0 (Ioc l a))
    (hbdry : 0 ≤ J b * ψ b)
    (hψ0 : ∀ᵐ t ∂volume.restrict (Ioo l b), 0 ≤ ψ t)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo l b),
      deriv J t ≤ h t * J t)
    (hint : IntegrableOn (fun t => h t * J t * ψ t) (Ioo l b)) :
    -(∫ t in Ioo l b, J t * deriv ψ t) ≤
      ∫ t in Ioo l b, h t * J t * ψ t := by
  have hopen : Ioo a b ⊆ Ioo l b :=
    fun _ ht => ⟨ha.trans ht.1, ht.2⟩
  have hhalf : Ico a b ⊆ Ioo l b :=
    fun _ ht => ⟨ha.trans_le ht.1, ht.2⟩
  have hψa : ψ a = 0 := hψzero ⟨ha, le_rfl⟩
  have hψderiv : EqOn (deriv ψ) 0 (Ioo l a) := by
    simpa only [deriv_zero] using
      (hψzero.mono Ioo_subset_Ioc_self).deriv isOpen_Ioo
  have hψ0' : ∀ᵐ t ∂volume.restrict (uIcc a b), 0 ≤ ψ t := by
    rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_mono (Measure.restrict_mono hopen le_rfl) hψ0
  have hderiv' : ∀ᵐ t ∂volume.restrict (uIcc a b),
      deriv J t ≤ h t * J t := by
    rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_mono (Measure.restrict_mono hopen le_rfl) hderiv
  have hint' : IntervalIntegrable (fun t => h t * J t * ψ t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    exact hint.mono_set hopen
  have hfinite :
      -(∫ t in a..b, J t * deriv ψ t) ≤
        ∫ t in a..b, h t * J t * ψ t :=
    neg_integral_mul_deriv_le hab hJ hψ (by simpa only [hψa, mul_zero] using hbdry)
      hψ0' hderiv' hint'
  have hleft :
      (∫ t in Ioo l b, J t * deriv ψ t) =
        ∫ t in a..b, J t * deriv ψ t := by
    calc
      (∫ t in Ioo l b, J t * deriv ψ t) =
          ∫ t in Ico a b, J t * deriv ψ t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hhalf
        intro t ht
        have hta : t < a := lt_of_not_ge fun hat => ht.2 ⟨hat, ht.1.2⟩
        have hψderiv_t : deriv ψ t = 0 := by
          simpa only [Pi.zero_apply] using hψderiv ⟨ht.1.1, hta⟩
        rw [hψderiv_t, mul_zero]
      _ = ∫ t in Ioc a b, J t * deriv ψ t :=
        integral_Ico_eq_integral_Ioc
      _ = ∫ t in a..b, J t * deriv ψ t := by
        rw [intervalIntegral.integral_of_le hab]
  have hright :
      (∫ t in Ioo l b, h t * J t * ψ t) =
        ∫ t in a..b, h t * J t * ψ t := by
    calc
      (∫ t in Ioo l b, h t * J t * ψ t) =
          ∫ t in Ico a b, h t * J t * ψ t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hhalf
        intro t ht
        have hta : t < a := lt_of_not_ge fun hat => ht.2 ⟨hat, ht.1.2⟩
        have hψt : ψ t = 0 := by
          simpa only [Pi.zero_apply] using hψzero ⟨ht.1.1, hta.le⟩
        rw [hψt, mul_zero]
      _ = ∫ t in Ioc a b, h t * J t * ψ t :=
        integral_Ico_eq_integral_Ioc
      _ = ∫ t in a..b, h t * J t * ψ t := by
        rw [intervalIntegral.integral_of_le hab]
  rw [hleft, hright]
  exact hfinite

theorem neg_integral_mul_deriv_le_of_locally_absolutely_continuous
    {l a b : ℝ} (ha : l < a) (hab : a < b) {J ψ h : ℝ → ℝ}
    (hJ : ∀ c ∈ Ioo a b, AbsolutelyContinuousOnInterval J a c)
    (hψ : ∀ c ∈ Ioo a b, AbsolutelyContinuousOnInterval ψ a c)
    (hψzero : EqOn ψ 0 (Ioc l a))
    (hbdry : ∀ c ∈ Ioo a b, 0 ≤ J c * ψ c)
    (hψ0 : ∀ᵐ t ∂volume.restrict (Ioo l b), 0 ≤ ψ t)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioo l b),
      deriv J t ≤ h t * J t)
    (hLint : IntegrableOn (fun t => J t * deriv ψ t) (Ioo l b))
    (hRint : IntegrableOn (fun t => h t * J t * ψ t) (Ioo l b)) :
    -(∫ t in Ioo l b, J t * deriv ψ t) ≤
      ∫ t in Ioo l b, h t * J t * ψ t := by
  let c : ℕ → ℝ := fun n => b - (b - a) / ((n : ℝ) + 2)
  let s : ℕ → Set ℝ := fun n => Ico a (c n)
  have hc_mem (n : ℕ) : c n ∈ Ioo a b := by
    have hba : 0 < b - a := sub_pos.mpr hab
    have hden : 1 < (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    constructor
    · have hq := div_lt_self hba hden
      dsimp [c]
      linarith
    · have hq : 0 < (b - a) / ((n : ℝ) + 2) :=
        div_pos hba (by positivity)
      dsimp [c]
      linarith
  have hc_mono : Monotone c := by
    intro n m hnm
    have hden : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hnm 2
    have hq := div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le)
      (by positivity : 0 < (n : ℝ) + 2) hden
    dsimp [c]
    linarith
  have hδ : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one,
      show (2 : ℝ) = 1 + 1 by norm_num, add_assoc] using
      ((tendsto_add_atTop_iff_nat 1).2
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hc_lim : Tendsto c atTop (𝓝 b) := by
    have H := (tendsto_const_nhds (x := b)).sub
      ((tendsto_const_nhds (x := b - a)).mul hδ)
    simpa [c, div_eq_mul_inv] using H
  have hs_mono : Monotone s :=
    fun _ _ hnm => Ico_subset_Ico_right (hc_mono hnm)
  have hs_union : (⋃ n, s n) = Ico a b := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hxn⟩
      exact ⟨hxn.1, hxn.2.trans (hc_mem n).2⟩
    · intro hx
      have hev : ∀ᶠ n in atTop, x < c n :=
        hc_lim.eventually (Ioi_mem_nhds hx.2)
      rcases hev.exists with ⟨n, hn⟩
      exact mem_iUnion.mpr ⟨n, hx.1, hn⟩
  have hhalf : Ico a b ⊆ Ioo l b :=
    fun _ ht => ⟨ha.trans_le ht.1, ht.2⟩
  have hψa : ψ a = 0 := hψzero ⟨ha, le_rfl⟩
  have hψderiv : EqOn (deriv ψ) 0 (Ioo l a) := by
    simpa only [deriv_zero] using
      (hψzero.mono Ioo_subset_Ioc_self).deriv isOpen_Ioo
  have hlim (q : ℝ → ℝ) (hq : IntegrableOn q (Ioo l b)) :
      Tendsto (fun n => ∫ t in a..c n, q t) atTop
        (𝓝 (∫ t in Ico a b, q t)) := by
    have H : Tendsto (fun n => ∫ t in s n, q t) atTop
        (𝓝 (∫ t in Ico a b, q t)) := by
      simpa only [hs_union] using
        tendsto_setIntegral_of_monotone
          (f := q) (μ := volume) (s := s) (fun _ => measurableSet_Ico) hs_mono
          (by
            rw [hs_union]
            exact hq.mono_set hhalf)
    exact H.congr' <| Eventually.of_forall fun n => by
      dsimp [s]
      rw [intervalIntegral.integral_of_le (hc_mem n).1.le]
      exact integral_Ico_eq_integral_Ioc
  have hfinite (n : ℕ) :
      -(∫ t in a..c n, J t * deriv ψ t) ≤
        ∫ t in a..c n, h t * J t * ψ t := by
    have hsub : Icc a (c n) ⊆ Ioo l b := by
      rintro t ⟨hat, htc⟩
      exact ⟨ha.trans_le hat, htc.trans_lt (hc_mem n).2⟩
    have hψ0' : ∀ᵐ t ∂volume.restrict (uIcc a (c n)), 0 ≤ ψ t := by
      rw [uIcc_of_le (hc_mem n).1.le]
      exact ae_mono (Measure.restrict_mono hsub le_rfl) hψ0
    have hderiv' : ∀ᵐ t ∂volume.restrict (uIcc a (c n)),
        deriv J t ≤ h t * J t := by
      rw [uIcc_of_le (hc_mem n).1.le]
      exact ae_mono (Measure.restrict_mono hsub le_rfl) hderiv
    have hRint' : IntervalIntegrable (fun t => h t * J t * ψ t)
        volume a (c n) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hc_mem n).1.le]
      exact hRint.mono_set hsub
    exact neg_integral_mul_deriv_le (hc_mem n).1.le
      (hJ (c n) (hc_mem n)) (hψ (c n) (hc_mem n))
      (by simpa only [hψa, mul_zero] using hbdry (c n) (hc_mem n))
      hψ0' hderiv' hRint'
  have hLlim := hlim (fun t => J t * deriv ψ t) hLint
  have hRlim := hlim (fun t => h t * J t * ψ t) hRint
  have hIco :
      -(∫ t in Ico a b, J t * deriv ψ t) ≤
        ∫ t in Ico a b, h t * J t * ψ t :=
    le_of_tendsto_of_tendsto' hLlim.neg hRlim hfinite
  have hleft :
      (∫ t in Ioo l b, J t * deriv ψ t) =
        ∫ t in Ico a b, J t * deriv ψ t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hhalf
    intro t ht
    have hta : t < a := lt_of_not_ge fun hat => ht.2 ⟨hat, ht.1.2⟩
    have hz : deriv ψ t = 0 := by
      simpa only [Pi.zero_apply] using hψderiv ⟨ht.1.1, hta⟩
    rw [hz, mul_zero]
  have hright :
      (∫ t in Ioo l b, h t * J t * ψ t) =
        ∫ t in Ico a b, h t * J t * ψ t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hhalf
    intro t ht
    have hta : t < a := lt_of_not_ge fun hat => ht.2 ⟨hat, ht.1.2⟩
    have hz : ψ t = 0 := by
      simpa only [Pi.zero_apply] using hψzero ⟨ht.1.1, hta.le⟩
    rw [hz, mul_zero]
  rw [hleft, hright]
  exact hIco

end DifferentialGeometry.Analysis.Integration
