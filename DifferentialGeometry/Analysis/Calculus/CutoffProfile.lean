import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.CutoffProfile

open Filter Set
open scoped ContDiff Topology

def stem (s : ℝ) : ℝ :=
  1 - Real.smoothTransition (s - 1)

def value (s : ℝ) : ℝ :=
  stem s ^ 2

theorem contDiff : ContDiff ℝ ∞ value := by
  have hlin : ContDiff ℝ ∞ (fun s : ℝ => s - 1) :=
    contDiff_id.sub contDiff_const
  have hstem : ContDiff ℝ ∞ stem := by
    simpa [stem] using
      (contDiff_const.sub (Real.smoothTransition.contDiff.comp hlin))
  simpa [value] using hstem.pow 2

theorem mem_Icc (s : ℝ) : value s ∈ Icc (0 : ℝ) 1 := by
  have hσ0 : 0 ≤ Real.smoothTransition (s - 1) :=
    Real.smoothTransition.nonneg _
  have hσ1 : Real.smoothTransition (s - 1) ≤ 1 :=
    Real.smoothTransition.le_one _
  constructor
  · exact sq_nonneg _
  · unfold value stem
    nlinarith [sq_nonneg (Real.smoothTransition (s - 1))]

theorem one_of_le_one {s : ℝ} (hs : s ≤ 1) : value s = 1 := by
  have hzero : Real.smoothTransition (s - 1) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [value, stem, hzero]

theorem zero_of_two_le {s : ℝ} (hs : 2 ≤ s) : value s = 0 := by
  have hone : Real.smoothTransition (s - 1) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [value, stem, hone]

theorem antitone_value : Antitone value := by
  have hstem_nonneg : ∀ y : ℝ, 0 ≤ stem y := by
    intro y
    unfold stem
    linarith [Real.smoothTransition.le_one (y - 1)]
  have hstem_antitone : Antitone stem := by
    intro a b hab
    have hmono :=
      Real.smoothTransition.monotone (sub_le_sub_right hab 1)
    unfold stem
    linarith
  intro a b hab
  rw [value, value]
  nlinarith [hstem_antitone hab, hstem_nonneg a, hstem_nonneg b]

noncomputable def evalue (s : ENNReal) : Real :=
  value (ENNReal.truncateToReal (2 : ENNReal) s)

theorem evalue_zero_of_ge {s : ENNReal} (hs : 2 ≤ s) :
    evalue s = 0 := by
  simp only [evalue, ENNReal.truncateToReal, min_eq_left hs,
    ENNReal.toReal_ofNat]
  exact zero_of_two_le le_rfl

@[simp] theorem evalue_top : evalue ⊤ = 0 :=
  evalue_zero_of_ge le_top

theorem evalue_eq_value {s : ENNReal} (hs : s ≠ ⊤) :
    evalue s = value s.toReal := by
  by_cases hle : s ≤ 2
  · rw [evalue,
      ENNReal.truncateToReal_eq_toReal (by norm_num) hle]
  · have htwo : (2 : ENNReal) ≤ s := (not_le.mp hle).le
    rw [evalue_zero_of_ge htwo, zero_of_two_le]
    simpa using ENNReal.toReal_mono hs htwo

theorem continuous_evalue : Continuous evalue :=
  contDiff.continuous.comp
    (ENNReal.continuous_truncateToReal (by norm_num))

theorem evalue_mem_Icc (s : ENNReal) :
    evalue s ∈ Set.Icc (0 : Real) 1 :=
  mem_Icc _

theorem evalue_one_of_le {s : ENNReal} (hs : s ≤ 1) :
    evalue s = 1 := by
  rw [evalue,
    ENNReal.truncateToReal_eq_toReal (by norm_num)
      (hs.trans (by norm_num))]
  apply one_of_le_one
  simpa using ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hs

theorem antitone_evalue : Antitone evalue := by
  intro a b hab
  exact antitone_value
    ((ENNReal.monotone_truncateToReal (by norm_num)) hab)

private theorem exists_stem_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |deriv stem s| ≤ C := by
  have hstem : ContDiff ℝ 1 stem :=
    (show ContDiff ℝ ∞ stem from by
      have hlin : ContDiff ℝ ∞ (fun s : ℝ => s - 1) :=
        contDiff_id.sub contDiff_const
      simpa [stem] using
        (contDiff_const.sub (Real.smoothTransition.contDiff.comp hlin))).of_le
      (by simp)
  have hcont : Continuous (deriv stem) := hstem.continuous_deriv_one
  obtain ⟨sMax, -, hsMax⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hcont.norm.continuousOn
  refine ⟨|deriv stem sMax|, abs_nonneg _, ?_⟩
  intro s
  by_cases hs1 : s < (1 : ℝ)
  · have hloc : stem =ᶠ[nhds s] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs1] with y hy
      change y < 1 at hy
      have hzero : Real.smoothTransition (y - 1) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [stem, hzero]
    rw [hloc.deriv_eq, deriv_const, abs_zero]
    exact abs_nonneg _
  · by_cases hs2 : (2 : ℝ) < s
    · have hloc : stem =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hs2] with y hy
        change 2 < y at hy
        have hone : Real.smoothTransition (y - 1) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith)
        simp [stem, hone]
      rw [hloc.deriv_eq, deriv_const, abs_zero]
      exact abs_nonneg _
    · push Not at hs1 hs2
      simpa [Real.norm_eq_abs] using
        (Filter.eventually_principal.mp hsMax s (Set.mem_Icc.2 ⟨hs1, hs2⟩))

theorem deriv_eq (s : ℝ) :
    deriv value s = 2 * stem s * deriv stem s := by
  have hstem : DifferentiableAt ℝ stem s := by
    have hsmooth : ContDiff ℝ ∞ stem := by
      have hlin : ContDiff ℝ ∞ (fun y : ℝ => y - 1) :=
        contDiff_id.sub contDiff_const
      simpa [stem] using
        (contDiff_const.sub (Real.smoothTransition.contDiff.comp hlin))
    exact hsmooth.differentiable (by simp) s
  change deriv (stem ^ 2) s = _
  rw [deriv_pow hstem 2]
  ring

theorem deriv_nonpos (s : ℝ) : deriv value s ≤ 0 := by
  exact antitone_value.deriv_nonpos

theorem deriv_zero_of_le {s : Real} (hs : s ≤ 1) :
    deriv value s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [one_of_le_one hs]
  exact (mem_Icc y).2

theorem deriv_zero_of_ge {s : Real} (hs : 2 ≤ s) :
    deriv value s = 0 := by
  apply IsLocalMin.deriv_eq_zero
  filter_upwards with y
  rw [zero_of_two_le hs]
  exact (mem_Icc y).1

theorem deriv2_zero_of_le {s : Real} (hs : s ≤ 1) :
    deriv (deriv value) s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [deriv_zero_of_le hs]
  exact deriv_nonpos y

theorem deriv2_zero_of_ge {s : Real} (hs : 2 ≤ s) :
    deriv (deriv value) s = 0 := by
  apply IsLocalMax.deriv_eq_zero
  filter_upwards with y
  rw [deriv_zero_of_ge hs]
  exact deriv_nonpos y

theorem deriv3_zero_of_le {s : Real} (hs : s ≤ 1) :
    deriv (deriv (deriv value)) s = 0 := by
  have hle3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤
        (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    exact h
  have hdiff : DifferentiableAt ℝ (deriv (deriv value)) s :=
    (((contDiff.of_le hle3).deriv' (n := 2)).deriv' (n := 1)).differentiable
      (by simp) s
  exact (uniqueDiffOn_Iic 1 s hs).eq_deriv _
    hdiff.hasDerivAt.hasDerivWithinAt
    ((hasDerivWithinAt_const (x := s) (s := Iic 1) (c := (0 : ℝ))).congr_of_mem
      (fun y hy ↦ deriv2_zero_of_le hy) hs)

theorem deriv3_zero_of_ge {s : Real} (hs : 2 ≤ s) :
    deriv (deriv (deriv value)) s = 0 := by
  have hle3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤
        (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    exact h
  have hdiff : DifferentiableAt ℝ (deriv (deriv value)) s :=
    (((contDiff.of_le hle3).deriv' (n := 2)).deriv' (n := 1)).differentiable
      (by simp) s
  exact (uniqueDiffOn_Ici 2 s hs).eq_deriv _
    hdiff.hasDerivAt.hasDerivWithinAt
    ((hasDerivWithinAt_const (x := s) (s := Ici 2) (c := (0 : ℝ))).congr_of_mem
      (fun y hy ↦ deriv2_zero_of_ge hy) hs)

theorem exists_deriv_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, (deriv value s) ^ 2 ≤ C * value s := by
  obtain ⟨C, hC, hbound⟩ := exists_stem_bound
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro s
  have hsq : (deriv stem s) ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_nonneg (C - |deriv stem s|), abs_nonneg (deriv stem s),
      hbound s, sq_abs (deriv stem s)]
  rw [deriv_eq, value]
  nlinarith [sq_nonneg (stem s)]

theorem exists_deriv_bounds :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s : ℝ, |deriv value s| ≤ C) ∧
      ∀ s : ℝ, |deriv (deriv value) s| ≤ C := by
  have hle1 : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h :
        ((1 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
    exact h
  have hle2 : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h :
        ((2 : ℕ∞) : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    exact h
  have hvalue1 : ContDiff ℝ 1 value :=
    contDiff.of_le hle1
  have hvalue2 : ContDiff ℝ 2 value :=
    contDiff.of_le hle2
  have hderiv1 : Continuous (deriv value) :=
    hvalue1.continuous_deriv_one
  have hderiv2 : Continuous (deriv (deriv value)) := by
    exact (hvalue2.deriv' (n := 1)).continuous_deriv_one
  obtain ⟨s₁, -, hs₁⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hderiv1.norm.continuousOn
  obtain ⟨s₂, -, hs₂⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hderiv2.norm.continuousOn
  let C := max |deriv value s₁| |deriv (deriv value) s₂|
  have hC : 0 ≤ C := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨C, hC, ?_, ?_⟩
  · intro s
    by_cases hs0 : s < (1 : ℝ)
    · have hloc : value =ᶠ[nhds s] fun _ => (1 : ℝ) := by
        filter_upwards [Iio_mem_nhds hs0] with y hy
        exact one_of_le_one hy.le
      rw [hloc.deriv_eq, deriv_const, abs_zero]
      exact hC
    · by_cases hs3 : (2 : ℝ) < s
      · have hloc : value =ᶠ[nhds s] fun _ => (0 : ℝ) := by
          filter_upwards [Ioi_mem_nhds hs3] with y hy
          exact zero_of_two_le hy.le
        rw [hloc.deriv_eq, deriv_const, abs_zero]
        exact hC
      · push Not at hs0 hs3
        have hmax : |deriv value s| ≤ |deriv value s₁| := by
          simpa [Real.norm_eq_abs] using
            (Filter.eventually_principal.mp hs₁ s
              (Set.mem_Icc.2 ⟨hs0, hs3⟩))
        exact hmax.trans (le_max_left _ _)
  · intro s
    by_cases hs0 : s < (1 : ℝ)
    · have hloc : deriv value =ᶠ[nhds s] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hs0] with y hy
        have hval : value =ᶠ[nhds y] fun _ => (1 : ℝ) := by
          filter_upwards [Iio_mem_nhds hy] with z hz
          exact one_of_le_one hz.le
        rw [hval.deriv_eq, deriv_const]
      rw [hloc.deriv_eq, deriv_const, abs_zero]
      exact hC
    · by_cases hs3 : (2 : ℝ) < s
      · have hloc : deriv value =ᶠ[nhds s] fun _ => (0 : ℝ) := by
          filter_upwards [Ioi_mem_nhds hs3] with y hy
          have hval : value =ᶠ[nhds y] fun _ => (0 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hy] with z hz
            exact zero_of_two_le hz.le
          rw [hval.deriv_eq, deriv_const]
        rw [hloc.deriv_eq, deriv_const, abs_zero]
        exact hC
      · push Not at hs0 hs3
        have hmax :
            |deriv (deriv value) s| ≤ |deriv (deriv value) s₂| := by
          simpa [Real.norm_eq_abs] using
            (Filter.eventually_principal.mp hs₂ s
              (Set.mem_Icc.2 ⟨hs0, hs3⟩))
        exact hmax.trans (le_max_right _ _)

noncomputable def derivBound : ℝ :=
  Classical.choose exists_deriv_bounds

theorem derivBound_nonneg : 0 ≤ derivBound :=
  (Classical.choose_spec exists_deriv_bounds).1

theorem abs_deriv_le_derivBound (s : ℝ) :
    |deriv value s| ≤ derivBound :=
  (Classical.choose_spec exists_deriv_bounds).2.1 s

theorem abs_deriv2_le_derivBound (s : ℝ) :
    |deriv (deriv value) s| ≤ derivBound :=
  (Classical.choose_spec exists_deriv_bounds).2.2 s

theorem exists_deriv3_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℝ, |deriv (deriv (deriv value)) s| ≤ C := by
  have hle3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤
        (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    exact h
  have hvalue3 : ContDiff ℝ 3 value := contDiff.of_le hle3
  have hderiv3 : Continuous (deriv (deriv (deriv value))) :=
    ((hvalue3.deriv' (n := 2)).deriv' (n := 1)).continuous_deriv_one
  obtain ⟨sMax, -, hsMax⟩ :=
    (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_isMaxOn
      (Set.nonempty_Icc.2 (by norm_num)) hderiv3.norm.continuousOn
  refine ⟨|deriv (deriv (deriv value)) sMax|, abs_nonneg _, ?_⟩
  intro s
  by_cases hs1 : s < (1 : ℝ)
  · rw [deriv3_zero_of_le hs1.le, abs_zero]
    exact abs_nonneg _
  · by_cases hs2 : (2 : ℝ) < s
    · rw [deriv3_zero_of_ge hs2.le, abs_zero]
      exact abs_nonneg _
    · push Not at hs1 hs2
      simpa [Real.norm_eq_abs] using
        (Filter.eventually_principal.mp hsMax s
          (Set.mem_Icc.2 ⟨hs1, hs2⟩))

noncomputable def deriv3Bound : ℝ :=
  Classical.choose exists_deriv3_bound

theorem deriv3Bound_nonneg : 0 ≤ deriv3Bound :=
  (Classical.choose_spec exists_deriv3_bound).1

theorem abs_deriv3_le_deriv3Bound (s : ℝ) :
    |deriv (deriv (deriv value)) s| ≤ deriv3Bound :=
  (Classical.choose_spec exists_deriv3_bound).2 s

end DifferentialGeometry.Analysis.CutoffProfile
