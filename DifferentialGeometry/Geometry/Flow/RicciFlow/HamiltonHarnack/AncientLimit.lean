import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

theorem hamilton_finite_origin_matrix_limit
    {q c t : Real} (ht : 0 < t)
    (hshift : ∀ α : Real, α ∈ Set.Ioo 0 t →
      0 ≤ q + c / (2 * (t - α))) :
    0 ≤ q + c / (2 * t) := by
  let alpha : Nat → Real := fun n => t / 2 * (1 / (n + 1 : Real))
  have halpha : Filter.Tendsto alpha Filter.atTop (nhds 0) := by
    simpa only [alpha, mul_zero] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)))
  have halphaMem (n : Nat) : alpha n ∈ Set.Ioo 0 t := by
    have hn : 0 < (n + 1 : Real) := by positivity
    have hone : 1 / (n + 1 : Real) ≤ 1 := by
      exact (div_le_one hn).2 (by norm_num)
    constructor
    · dsimp only [alpha]
      positivity
    · dsimp only [alpha]
      have hhalf : t / 2 < t := by linarith
      exact (mul_le_of_le_one_right (by positivity : 0 ≤ t / 2) hone).trans_lt hhalf
  have hden : Filter.Tendsto (fun n => 2 * (t - alpha n)) Filter.atTop
      (nhds (2 * t)) := by
    have hsub : Filter.Tendsto (fun n => t - alpha n) Filter.atTop
        (nhds (t - 0)) := tendsto_const_nhds.sub halpha
    simpa only [sub_zero] using tendsto_const_nhds.mul hsub
  have hlimit : Filter.Tendsto (fun n => q + c / (2 * (t - alpha n)))
      Filter.atTop (nhds (q + c / (2 * t))) := by
    exact tendsto_const_nhds.add
      (tendsto_const_nhds.div hden (by positivity : 2 * t ≠ 0))
  exact ge_of_tendsto hlimit (Filter.Eventually.of_forall fun n =>
    hshift (alpha n) (halphaMem n))

theorem hamilton_ancient_matrix_limit
    {q c t : Real}
    (hshift : ∀ α : Real, α < t → 0 ≤ q + c / (2 * (t - α)))
    (hc : 0 ≤ c) :
    0 ≤ q := by
  by_contra hq
  have hq' : q < 0 := lt_of_not_ge hq
  have hneg : 0 < -q := neg_pos.mpr hq'
  by_cases hc0 : c = 0
  · have hbad := hshift (t - 1) (by linarith)
    simp [hc0] at hbad
    linarith
  have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hratio_nonneg : 0 ≤ c / (2 * (-q)) := by positivity
  obtain ⟨n : Nat, hn⟩ := exists_nat_gt (c / (2 * (-q)))
  have hncast : c / (2 * (-q)) < (n : Real) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : Real) := by
    have : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have hden_pos : 0 < 2 * (-q) := by positivity
  have hmul : c < (n : Real) * (2 * (-q)) := by
    exact (div_lt_iff₀ hden_pos).mp hncast
  have hterm : c / (2 * (n : Real)) < -q := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : Real))).2
    nlinarith
  have hbad := hshift (t - (n : Real)) (by linarith)
  have hclock : 2 * (t - (t - (n : Real))) = 2 * (n : Real) := by ring
  rw [hclock] at hbad
  linarith

theorem hamilton_ancient_matrix_limit_of_all_origins
    {q c t : Real}
    (hshift : ∀ alpha : Real, alpha < t →
      0 ≤ q + c / (2 * (t - alpha))) :
    0 ≤ q := by
  have hc : 0 ≤ c := by
    by_contra hc
    have hcneg : c < 0 := lt_of_not_ge hc
    let epsilon := -c / (4 * (abs q + 1))
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      exact div_pos (neg_pos.mpr hcneg) (by positivity)
    have hbad := hshift (t - epsilon) (by linarith)
    have habs : q ≤ abs q := le_abs_self q
    change 0 ≤ q + c / (2 * (t - (t - epsilon))) at hbad
    rw [show t - (t - epsilon) = epsilon by ring] at hbad
    have heq : c / (2 * epsilon) = -2 * (abs q + 1) := by
      dsimp only [epsilon]
      field_simp [ne_of_lt hcneg,
        ne_of_gt (show 0 < abs q + 1 by positivity)]
      ring
    rw [heq] at hbad
    linarith [abs_nonneg q]
  exact hamilton_ancient_matrix_limit hshift hc

theorem hamilton_ancient_trace_limit
    {q c t : Real}
    (hshift : ∀ α : Real, α < t → 0 ≤ q + c / (t - α))
    (hc : 0 ≤ c) :
    0 ≤ q := by
  apply hamilton_ancient_matrix_limit (q := q) (c := 2 * c)
  · intro α hα
    have h := hshift α hα
    convert h using 1
    all_goals field_simp [sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hα))]
  · exact mul_nonneg (by norm_num) hc

theorem hamilton_ancient_trace_expression_nonneg
    {dR R b t : Real}
    (hshift : ∀ α : Real, α < t → 0 ≤ dR + R / (t - α) + b)
    (hR : 0 ≤ R) :
    0 ≤ dR + b := by
  apply hamilton_ancient_trace_limit (q := dR + b) (c := R)
  · intro α hα
    have h := hshift α hα
    convert h using 1
    all_goals field_simp [sub_ne_zero.mpr (ne_of_gt (sub_pos.mpr hα))]
    all_goals ring
  · exact hR

theorem hamilton_ancient_two_time_limit
    {A B t₁ t₂ : Real} (htimes : t₁ < t₂)
    (hshift : ∀ alpha : Real, alpha < t₁ →
      (t₁ - alpha) / (t₂ - alpha) * A ≤ B) :
    A ≤ B := by
  let denominator : Nat → Real := fun n => (n : Real) + 1 + (t₂ - t₁)
  have hdenominator : Filter.Tendsto denominator Filter.atTop Filter.atTop := by
    have hconst : Filter.Tendsto (fun _ : Nat => 1 + (t₂ - t₁))
        Filter.atTop (nhds (1 + (t₂ - t₁))) := tendsto_const_nhds
    have h := hconst.add_atTop (tendsto_natCast_atTop_atTop (R := Real))
    convert h using 1
    ext n
    dsimp only [denominator]
    ring
  have herror : Filter.Tendsto
      (fun n : Nat => (t₂ - t₁) / denominator n)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hdenominator
  have hratio : Filter.Tendsto
      (fun n : Nat => ((n : Real) + 1) / denominator n)
      Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : Nat => (1 : Real))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hsub := hone.sub herror
    convert hsub using 1
    · ext n
      dsimp only [denominator]
      field_simp [ne_of_gt
        (show 0 < (n : Real) + 1 + (t₂ - t₁) by positivity)]
      ring
    · simp
  have hleft : Filter.Tendsto
      (fun n : Nat => ((n : Real) + 1) / denominator n * A)
      Filter.atTop (nhds A) := by
    simpa using hratio.mul tendsto_const_nhds
  apply le_of_tendsto hleft
  filter_upwards [] with n
  have h := hshift (t₁ - ((n : Real) + 1)) (by
    have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith)
  have hdeneq : t₂ - (t₁ - ((n : Real) + 1)) = denominator n := by
    dsimp only [denominator]
    ring
  have hnumeq : t₁ - (t₁ - ((n : Real) + 1)) = (n : Real) + 1 := by
    ring
  rw [hdeneq, hnumeq] at h
  exact h

theorem hamilton_shifted_scalar_hasDerivAt
    {R dR : Real → Real} {α t : Real}
    (hR : HasDerivAt R (dR t) t) :
    HasDerivAt (fun s : Real => (s - α) * R s)
      (R t + (t - α) * dR t) t := by
  have hlin : HasDerivAt (fun s : Real => s - α) 1 t :=
    (hasDerivAt_id t).sub_const α
  have hmul := hlin.mul hR
  change HasDerivAt ((fun s : Real => s - α) * R)
    (R t + (t - α) * dR t) t
  simpa only [one_mul] using hmul

theorem hamilton_shifted_scalar_deriv_nonneg
    {R dR : Real → Real} {α t : Real}
    (hclock : α < t)
    (htrace : 0 ≤ dR t + R t / (t - α)) :
    0 ≤ R t + (t - α) * dR t := by
  have hτ : 0 < t - α := sub_pos.mpr hclock
  have hτne : t - α ≠ 0 := ne_of_gt hτ
  have hscale : 0 ≤ (t - α) * (dR t + R t / (t - α)) :=
    mul_nonneg hτ.le htrace
  field_simp [hτne] at hscale
  nlinarith

theorem hamilton_shifted_scalar_monotoneOn
    {R dR : Real → Real} {α a b : Real}
    (hαa : α ≤ a)
    (hcont : ContinuousOn (fun s : Real => (s - α) * R s) (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt R (dR s) s)
    (htrace : ∀ s ∈ Set.Ioo a b,
      0 ≤ dR s + R s / (s - α)) :
    MonotoneOn (fun s : Real => (s - α) * R s) (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
    (fun s hs =>
      (hamilton_shifted_scalar_hasDerivAt (α := α) (t := s)
        (hderiv s (by simpa [interior_Icc] using hs))).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      have hsi : s ∈ Set.Ioo a b := by simpa [interior_Icc] using hs
      rw [(hamilton_shifted_scalar_hasDerivAt (α := α) (t := s)
        (hderiv s hsi)).deriv]
      exact hamilton_shifted_scalar_deriv_nonneg
        (lt_of_le_of_lt hαa hsi.1) (htrace s hsi))

theorem hamilton_shifted_scalar_two_time
    {R : Real → Real} {α t₁ t₂ : Real}
    (ht : t₁ ≤ t₂)
    (hmono : MonotoneOn (fun s : Real => (s - α) * R s)
      (Set.Icc t₁ t₂)) :
    (t₁ - α) * R t₁ ≤ (t₂ - α) * R t₂ := by
  exact hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht

theorem monotoneOn_of_hamilton_ancient_scalar_trace
    {R dR : Real → Real} {a b : Real}
    (hcont : ContinuousOn R (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt R (dR s) s)
    (htrace : ∀ s ∈ Set.Ioo a b, 0 ≤ dR s) :
    MonotoneOn R (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
    (fun s hs =>
      (hderiv s (by simpa [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      have hsi : s ∈ Set.Ioo a b := by simpa [interior_Icc] using hs
      rw [(hderiv s hsi).deriv]
      exact htrace s hsi)

theorem hamilton_scalar_two_time_of_monotoneOn
    {R : Real → Real} {t₁ t₂ : Real}
    (ht : t₁ ≤ t₂)
    (hmono : MonotoneOn R (Set.Icc t₁ t₂)) :
    R t₁ ≤ R t₂ := by
  exact hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht

theorem hamilton_ancient_backward_time_trace_of_forward
    {timeDeriv gradientPair ricciPair : Real}
    (hforward : 0 ≤ timeDeriv + 2 * gradientPair + 2 * ricciPair) :
    0 ≤ -(-timeDeriv) - 2 * (-gradientPair) + 2 * ricciPair := by
  linarith

end DifferentialGeometry.PDE.RicciFlow
