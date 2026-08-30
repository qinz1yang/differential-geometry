import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

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

theorem hamilton_ancient_scalar_monotoneOn
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

theorem hamilton_ancient_scalar_two_time
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
