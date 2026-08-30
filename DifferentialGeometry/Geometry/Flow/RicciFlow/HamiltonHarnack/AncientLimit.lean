import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul

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

end DifferentialGeometry.PDE.RicciFlow
