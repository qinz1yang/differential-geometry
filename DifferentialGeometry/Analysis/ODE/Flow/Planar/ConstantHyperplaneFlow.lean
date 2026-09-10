import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Topology
open scoped ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integralCurve_eq_translation_on_constant_hyperplane
    {v : E → E} (hv : ContDiff ℝ 1 v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : ℓ c = 0) (hfixed : ∀ x, ℓ x = b → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    {t : ℝ} (ht : ℓ (γ t) = b) (s : ℝ) : γ s = γ t + (s - t) • c := by
  let η : ℝ → E := fun r ↦ γ t + (r - t) • c
  have hηlevel (r : ℝ) : ℓ (η r) = b := by simp [η, hc, ht]
  have hηd (r : ℝ) : HasDerivAt η (v (η r)) r := by
    rw [hfixed _ (hηlevel r)]
    simpa only [η, one_smul, id_eq] using
      (((hasDerivAt_id r).sub_const t).smul_const c).const_add (γ t)
  let R := |s| + |t| + 1
  have htin : t ∈ Ioo (-R) R := by
    constructor <;> dsimp [R] <;> linarith [neg_abs_le t, le_abs_self t, abs_nonneg s]
  have hsin : s ∈ Ioo (-R) R := by
    constructor <;> dsimp [R] <;> linarith [neg_abs_le s, le_abs_self s, abs_nonneg t]
  have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth hv htin
    (fun r _ ↦ hγ r) (fun r _ ↦ hηd r) (by simp [η])
  exact he hsin

theorem lt_iff_of_integralCurve_constant_hyperplane
    {v : E → E} (hv : ContDiff ℝ 1 v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : ℓ c = 0) (hfixed : ∀ x, ℓ x = b → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ) :
    ℓ (γ s) < b ↔ ℓ (γ t) < b := by
  have hcont : Continuous (fun r ↦ ℓ (γ r)) := ℓ.continuous.comp
    (continuous_iff_continuousAt.mpr (fun r ↦ (hγ r).continuousAt))
  have hside (s t : ℝ) (hs : ℓ (γ s) < b) : ℓ (γ t) < b := by
    by_contra ht
    obtain ⟨u, hu⟩ := intermediate_value_univ s t hcont ⟨hs.le, not_lt.mp ht⟩
    have he := integralCurve_eq_translation_on_constant_hyperplane hv ℓ c hc hfixed hγ hu s
    have hlevel := congrArg ℓ he
    simp only [map_add, map_smul, smul_eq_mul, hu, hc, mul_zero, add_zero] at hlevel
    exact hs.ne hlevel
  exact ⟨hside s t, hside t s⟩

theorem le_iff_of_integralCurve_constant_hyperplane
    {v : E → E} (hv : ContDiff ℝ 1 v) (ℓ : E →L[ℝ] ℝ) (c : E) {b : ℝ}
    (hc : ℓ c = 0) (hfixed : ∀ x, ℓ x = b → v x = c)
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ) :
    ℓ (γ s) ≤ b ↔ ℓ (γ t) ≤ b := by
  have hside (s t : ℝ) (hs : ℓ (γ s) ≤ b) : ℓ (γ t) ≤ b := by
    rcases lt_or_eq_of_le hs with hs | hs
    · exact ((lt_iff_of_integralCurve_constant_hyperplane hv ℓ c hc hfixed hγ s t).mp hs).le
    · have he := integralCurve_eq_translation_on_constant_hyperplane hv ℓ c hc hfixed hγ hs t
      have hlevel := congrArg ℓ he
      simpa only [map_add, map_smul, smul_eq_mul, hs, hc, mul_zero, add_zero] using hlevel.le
  exact ⟨hside s t, hside t s⟩

end Poincare.Analysis
