import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option linter.unusedSectionVars false

/-!
# Integral form of Grönwall's inequality

`Mathlib.Analysis.ODE.Gronwall` proves the **differential** Grönwall inequality
(`le_gronwallBound_of_liminf_deriv_right_le`). Many estimates — notably mild-solution
bounds for semilinear evolution equations — instead need the **integral** form:

> if `0 ≤ f` is continuous on `[0, T]` and satisfies
> `f(t) ≤ A + K ∫₀ᵗ f`, then `f(t) ≤ A · exp(K t)` on `[0, T]`,

together with its affine refinement

> if `f(t) ≤ A + B t + K ∫₀ᵗ f`, then `f(t) ≤ (A + B t) · exp(K t)`.

Both follow from the differential form applied to the primitive
`g(t) := A + K ∫₀ᵗ f`. This file packages the two statements; they could
reasonably be upstreamed alongside the existing material in
`Mathlib.Analysis.ODE.Gronwall`.
-/

open MeasureTheory Set Real
open scoped Topology

namespace RicciFlower.Analysis.ODE

/-- Clamp a function defined on `Icc 0 T` to the whole real line by extending it
constantly past each endpoint. Equal to the original on `Icc 0 T`, and continuous
on `ℝ` whenever the original is `ContinuousOn (Icc 0 T)`. -/
private noncomputable def clamp (T : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f (max 0 (min T t))

private lemma clamp_eq_of_mem {T : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) T) : clamp T f t = f t := by
  unfold clamp
  obtain ⟨h0, hT⟩ := ht
  rw [min_eq_right hT, max_eq_right h0]

private lemma continuous_clamp {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 T)) : Continuous (clamp T f) := by
  have hproj : Continuous (fun t : ℝ => max 0 (min T t)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hmem : ∀ t : ℝ, max 0 (min T t) ∈ Set.Icc (0:ℝ) T := fun _ =>
    ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  exact hf.comp_continuous hproj hmem

private lemma integral_clamp_eq {T : ℝ} {f : ℝ → ℝ}
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) :
    ∫ τ in (0:ℝ)..t, clamp T f τ = ∫ τ in (0:ℝ)..t, f τ := by
  have h0t : Set.uIcc (0:ℝ) t ⊆ Set.Icc 0 T := by
    rw [Set.uIcc_of_le ht.1]
    exact Set.Icc_subset_Icc le_rfl ht.2
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  exact clamp_eq_of_mem (h0t hτ)

/-- The primitive `t ↦ ∫₀ᵗ f₀` is continuous when `f₀` is continuous. -/
private lemma primitive_continuous {f₀ : ℝ → ℝ} (hf₀ : Continuous f₀) :
    Continuous (fun t : ℝ => ∫ τ in (0:ℝ)..t, f₀ τ) :=
  intervalIntegral.continuous_primitive (fun _ _ => hf₀.intervalIntegrable _ _) 0

/-- FTC for the primitive of a continuous function. -/
private lemma primitive_hasDerivAt {f₀ : ℝ → ℝ} (hf₀ : Continuous f₀) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ τ in (0:ℝ)..u, f₀ τ) (f₀ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (hf₀.intervalIntegrable _ _)
    hf₀.stronglyMeasurable.stronglyMeasurableAtFilter
    hf₀.continuousAt

set_option linter.unusedVariables false in
/-- **Integral Grönwall inequality.** If `0 ≤ f` is continuous on `[0, T]` and
satisfies `f(t) ≤ A + K · ∫₀ᵗ f` for every `t ∈ [0, T]`, then
`f(t) ≤ A · exp(K t)` on `[0, T]`. -/
theorem integral_gronwall_le
    {T A K : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hK : 0 ≤ K)
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Icc 0 T))
    (hf_nn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ f t)
    (hf_int : ∀ t ∈ Set.Icc (0:ℝ) T,
      f t ≤ A + K * ∫ τ in (0:ℝ)..t, f τ) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t ≤ A * Real.exp (K * t) := by
  -- Work with the clamped function so we have global continuity / integrability.
  set f₀ : ℝ → ℝ := clamp T f with hf₀def
  have hf₀_cont : Continuous f₀ := continuous_clamp hT hf_cont
  have hf₀_int_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      ∫ τ in (0:ℝ)..t, f₀ τ = ∫ τ in (0:ℝ)..t, f τ := fun _ ht => integral_clamp_eq ht
  have hf₀_eq : ∀ t ∈ Set.Icc (0:ℝ) T, f₀ t = f t := fun _ ht => clamp_eq_of_mem ht
  -- The primitive `g(t) := A + K * ∫₀ᵗ f₀`. By FTC, `g'(t) = K · f₀(t)` everywhere.
  set g : ℝ → ℝ := fun t => A + K * ∫ τ in (0:ℝ)..t, f₀ τ with hgdef
  have hg_cont : Continuous g :=
    continuous_const.add (continuous_const.mul (primitive_continuous hf₀_cont))
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (K * f₀ t) t := fun t =>
    ((primitive_hasDerivAt hf₀_cont t).const_mul K).const_add A
  -- On `Icc 0 T` we have `f ≤ g`.
  have hfg : ∀ t ∈ Set.Icc (0:ℝ) T, f t ≤ g t := by
    intro t ht
    have hbd := hf_int t ht
    change f t ≤ A + K * ∫ τ in (0:ℝ)..t, f₀ τ
    rw [hf₀_int_eq t ht]; exact hbd
  -- Slope inequality required by `le_gronwallBound_of_liminf_deriv_right_le`.
  have hslope :
      ∀ t ∈ Set.Ico (0:ℝ) T, ∀ r, K * f₀ t < r →
        ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (g z - g t) < r := by
    intro t _ r hr
    exact (hg_deriv t).hasDerivWithinAt.liminf_right_slope_le hr
  -- Bound on the derivative: `K · f₀(t) ≤ K · g(t) + 0` whenever `t ∈ [0, T]`.
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) T, K * f₀ t ≤ K * g t + 0 := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1, ht.2.le⟩
    have hft : f₀ t ≤ g t := by rw [hf₀_eq t ht']; exact hfg t ht'
    have := mul_le_mul_of_nonneg_left hft hK
    linarith
  -- Initial condition: `g(0) ≤ A`.
  have hg0 : g 0 ≤ A := by
    change A + K * ∫ τ in (0:ℝ)..0, f₀ τ ≤ A
    rw [intervalIntegral.integral_same, mul_zero, add_zero]
  -- Apply the differential Grönwall inequality to `g` with `δ := A, K := K, ε := 0`.
  have hgB : ∀ t ∈ Set.Icc (0:ℝ) T, g t ≤ gronwallBound A K 0 (t - 0) :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f' := fun t => K * f₀ t) hg_cont.continuousOn hslope hg0 hbound
  -- Identify `gronwallBound A K 0 t = A * exp(K · t)`.
  intro t ht
  have hfg_t : f t ≤ g t := hfg t ht
  have hgt : g t ≤ gronwallBound A K 0 (t - 0) := hgB t ht
  have hsim : gronwallBound A K 0 (t - 0) = A * Real.exp (K * t) := by
    rw [gronwallBound_ε0, sub_zero]
  linarith [hgt, hfg_t, hsim.le, hsim.ge]

set_option linter.unusedVariables false in
/-- **Affine integral Grönwall inequality.** If `0 ≤ f` is continuous on `[0, T]`
and satisfies `f(t) ≤ A + B · t + K · ∫₀ᵗ f` for every `t ∈ [0, T]`, then
`f(t) ≤ (A + B · t) · exp(K t)` on `[0, T]`. -/
theorem integral_gronwall_le_affine
    {T A B K : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Icc 0 T))
    (hf_nn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ f t)
    (hf_int : ∀ t ∈ Set.Icc (0:ℝ) T,
      f t ≤ A + B * t + K * ∫ τ in (0:ℝ)..t, f τ) :
    ∀ t ∈ Set.Icc (0:ℝ) T, f t ≤ (A + B * t) * Real.exp (K * t) := by
  -- Same plan: clamp, build primitive, apply differential Grönwall, identify bound.
  set f₀ : ℝ → ℝ := clamp T f with hf₀def
  have hf₀_cont : Continuous f₀ := continuous_clamp hT hf_cont
  have hf₀_int_eq : ∀ t ∈ Set.Icc (0:ℝ) T,
      ∫ τ in (0:ℝ)..t, f₀ τ = ∫ τ in (0:ℝ)..t, f τ := fun _ ht => integral_clamp_eq ht
  have hf₀_eq : ∀ t ∈ Set.Icc (0:ℝ) T, f₀ t = f t := fun _ ht => clamp_eq_of_mem ht
  set g : ℝ → ℝ := fun t => A + B * t + K * ∫ τ in (0:ℝ)..t, f₀ τ with hgdef
  have hg_cont : Continuous g :=
    ((continuous_const.add (continuous_const.mul continuous_id)).add
      (continuous_const.mul (primitive_continuous hf₀_cont)))
  -- Derivative: `g'(t) = B + K · f₀(t)`.
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (B + K * f₀ t) t := by
    intro t
    have h₁ : HasDerivAt (fun u : ℝ => A + B * u) B t := by
      have hBu : HasDerivAt (fun u : ℝ => B * u) B t := by
        simpa using (hasDerivAt_id t).const_mul B
      simpa using hBu.const_add A
    have h₂ : HasDerivAt (fun u : ℝ => K * ∫ τ in (0:ℝ)..u, f₀ τ) (K * f₀ t) t :=
      (primitive_hasDerivAt hf₀_cont t).const_mul K
    simpa [g] using h₁.add h₂
  have hfg : ∀ t ∈ Set.Icc (0:ℝ) T, f t ≤ g t := by
    intro t ht
    have hbd := hf_int t ht
    change f t ≤ A + B * t + K * ∫ τ in (0:ℝ)..t, f₀ τ
    rw [hf₀_int_eq t ht]; exact hbd
  have hslope :
      ∀ t ∈ Set.Ico (0:ℝ) T, ∀ r, B + K * f₀ t < r →
        ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (g z - g t) < r := by
    intro t _ r hr
    exact (hg_deriv t).hasDerivWithinAt.liminf_right_slope_le hr
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) T, B + K * f₀ t ≤ K * g t + B := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) T := ⟨ht.1, ht.2.le⟩
    have hft : f₀ t ≤ g t := by rw [hf₀_eq t ht']; exact hfg t ht'
    have := mul_le_mul_of_nonneg_left hft hK
    linarith
  have hg0 : g 0 ≤ A := by
    change A + B * 0 + K * ∫ τ in (0:ℝ)..0, f₀ τ ≤ A
    rw [intervalIntegral.integral_same, mul_zero, mul_zero, add_zero, add_zero]
  -- Apply differential Grönwall with `δ := A, K := K, ε := B`.
  have hgB : ∀ t ∈ Set.Icc (0:ℝ) T, g t ≤ gronwallBound A K B (t - 0) :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f' := fun t => B + K * f₀ t) hg_cont.continuousOn hslope hg0 hbound
  -- Now compare `gronwallBound A K B t` to `(A + B · t) · exp(K · t)`.
  intro t ht
  have hfg_t : f t ≤ g t := hfg t ht
  have hgt : g t ≤ gronwallBound A K B (t - 0) := hgB t ht
  rw [sub_zero] at hgt
  -- Show `gronwallBound A K B t ≤ (A + B · t) · exp(K · t)`.
  have hbnd_le : gronwallBound A K B t ≤ (A + B * t) * Real.exp (K * t) := by
    by_cases hK0 : K = 0
    · -- `gronwallBound A 0 B t = A + B · t`, and `exp(0) = 1`.
      have hgB_eq : gronwallBound A K B t = A + B * t := by
        simp [gronwallBound_K0, hK0]
      have hexp : Real.exp (K * t) = 1 := by simp [hK0]
      rw [hgB_eq, hexp, mul_one]
    · -- `gronwallBound A K B t = A · exp(Kt) + (B/K) · (exp(Kt) - 1)`.
      have hK_pos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
      have hgB_eq : gronwallBound A K B t = A * Real.exp (K * t)
          + B / K * (Real.exp (K * t) - 1) := by
        rw [gronwallBound_of_K_ne_0 hK0]
      rw [hgB_eq]
      -- Need: A * exp + (B/K) * (exp - 1) ≤ (A + B t) * exp.
      -- Equivalently: (B/K) * (exp - 1) ≤ B * t * exp.
      -- Equivalently: (exp - 1) ≤ K * t * exp  (since B ≥ 0 and K > 0).
      -- Use `add_one_le_exp`: `-Kt + 1 ≤ exp(-Kt)` ⇒ `1 - exp(-Kt) ≤ Kt`.
      have hexp_pos : 0 < Real.exp (K * t) := Real.exp_pos _
      have h_neg : -(K * t) + 1 ≤ Real.exp (-(K * t)) := add_one_le_exp (-(K * t))
      have h_one_sub : 1 - Real.exp (-(K * t)) ≤ K * t := by linarith
      have hexp_inv : Real.exp (-(K * t)) * Real.exp (K * t) = 1 := by
        rw [← Real.exp_add]; simp
      -- Multiply by `exp(K*t) ≥ 0`:
      have hmul : (1 - Real.exp (-(K * t))) * Real.exp (K * t)
          ≤ K * t * Real.exp (K * t) :=
        mul_le_mul_of_nonneg_right h_one_sub hexp_pos.le
      have hLHS : (1 - Real.exp (-(K * t))) * Real.exp (K * t)
          = Real.exp (K * t) - 1 := by
        have : (1 - Real.exp (-(K * t))) * Real.exp (K * t)
            = Real.exp (K * t) - Real.exp (-(K * t)) * Real.exp (K * t) := by ring
        rw [this, hexp_inv]
      rw [hLHS] at hmul
      -- So `exp(Kt) - 1 ≤ K * t * exp(Kt)`. Multiply by `B / K ≥ 0`.
      have hBK_nn : 0 ≤ B / K := div_nonneg hB hK
      have hscaled : B / K * (Real.exp (K * t) - 1)
          ≤ B / K * (K * t * Real.exp (K * t)) :=
        mul_le_mul_of_nonneg_left hmul hBK_nn
      have hsimplify : B / K * (K * t * Real.exp (K * t))
          = B * t * Real.exp (K * t) := by
        field_simp
      rw [hsimplify] at hscaled
      -- Now: `A * exp + (B/K)(exp - 1) ≤ A * exp + B * t * exp = (A + B * t) * exp`.
      have hRHS : (A + B * t) * Real.exp (K * t)
          = A * Real.exp (K * t) + B * t * Real.exp (K * t) := by ring
      linarith
  linarith [hgt, hfg_t, hbnd_le]

end RicciFlower.Analysis.ODE

