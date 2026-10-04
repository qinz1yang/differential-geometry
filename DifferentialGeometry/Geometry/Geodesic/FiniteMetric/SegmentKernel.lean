import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Direction kernel for short metric segments

If a curve `ξ` in a normed space has `G(ξ h, ξ h) = h²` for a coercive symmetric form `G`, and a
function `R` with `R(0) = τ²`, `dR(0) = 2 G(V, ·)`, `G(V, V) = τ²` takes the values
`R(ξ h) = (τ + h)²`, then `ξ` is differentiable at `0` with derivative `V / τ`
(`hasDerivAt_of_quadratic_radial`). This is the infinitesimal form of the equality case of the
Gauss-lemma inequality: a curve moving at unit speed whose radial distance grows at unit rate moves
radially.
-/

set_option autoImplicit false

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Segment direction kernel.** -/
theorem hasDerivAt_of_quadratic_radial {G : E →L[ℝ] E →L[ℝ] ℝ} (hsym : ∀ u w, G u w = G w u)
    {c : ℝ} (hc : 0 < c) (hcoer : ∀ u, c * ‖u‖ * ‖u‖ ≤ G u u)
    {ξ : ℝ → E} {V : E} {τ : ℝ} (hτ : 0 < τ) (hV : G V V = τ ^ 2)
    {R : E → ℝ} (hR : HasFDerivAt R ((2 : ℝ) • G V) 0) (hR0 : R 0 = τ ^ 2)
    (hξ : ∀ᶠ h in 𝓝 (0 : ℝ), G (ξ h) (ξ h) = h ^ 2 ∧ R (ξ h) = (τ + h) ^ 2) :
    HasDerivAt ξ (τ⁻¹ • V) 0 := by
  have hnorm_sq : ∀ u : E, c * ‖u‖ ^ 2 ≤ G u u := fun u => by nlinarith [hcoer u]
  -- `ξ 0 = 0`
  have hξ0 : ξ 0 = 0 := by
    have h := (hξ.self_of_nhds).1
    have h1 := hnorm_sq (ξ 0)
    rw [h] at h1
    have : ‖ξ 0‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖ξ 0‖ = 0 := by nlinarith [norm_nonneg (ξ 0)]
    exact norm_eq_zero.mp this
  -- `ξ = O(h)`
  have hO : ξ =O[𝓝 0] fun h : ℝ => h := by
    refine IsBigO.of_bound (Real.sqrt (1 / c)) ?_
    filter_upwards [hξ] with h hh
    have h1 : ‖ξ h‖ ^ 2 ≤ (Real.sqrt (1 / c) * ‖h‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.norm_eq_abs, sq_abs]
      have := hnorm_sq (ξ h)
      rw [hh.1] at this
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h1
  have htend : Tendsto ξ (𝓝 0) (𝓝 0) := hO.trans_tendsto tendsto_id
  -- the radial identity to first order
  have hRo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hR).comp_tendsto htend
  have hA : (fun h : ℝ => τ * h - G V (ξ h)) =o[𝓝 0] fun h : ℝ => h := by
    have h1 := hRo.trans_isBigO hO
    have h2 : (fun h : ℝ => h ^ 2) =o[𝓝 0] fun h : ℝ => h := by
      simpa using (isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))
    have h3 := (h1.sub h2).const_mul_left (1 / 2 : ℝ)
    refine h3.congr' ?_ EventuallyEq.rfl
    filter_upwards [hξ] with h hh
    simp only [Function.comp_apply, zero_add, hR0, hh.2, smul_apply,
      smul_eq_mul]
    ring
  -- the defect
  set N : E := τ⁻¹ • V with hN
  set D : ℝ → E := fun h => ξ h - h • N with hD
  have hGD : ∀ᶠ h in 𝓝 (0 : ℝ), G (D h) (D h) = 2 * τ⁻¹ * h * (τ * h - G V (ξ h)) := by
    filter_upwards [hξ] with h hh
    simp only [hD, hN, map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul]
    rw [hh.1, hV, hsym (ξ h) V]
    field_simp
    ring
  have hGDo : (fun h : ℝ => G (D h) (D h)) =o[𝓝 0] fun h : ℝ => h * h := by
    have h1 : (fun h : ℝ => 2 * τ⁻¹ * h) =O[𝓝 0] fun h : ℝ => h :=
      (isBigO_refl (fun h : ℝ => h) _).const_mul_left (2 * τ⁻¹) |>.congr_left
        (fun h => by ring)
    exact (h1.mul_isLittleO hA).congr' (hGD.mono fun h hh => hh.symm) EventuallyEq.rfl
  -- conclusion
  have hDo : D =o[𝓝 0] fun h : ℝ => h := by
    refine isLittleO_iff.mpr fun ε hε => ?_
    have hb := isLittleO_iff.mp hGDo (show 0 < c * ε ^ 2 by positivity)
    filter_upwards [hb] with h hh
    have h1 := hnorm_sq (D h)
    have h2 : c * ‖D h‖ ^ 2 ≤ c * (ε * ‖h‖) ^ 2 := by
      have := le_abs_self (G (D h) (D h))
      have hh' : |G (D h) (D h)| ≤ c * ε ^ 2 * (‖h‖ * ‖h‖) := by rwa [norm_mul] at hh
      nlinarith
    have h3 : ‖D h‖ ^ 2 ≤ (ε * ‖h‖) ^ 2 := le_of_mul_le_mul_left h2 hc
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp h3
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine hDo.congr_left (fun h => ?_)
  simp only [hD, zero_add, hξ0, sub_zero]

end Bundle.ContMDiffRiemannianMetric
