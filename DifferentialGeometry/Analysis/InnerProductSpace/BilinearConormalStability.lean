import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LC40 for bilinear forms: the tangent-metric binding of conormal stability

The kernel `ContinuousLinearMap.dual_apply_inverse_pos` (`PositiveInverseBounds.lean`) proves
blueprint LC40 (master207A:21751) on a Hilbert space with a positive operator. Here the same
inequality is proved for the data that a Riemannian manifold actually supplies at one point:
two symmetric bilinear forms `G` (the metric `g`) and `Hf` (another metric `h`, for instance a
pullback), the `G`-representer `b` of the covector `β` (so `‖β‖_{g*}² = G b b`), and an
`Hf`-representer `w` of `ξ` (this is `h⁻¹ξ`). The dual-norm error is stated as
`|ξ v - β v| ≤ σ √(G v v)` for all `v`.

The proof is elementary: Cauchy–Schwarz for positive semidefinite forms and, in finite
dimensions, the existence of the `Hf`-representer of `β`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace DifferentialGeometry.BilinearConormal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cauchy–Schwarz for a symmetric positive semidefinite bilinear form. -/
theorem sq_apply_le_mul (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    (hnonneg : ∀ v, 0 ≤ B v v) (u v : V) :
    (B u v) ^ 2 ≤ B u u * B v v := by
  have h : ∀ t : ℝ, 0 ≤ B v v * (t * t) + 2 * B u v * t + B u u := by
    intro t
    have h0 := hnonneg (u + t • v)
    simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      hsymm v u] at h0
    nlinarith [h0]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

/-- Cauchy–Schwarz in square-root form. -/
theorem abs_apply_le_sqrt_mul_sqrt (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ u v, B u v = B v u)
    (hnonneg : ∀ v, 0 ≤ B v v) (u v : V) :
    |B u v| ≤ √(B u u) * √(B v v) := by
  rw [← Real.sqrt_mul (hnonneg u), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_mul B hsymm hnonneg u v)

/-- A bilinear form bounded below by a positive definite form is surjective onto the dual
in finite dimensions: every covector has an `Hf`-representer. -/
theorem exists_representer [FiniteDimensional ℝ V] (G Hf : V →L[ℝ] V →L[ℝ] ℝ)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) {δ : ℝ} (hδ1 : δ < 1)
    (hlower : ∀ v, (1 - δ) * G v v ≤ Hf v v) (β : V →L[ℝ] ℝ) :
    ∃ w : V, Hf w = β := by
  have hinj : Function.Injective (Hf : V →ₗ[ℝ] V →L[ℝ] ℝ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hz : Hf v v = 0 := by
      change (Hf : V →ₗ[ℝ] V →L[ℝ] ℝ) v v = 0
      rw [hv]
      rfl
    have h1 := hlower v
    have h2 := hGpos v hne
    rw [hz] at h1
    nlinarith
  have hrank : Module.finrank ℝ V = Module.finrank ℝ (V →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).finrank_eq,
      Module.finrank_linearMap_self]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj β

/-- LC40, bilinear-form version: quantitative lower bound for `β (h⁻¹ ξ)`. -/
theorem le_apply_representer [FiniteDimensional ℝ V] (G Hf : V →L[ℝ] V →L[ℝ] ℝ)
    (hGsymm : ∀ u v, G u v = G v u) (hHsymm : ∀ u v, Hf u v = Hf v u)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) {δ σ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlower : ∀ v, (1 - δ) * G v v ≤ Hf v v) (hupper : ∀ v, Hf v v ≤ (1 + δ) * G v v)
    (β ξ : V →L[ℝ] ℝ) {b w : V} (hb : G b = β) (hw : Hf w = ξ)
    (herror : ∀ v, |ξ v - β v| ≤ σ * √(G v v)) :
    G b b / (1 + δ) - σ * √(G b b) / (1 - δ) ≤ β w := by
  have hGnn : ∀ v, 0 ≤ G v v := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hGpos v hv).le
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  have hHnn : ∀ v, 0 ≤ Hf v v := fun v =>
    le_trans (mul_nonneg hm.le (hGnn v)) (hlower v)
  obtain ⟨w₁, hw₁⟩ := exists_representer G Hf hGpos hδ1 hlower β
  set w₂ := w - w₁ with hw₂def
  have hsplit : β w = β w₁ + β w₂ := by rw [hw₂def, map_sub]; ring
  -- main term
  have hmain : G b b / (1 + δ) ≤ β w₁ := by
    have hββ : Hf w₁ b = G b b := by rw [hw₁, ← hb]
    have hw₁w₁ : Hf w₁ w₁ = β w₁ := by rw [hw₁]
    have hcs := sq_apply_le_mul Hf hHsymm hHnn w₁ b
    rw [hββ, hw₁w₁] at hcs
    have hup := hupper b
    have hβnn : 0 ≤ β w₁ := hw₁w₁ ▸ hHnn w₁
    rw [div_le_iff₀ hp]
    by_cases hbb : G b b = 0
    · rw [hbb]
      nlinarith
    · have hbpos : 0 < G b b := lt_of_le_of_ne (hGnn b) (Ne.symm hbb)
      have h1 : G b b ^ 2 ≤ β w₁ * ((1 + δ) * G b b) :=
        hcs.trans (mul_le_mul_of_nonneg_left hup hβnn)
      nlinarith
  -- error term
  have hσb : 0 ≤ σ * √(G b b) := by
    by_cases hbb : G b b = 0
    · rw [hbb, Real.sqrt_zero, mul_zero]
    · exact (abs_nonneg _).trans (herror b)
  have herr : |β w₂| ≤ σ * √(G b b) / (1 - δ) := by
    have hrep : Hf w₂ = ξ - β := by rw [hw₂def, map_sub, hw, hw₁]
    have hcs := abs_apply_le_sqrt_mul_sqrt G hGsymm hGnn b w₂
    have hbw : G b w₂ = β w₂ := by rw [hb]
    rw [hbw] at hcs
    have hHw₂ : Hf w₂ w₂ ≤ σ * √(G w₂ w₂) := by
      rw [hrep]
      exact (le_abs_self _).trans (herror w₂)
    have hlw := hlower w₂
    rw [le_div_iff₀ hm]
    by_cases hz : G w₂ w₂ = 0
    · have : |β w₂| = 0 := by
        apply le_antisymm _ (abs_nonneg _)
        simpa [hz] using hcs
      rw [this, zero_mul]
      exact hσb
    · have hpos : 0 < √(G w₂ w₂) := Real.sqrt_pos.mpr (lt_of_le_of_ne (hGnn w₂) (Ne.symm hz))
      have hsq : √(G w₂ w₂) ^ 2 = G w₂ w₂ := Real.sq_sqrt (hGnn w₂)
      have hkey : (1 - δ) * √(G w₂ w₂) ≤ σ := by
        have h3 : (1 - δ) * (√(G w₂ w₂) * √(G w₂ w₂)) ≤ σ * √(G w₂ w₂) := by
          nlinarith [hlw, hHw₂, hsq]
        nlinarith
      have hsb := Real.sqrt_nonneg (G b b)
      calc |β w₂| * (1 - δ) ≤ √(G b b) * √(G w₂ w₂) * (1 - δ) :=
            mul_le_mul_of_nonneg_right hcs hm.le
        _ = √(G b b) * ((1 - δ) * √(G w₂ w₂)) := by ring
        _ ≤ √(G b b) * σ := mul_le_mul_of_nonneg_left hkey hsb
        _ = σ * √(G b b) := by ring
  have hneg := neg_abs_le (β w₂)
  linarith

/-- LC40, bilinear-form version: strict positivity of `β (h⁻¹ ξ)` under the strict budget. -/
theorem apply_representer_pos [FiniteDimensional ℝ V] (G Hf : V →L[ℝ] V →L[ℝ] ℝ)
    (hGsymm : ∀ u v, G u v = G v u) (hHsymm : ∀ u v, Hf u v = Hf v u)
    (hGpos : ∀ v, v ≠ 0 → 0 < G v v) {δ σ m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlower : ∀ v, (1 - δ) * G v v ≤ Hf v v) (hupper : ∀ v, Hf v v ≤ (1 + δ) * G v v)
    (β ξ : V →L[ℝ] ℝ) {b w : V} (hb : G b = β) (hw : Hf w = ξ)
    (hmpos : 0 < m) (hβm : m ≤ √(G b b))
    (herror : ∀ v, |ξ v - β v| ≤ σ * √(G v v))
    (hbudget : σ < (1 - δ) / (1 + δ) * m) :
    0 < β w := by
  have hl := le_apply_representer G Hf hGsymm hHsymm hGpos hδ hδ1 hlower hupper β ξ hb hw herror
  have hm : 0 < 1 - δ := by linarith
  have hp : 0 < 1 + δ := by linarith
  set s := √(G b b) with hs
  have hspos : 0 < s := hmpos.trans_le hβm
  have hss : G b b = s ^ 2 := by
    rw [hs, Real.sq_sqrt]
    by_contra hneg
    push Not at hneg
    rw [Real.sqrt_eq_zero'.mpr hneg.le] at hs
    linarith
  rw [hss] at hl
  have hb' : σ * (1 + δ) < (1 - δ) * s := by
    have h1 : σ * (1 + δ) < (1 - δ) * m := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hp] at hbudget
      exact hbudget
    nlinarith
  have hgoal : σ * s / (1 - δ) < s ^ 2 / (1 + δ) := by
    rw [div_lt_div_iff₀ hm hp]
    nlinarith
  linarith

end DifferentialGeometry.BilinearConormal

namespace DifferentialGeometry

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- LC40 at a point of a Riemannian manifold: `g` is the smooth metric, `Hf` a symmetric form on
the same tangent space with `(1-δ) g ≤ Hf ≤ (1+δ) g` (for instance a pullback metric), `b` the
`g`-gradient of `β`, `w` an `Hf`-gradient of `ξ`. -/
theorem SmoothRiemannianMetric.conormal_apply_pos (g : SmoothRiemannianMetric I M) (x : M)
    (Hf : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hHsymm : ∀ u v, Hf u v = Hf v u) {δ σ m : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hlower : ∀ v, (1 - δ) * g.inner x v v ≤ Hf v v)
    (hupper : ∀ v, Hf v v ≤ (1 + δ) * g.inner x v v)
    (β ξ : TangentSpace I x →L[ℝ] ℝ) {b w : TangentSpace I x}
    (hb : g.inner x b = β) (hw : Hf w = ξ)
    (hmpos : 0 < m) (hβm : m ≤ √(g.inner x b b))
    (herror : ∀ v, |ξ v - β v| ≤ σ * √(g.inner x v v))
    (hbudget : σ < (1 - δ) / (1 + δ) * m) :
    0 < β w :=
  BilinearConormal.apply_representer_pos (V := E) (g.inner x) Hf (g.symm x) hHsymm
    (g.pos x) hδ hδ1 hlower hupper β ξ hb hw hmpos hβm herror hbudget

end DifferentialGeometry
