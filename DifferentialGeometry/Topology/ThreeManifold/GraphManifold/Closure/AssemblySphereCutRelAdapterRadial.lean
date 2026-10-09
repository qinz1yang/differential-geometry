import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelNeck
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlaceBox

/-!
# Chapter-14 assembly, relative COMPARE side adapters (d): the radial reparametrization of a tube

Lane ASM-L2f, group G1. Drilling a second fibre shrinks the radial port of the first drilled tube:
its collar becomes `(τ, s) ↦ φ ((1 + δ s / 2) w, θ)`. To present it again in the standard form
`(τ, s) ↦ φ' ((1 + s / 2) w, θ)`, the tube is reparametrized by a radial diffeomorphism of the plane
factor which is the identity near the axis and `ρ ↦ 1 + δ (ρ - 1)` for `ρ ≥ 1/2`.

* `exists_tubeRadialProfile`: the profile (from the neck profile G3, `exists_neckProfile`) and its
  inverse.
* `innerRadialMap` (`_eq_smul`, `_zero`, `contDiff_innerRadialMap`, `norm_innerRadialMap`,
  `innerRadialMap_innerRadialMap`): the radial map of a profile in a real inner product space.
* `exists_tubeRadial`: the reparametrization of `PlaneLift × Circle`, with its norm and band
  properties.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The radial profile.** For `0 < δ ≤ 1`, a smooth strictly increasing bijection of the line
with smooth inverse, the identity on `(-∞, 1/4]` and `ρ ↦ 1 + δ (ρ - 1)` on `[1/2, ∞)`. -/
theorem exists_tubeRadialProfile {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ f g : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ StrictMono f ∧ (∀ ρ, g (f ρ) = ρ) ∧
      (∀ y, f (g y) = y) ∧ (∀ ρ, ρ ≤ 1 / 4 → f ρ = ρ) ∧ (∀ ρ, ρ ≤ 1 / 4 → g ρ = ρ) ∧
      ∀ ρ, 1 / 2 ≤ ρ → f ρ = 1 + δ * (ρ - 1) := by
  have hgap : |δ - 1| * (1 / 8) ≤ (1 - 5 * δ / 8) - 3 / 8 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  obtain ⟨h, hmono, h0, h1⟩ := exists_neckProfile (a := 1 / 8) (m₀ := δ) (m₁ := 1)
    (c₀ := 1 - 5 * δ / 8) (c₁ := 3 / 8) (by norm_num) hδ one_pos hgap
  have hf : ∀ ρ, ρ ≤ 1 / 4 → h (ρ - 3 / 8) = ρ := by
    intro ρ hρ
    rw [h1 _ (by linarith)]
    ring
  refine ⟨fun ρ => h (ρ - 3 / 8), fun y => h.symm y + 3 / 8,
    (contMDiff_iff_contDiff.mp h.contMDiff).comp (contDiff_id.sub contDiff_const),
    (contMDiff_iff_contDiff.mp h.symm.contMDiff).add contDiff_const,
    fun a b hab => hmono (by linarith), ?_, ?_, hf, ?_, ?_⟩
  · intro ρ
    change h.symm (h (ρ - 3 / 8)) + 3 / 8 = ρ
    rw [Diffeomorph.symm_apply_apply]
    ring
  · intro y
    change h (h.symm y + 3 / 8 - 3 / 8) = y
    rw [add_sub_cancel_right, Diffeomorph.apply_symm_apply]
  · intro ρ hρ
    change h.symm ρ + 3 / 8 = ρ
    conv_lhs => rw [← hf ρ hρ, Diffeomorph.symm_apply_apply]
    ring
  · intro ρ hρ
    change h (ρ - 3 / 8) = _
    rw [h0 _ (by linarith)]
    ring

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial map of a profile `f`: `x ↦ x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x`. -/
def innerRadialMap (f : ℝ → ℝ) (x : E) : E :=
  x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x

theorem innerRadialMap_eq_smul (f : ℝ → ℝ) {x : E} (hx : x ≠ 0) :
    innerRadialMap f x = (f ‖x‖ / ‖x‖) • x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h : x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x = (1 + (f ‖x‖ - ‖x‖) / ‖x‖) • x := by
    rw [add_smul, one_smul]
  rw [innerRadialMap, h]
  congr 1
  field_simp
  ring

theorem innerRadialMap_zero (f : ℝ → ℝ) : innerRadialMap f (0 : E) = 0 := by
  simp [innerRadialMap]

theorem contDiff_innerRadialMap {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a)
    (hfa : ∀ r, r < a → f r = r) : ContDiff ℝ ∞ (innerRadialMap (E := E) f) := by
  have hs : ContDiff ℝ ∞ (fun x : E => (f ‖x‖ - ‖x‖) / ‖x‖) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < a
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      rw [hfa ‖y‖ hy, sub_self, zero_div]
    · have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx
        exact hx ha
      have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx0
      exact ((hf.contDiffAt.comp x hn).sub hn).div hn (norm_ne_zero_iff.mpr hx0)
  exact contDiff_id.add (hs.smul contDiff_id)

theorem norm_innerRadialMap {f : ℝ → ℝ} (hf0 : f 0 = 0) (hf : ∀ r, 0 < r → 0 < f r) (x : E) :
    ‖innerRadialMap f x‖ = f ‖x‖ := by
  by_cases hx : x = 0
  · rw [hx, innerRadialMap_zero, norm_zero, hf0]
  · rw [innerRadialMap_eq_smul f hx, norm_smul]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [Real.norm_of_nonneg (div_nonneg (hf _ hn).le hn.le)]
    field_simp

theorem innerRadialMap_innerRadialMap {f g : ℝ → ℝ} (hg : ∀ r, 0 < r → 0 < g r)
    (hfg : ∀ r, 0 < r → f (g r) = r) (x : E) :
    innerRadialMap f (innerRadialMap g x) = x := by
  by_cases hx : x = 0
  · rw [hx, innerRadialMap_zero, innerRadialMap_zero]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hgx : innerRadialMap g x ≠ 0 := by
      rw [innerRadialMap_eq_smul g hx]
      exact smul_ne_zero (div_pos (hg _ hn) hn).ne' hx
    have hng : ‖innerRadialMap g x‖ = g ‖x‖ := by
      rw [innerRadialMap_eq_smul g hx, norm_smul,
        Real.norm_of_nonneg (div_nonneg (hg _ hn).le hn.le)]
      field_simp
    rw [innerRadialMap_eq_smul f hgx, hng, innerRadialMap_eq_smul g hx, smul_smul, hfg _ hn]
    have hgp := hg _ hn
    rw [show ‖x‖ / g ‖x‖ * (g ‖x‖ / ‖x‖) = 1 by field_simp, one_smul]

end Radial

/-- **The radial reparametrization of a tube.** For `0 < δ ≤ 1`, a diffeomorphism `Λ` of
`PlaneLift × Circle` over the circle factor which preserves the open and the closed unit tube and
the closed radius-three tube, and carries the radial band `((1 + s/2) w, θ)` (`s ≥ 0`, `|w| = 1`)
to `((1 + δ s/2) w, θ)`. -/
theorem exists_tubeRadial {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ Λ : (PlaneLift.{u} × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), 𝓘(ℝ, ℂ).prod (𝓡 1)⟯
        (PlaneLift.{u} × Circle),
      (∀ p, (Λ p).2 = p.2) ∧ (∀ p, ‖(Λ p).1.down‖ < 1 ↔ ‖p.1.down‖ < 1) ∧
      (∀ p, ‖(Λ p).1.down‖ ≤ 1 ↔ ‖p.1.down‖ ≤ 1) ∧
      (∀ p, ‖p.1.down‖ ≤ 3 → ‖(Λ p).1.down‖ ≤ 3) ∧
      ∀ (w θ : Circle) (s : ℝ), 0 ≤ s →
        Λ (ULift.up ((1 + s / 2) • (w : ℂ)), θ) = (ULift.up ((1 + δ * s / 2) • (w : ℂ)), θ) := by
  obtain ⟨f, g, hf, hg, hmono, hgf, hfg, hf4, hg4, hfb⟩ := exists_tubeRadialProfile hδ hδ1
  have hf0 : f 0 = 0 := hf4 0 (by norm_num)
  have hfpos : ∀ r, 0 < r → 0 < f r := fun r hr => hf0 ▸ hmono hr
  have hgmono : StrictMono g := by
    intro a b hab
    by_contra h
    have h' := hmono.monotone (not_lt.mp h)
    rw [hfg, hfg] at h'
    linarith
  have hg0 : g 0 = 0 := hg4 0 (by norm_num)
  have hgpos : ∀ r, 0 < r → 0 < g r := fun r hr => hg0 ▸ hgmono hr
  have hsmooth : ∀ k : ℝ → ℝ, ContDiff ℝ ∞ k → (∀ r, r < 1 / 4 → k r = r) →
      ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
        (fun p : PlaneLift.{u} × Circle => (ULift.up (innerRadialMap k p.1.down), p.2)) :=
    fun k hk hk4 => (contMDiff_planeLift_up.comp
      ((contDiff_innerRadialMap hk (by norm_num : (0 : ℝ) < 1 / 4) hk4).contMDiff.comp
        (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk contMDiff_snd
  let Λ : (PlaneLift.{u} × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1), 𝓘(ℝ, ℂ).prod (𝓡 1)⟯
      (PlaneLift.{u} × Circle) :=
    { toFun := fun p => (ULift.up (innerRadialMap f p.1.down), p.2)
      invFun := fun p => (ULift.up (innerRadialMap g p.1.down), p.2)
      left_inv := fun p => by
        apply Prod.ext
        · apply ULift.ext
          exact innerRadialMap_innerRadialMap hfpos (fun r _ => hgf r) p.1.down
        · rfl
      right_inv := fun p => by
        apply Prod.ext
        · apply ULift.ext
          exact innerRadialMap_innerRadialMap hgpos (fun r _ => hfg r) p.1.down
        · rfl
      contMDiff_toFun := hsmooth f hf fun r hr => hf4 r hr.le
      contMDiff_invFun := hsmooth g hg fun r hr => hg4 r hr.le }
  have hnorm : ∀ p : PlaneLift.{u} × Circle, ‖(Λ p).1.down‖ = f ‖p.1.down‖ :=
    fun p => norm_innerRadialMap hf0 hfpos p.1.down
  have hf1 : f 1 = 1 := by
    rw [hfb 1 (by norm_num)]
    ring
  refine ⟨Λ, fun p => rfl, fun p => ?_, fun p => ?_, fun p hp => ?_, fun w θ s hs => ?_⟩
  · rw [hnorm]
    conv_lhs => rw [← hf1]
    exact hmono.lt_iff_lt
  · rw [hnorm]
    conv_lhs => rw [← hf1]
    exact hmono.le_iff_le
  · rw [hnorm]
    have h3 : f 3 = 1 + 2 * δ := by
      rw [hfb 3 (by norm_num)]
      ring
    have := hmono.monotone hp
    linarith
  · have hw : ‖(w : ℂ)‖ = 1 := Circle.norm_coe w
    have hpos : 0 < 1 + s / 2 := by linarith
    have hx : ((1 + s / 2) • (w : ℂ)) ≠ 0 := by
      refine smul_ne_zero hpos.ne' ?_
      intro h
      rw [h, norm_zero] at hw
      exact zero_ne_one hw
    have hnx : ‖(1 + s / 2) • (w : ℂ)‖ = 1 + s / 2 := by
      rw [norm_smul, hw, mul_one, Real.norm_of_nonneg hpos.le]
    apply Prod.ext
    · apply ULift.ext
      change innerRadialMap f ((1 + s / 2) • (w : ℂ)) = (1 + δ * s / 2) • (w : ℂ)
      rw [innerRadialMap_eq_smul f hx, hnx, hfb _ (by linarith), smul_smul]
      congr 1
      field_simp
      ring
    · rfl

end GC.GraphManifold.Assembly
