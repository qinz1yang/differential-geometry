import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryFold
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryMoves

/-!
# Invariance of the two-cone fold under the generator moves

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3,
with review 21 §4.3, §4.5). The fold `foldMap` is invariant under the deck translations
`(z, s + n)` everywhere (`foldMap_moveTrans_int`), and the model maps satisfy the reflection
rules of the walls: `liftT ∘ ρ₁ = conjPair ∘ liftT` on `patchOne` (wall 1, shift `0`),
`liftT ∘ ρ₂ = conjPair ∘ liftT` on `patchTwo` (wall 2, shift `k₁`),
`tubeOne ∘ ρ₁ = conjPair ∘ tubeOne` on `discOne`; the screws `S₁`, `S₂` act on the tube
coordinates by rotations (`tubeOne_screw`, `tubeTwo_screw`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

variable {σ : ConeShape} (D : σ.FoldData) (n : Numbers)

theorem eC_add_int (t : ℝ) (k : ℤ) : eC (t + k) = eC t := by
  rw [eC_add, eC_int, mul_one]

theorem liftT_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) : liftT D n p' = liftT D n p := by
  unfold liftT
  rw [hz, h2, eC_add_int]

theorem tubeOne_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) : tubeOne D n p' = tubeOne D n p := by
  unfold tubeOne
  rw [hz, h2]
  apply Prod.ext
  · change coneDisc σ.vertexOne (zOf p) * (eC _ : ℂ) = coneDisc σ.vertexOne (zOf p) * (eC _ : ℂ)
    congr 2
    rw [show (n.a₁ : ℝ) * (p 2 + k + betaOne D n (zOf p)) =
      n.a₁ * (p 2 + betaOne D n (zOf p)) + ((n.a₁ * k : ℤ) : ℝ) by push_cast; ring, eC_add_int]
  · change eC _ = eC _
    rw [show (n.p₁ : ℝ) * (p 2 + k + betaOne D n (zOf p)) =
      n.p₁ * (p 2 + betaOne D n (zOf p)) + ((n.p₁ * k : ℤ) : ℝ) by push_cast; ring, eC_add_int]

theorem tubeTwo_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) : tubeTwo D n p' = tubeTwo D n p := by
  unfold tubeTwo
  rw [hz, h2]
  apply Prod.ext
  · change exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) * (eC _ : ℂ) =
      exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) * (eC _ : ℂ)
    congr 2
    rw [show (n.a₂ : ℝ) * (p 2 + k + betaTwo D n (zOf p)) =
      n.a₂ * (p 2 + betaTwo D n (zOf p)) + ((n.a₂ * k : ℤ) : ℝ) by push_cast; ring, eC_add_int]
  · change eC _ = eC _
    rw [show (n.p₂ : ℝ) * (p 2 + k + betaTwo D n (zOf p)) =
      n.p₂ * (p 2 + betaTwo D n (zOf p)) + ((n.p₂ * k : ℤ) : ℝ) by push_cast; ring, eC_add_int]

theorem flip_congr {c : ℝ} {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) :
    zOf (flipMap c p') = zOf (flipMap c p) ∧ flipMap c p' 2 = flipMap c p 2 + ((-k : ℤ) : ℝ) := by
  refine ⟨by rw [coe_logPoint_flipMap, coe_logPoint_flipMap, hz], ?_⟩
  rw [flipMap_two, flipMap_two, h2]
  push_cast
  ring

theorem liftS_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) : liftS D n p' = liftS D n p := by
  obtain ⟨h1, h2'⟩ := flip_congr (c := n.c₀) hz k h2
  unfold liftS
  rw [liftT_congr D n h1 (-k) h2']

theorem tubeOneS_congr {p p' : ModelCoordinates} (hz : zOf p' = zOf p) (k : ℤ)
    (h2 : p' 2 = p 2 + k) : tubeOneS D n p' = tubeOneS D n p := by
  obtain ⟨h1, h2'⟩ := flip_congr (c := n.c₀) hz k h2
  unfold tubeOneS
  rw [tubeOne_congr D n h1 (-k) h2']

theorem liftT_rhoOne {p : ModelCoordinates} (hV : zOf p ∈ D.V 1) (hre : 3 / 2 < (D.f (zOf p)).re) :
    liftT D n (rhoOne σ p) = conjPair (liftT D n p) := by
  unfold liftT conjPair
  rw [zOf_rhoOne, rhoOne_two, D.f_refl 1 _ hV, basePhase_conj_of_gt _ _ hre, eC_neg, mul_inv]

theorem liftT_rhoTwo {p : ModelCoordinates} (hV : zOf p ∈ D.V 2)
    (hre1 : -(3 / 2) < (D.f (zOf p)).re) (hre2 : (D.f (zOf p)).re < 3 / 2) :
    liftT D n (rhoTwo σ n.k₁ p) = conjPair (liftT D n p) := by
  have hp : 0 < (zOf p).im := D.im_pos_of_mem_V hV
  unfold liftT conjPair
  rw [zOf_rhoTwo σ _ p hp, rhoTwo_two, D.f_refl 2 _ hV, basePhase_conj_of_mid _ _ hre1 hre2]
  congr 1
  rw [mul_inv, eC, eC, ← mul_assoc, ← Circle.exp_add, ← Circle.exp_neg]
  congr 2
  ring

theorem betaOne_refl_one {z : ℂ} (hV : z ∈ D.V 1) (hre : -(3 / 2) < (D.f z).re) :
    betaOne D n (σ.refl 1 z) = -betaOne D n z := by
  unfold betaOne
  rw [D.f_refl 1 z hV, phaseArg_conj_of_lt hre]
  ring

theorem tubeOne_rhoOne {p : ModelCoordinates} (hV : zOf p ∈ D.V 1)
    (hre : -(3 / 2) < (D.f (zOf p)).re) :
    tubeOne D n (rhoOne σ p) = conjPair (tubeOne D n p) := by
  unfold tubeOne conjPair
  rw [zOf_rhoOne, rhoOne_two, betaOne_refl_one D n hV hre, σ.coneDisc_vertexOne_refl_one]
  apply Prod.ext
  · change conj (coneDisc σ.vertexOne (zOf p)) * (eC _ : ℂ) =
      conj (coneDisc σ.vertexOne (zOf p) * (eC _ : ℂ))
    rw [map_mul, ← Circle.coe_inv_eq_conj, ← eC_neg]
    congr 3
    ring
  · change eC _ = (eC _)⁻¹
    rw [← eC_neg]
    congr 1
    ring

variable {n}

theorem exp_mul_I_eq_circle (t : ℝ) : exp ((t : ℂ) * I) = (Circle.exp t : ℂ) :=
  (Circle.coe_exp t).symm

theorem coneDisc_rot_one {z : ℂ} (hz : 0 < z.im) :
    coneDisc σ.vertexOne (σ.refl 1 (σ.refl 2 z)) =
      exp (((-2 * σ.θ₁ : ℝ) : ℂ) * I) * coneDisc σ.vertexOne z := by
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [σ.coneDisc_vertexOne_refl_one, σ.coneDisc_vertexOne_refl_two hc, map_mul,
    Complex.conj_conj, ← exp_conj]
  congr 2
  simp only [map_mul, conj_I, conj_ofReal, map_ofNat]
  push_cast
  ring

theorem tubeOne_screw (hθ₁ : σ.θ₁ * n.p₁ = Real.pi) (hb₁ : (n.p₁ : ℤ) * n.b₁ - n.a₁ * n.q₁ = 1)
    {p : ModelCoordinates} (hd : zOf p ∈ discOne D hθ₁)
    (hd' : zOf (rhoOne σ (rhoTwo σ n.k₁ p)) ∈ discOne D hθ₁) :
    tubeOne D n (rhoOne σ (rhoTwo σ n.k₁ p)) = tubeOne D n p := by
  have hz : zOf (rhoOne σ (rhoTwo σ n.k₁ p)) = σ.refl 1 (σ.refl 2 (zOf p)) := by
    rw [zOf_rhoOne, zOf_rhoTwo σ _ p hd.1]
  have h2 : rhoOne σ (rhoTwo σ n.k₁ p) 2 = p 2 - n.k₁ := by
    rw [rhoOne_two, rhoTwo_two]; ring
  have hrot := coneDisc_rot_one hd.1 (σ := σ)
  have hp0 : (n.p₁ : ℝ) ≠ 0 := by exact_mod_cast p₁_ne_zero hθ₁
  have hθ : σ.θ₁ = Real.pi / n.p₁ := by rw [← hθ₁, mul_div_cancel_right₀ _ hp0]
  have hf : D.f (zOf (rhoOne σ (rhoTwo σ n.k₁ p))) = D.f (zOf p) := by
    rw [(radiusOne_spec D hθ₁ hd'.1 hd'.2).2.1, (radiusOne_spec D hθ₁ hd.1 hd.2).2.1, hz,
      coneApexOne, coneApexOne, hrot, mul_pow, ← exp_nat_mul]
    have hp0' : (n.p₁ : ℂ) ≠ 0 := by exact_mod_cast hp0
    have : (n.p₁ : ℂ) * (((-2 * σ.θ₁ : ℝ) : ℂ) * I) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [hθ]; push_cast; field_simp
    rw [this, exp_int_mul_two_pi_mul_I, one_mul]
  have hβ : betaOne D n (zOf (rhoOne σ (rhoTwo σ n.k₁ p))) = betaOne D n (zOf p) := by
    unfold betaOne; rw [hf]
  have hk := kOne_mul hθ₁
  unfold tubeOne
  rw [hβ, h2]
  apply Prod.ext
  · change coneDisc σ.vertexOne (zOf (rhoOne σ (rhoTwo σ n.k₁ p))) * (eC _ : ℂ) =
      coneDisc σ.vertexOne (zOf p) * (eC _ : ℂ)
    rw [hz, hrot, exp_mul_I_eq_circle, mul_comm, ← mul_assoc, ← Circle.coe_mul, eC, eC,
      ← Circle.exp_add, mul_comm]
    congr 2
    have hb' : (n.p₁ : ℝ) * n.b₁ - n.a₁ * n.q₁ = 1 := by exact_mod_cast hb₁
    have : 2 * Real.pi * (n.a₁ * (p 2 - n.k₁ + betaOne D n (zOf p))) + -2 * σ.θ₁ =
        2 * Real.pi * (n.a₁ * (p 2 + betaOne D n (zOf p))) + ((-n.b₁ : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hθ, Numbers.k₁]
      push_cast
      field_simp
      linear_combination hb'
    rw [this, Circle.exp_add _ ((-n.b₁ : ℤ) * (2 * Real.pi) : ℝ), Circle.exp_int_mul_two_pi,
      mul_one]
  · change eC _ = eC _
    rw [show (n.p₁ : ℝ) * (p 2 - n.k₁ + betaOne D n (zOf p)) =
      n.p₁ * (p 2 + betaOne D n (zOf p)) + ((-n.q₁ : ℤ) : ℝ) by push_cast; linear_combination -hk,
      eC_add_int]

theorem coneDisc_rot_two {z : ℂ} (hz : 0 < z.im) :
    coneDisc σ.vertexTwo (σ.refl 2 (σ.refl 0 z)) =
      exp (((-2 * σ.θ₂ : ℝ) : ℂ) * I) * coneDisc σ.vertexTwo z := by
  have hz0 : 0 < (σ.refl 0 z).im := σ.refl_im_pos hz 0
  have hc : σ.refl 0 z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [σ.coneDisc_vertexTwo_refl_two hc, σ.coneDisc_vertexTwo_refl_zero, Complex.conj_conj]
  congr 1
  rw [show 2 * (((Real.pi - σ.θ₂ : ℝ)) : ℂ) * I = ((-2 * σ.θ₂ : ℝ) : ℂ) * I + 2 * Real.pi * I by
    push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]

theorem tubeTwo_screw (hθ₂ : σ.θ₂ * n.p₂ = Real.pi) (hb₂ : (n.p₂ : ℤ) * n.b₂ - n.a₂ * n.q₂ = 1)
    {p : ModelCoordinates} (hd : zOf p ∈ discTwo D hθ₂)
    (hd' : zOf (rhoTwo σ n.k₁ (rhoZero n.c₀ p)) ∈ discTwo D hθ₂) :
    tubeTwo D n (rhoTwo σ n.k₁ (rhoZero n.c₀ p)) = tubeTwo D n p := by
  have hz : zOf (rhoTwo σ n.k₁ (rhoZero n.c₀ p)) = σ.refl 2 (σ.refl 0 (zOf p)) := by
    rw [zOf_rhoTwo σ _ _ (by rw [zOf_rhoZero]; exact σ.refl_im_pos hd.1 0), zOf_rhoZero]
  have h2 : rhoTwo σ n.k₁ (rhoZero n.c₀ p) 2 = p 2 - n.k₂ := by
    rw [rhoTwo_two, rhoZero_two, Numbers.c₀]; ring
  have hrot := coneDisc_rot_two hd.1 (σ := σ)
  have hp0 : (n.p₂ : ℝ) ≠ 0 := by exact_mod_cast p₂_ne_zero hθ₂
  have hθ : σ.θ₂ = Real.pi / n.p₂ := by rw [← hθ₂, mul_div_cancel_right₀ _ hp0]
  have hf : D.f (zOf (rhoTwo σ n.k₁ (rhoZero n.c₀ p))) = D.f (zOf p) := by
    rw [(radiusTwo_spec D hθ₂ hd'.1 hd'.2).2.1, (radiusTwo_spec D hθ₂ hd.1 hd.2).2.1, hz,
      coneApexTwo, coneApexTwo, hrot, mul_pow, ← exp_nat_mul]
    have hp0' : (n.p₂ : ℂ) ≠ 0 := by exact_mod_cast hp0
    have : (n.p₂ : ℂ) * (((-2 * σ.θ₂ : ℝ) : ℂ) * I) = ((-1 : ℤ) : ℂ) * (2 * Real.pi * I) := by
      rw [hθ]; push_cast; field_simp
    rw [this, exp_int_mul_two_pi_mul_I, one_mul]
  have hβ : betaTwo D n (zOf (rhoTwo σ n.k₁ (rhoZero n.c₀ p))) = betaTwo D n (zOf p) := by
    unfold betaTwo; rw [hf]
  have hk := kTwo_mul hθ₂
  unfold tubeTwo
  rw [hβ, h2]
  apply Prod.ext
  · change exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf (rhoTwo σ n.k₁ (rhoZero n.c₀ p))) *
      (eC _ : ℂ) = exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf p) * (eC _ : ℂ)
    have key : Circle.exp (-2 * σ.θ₂) * eC (n.a₂ * (p 2 - n.k₂ + betaTwo D n (zOf p))) =
        eC (n.a₂ * (p 2 + betaTwo D n (zOf p))) := by
      rw [eC, eC, ← Circle.exp_add]
      have hb' : (n.p₂ : ℝ) * n.b₂ - n.a₂ * n.q₂ = 1 := by exact_mod_cast hb₂
      have : -2 * σ.θ₂ + 2 * Real.pi * (n.a₂ * (p 2 - n.k₂ + betaTwo D n (zOf p))) =
          2 * Real.pi * (n.a₂ * (p 2 + betaTwo D n (zOf p))) +
            ((-n.b₂ : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hθ, Numbers.k₂]
        push_cast
        field_simp
        linear_combination hb'
      rw [this, Circle.exp_add _ ((-n.b₂ : ℤ) * (2 * Real.pi) : ℝ), Circle.exp_int_mul_two_pi,
        mul_one]
    rw [hz, hrot, exp_mul_I_eq_circle (-2 * σ.θ₂), ← key, Circle.coe_mul]
    ring
  · change eC _ = eC _
    rw [show (n.p₂ : ℝ) * (p 2 - n.k₂ + betaTwo D n (zOf p)) =
      n.p₂ * (p 2 + betaTwo D n (zOf p)) + ((-n.q₂ : ℤ) : ℝ) by push_cast; linear_combination -hk,
      eC_add_int]

end Fold

end TwoConeFold

end GC.Seifert
