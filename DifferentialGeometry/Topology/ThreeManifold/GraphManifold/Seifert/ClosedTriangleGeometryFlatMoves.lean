import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatSurj
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryRelation

/-!
# The generator moves of a flat closed triangle fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§3, with review 27). For the fold `F = flatMap` on `N = flatDomain` and the model metric, the local
composite relation `FoldRel` holds between a point and its image under each generator move, on an
open piece where the move preserves `F`:
* the deck translations `h^n = fibreTranslation (n ℓ)` on all of `N` (`foldRel_deck`);
* the screws `S₁`, `S₂`, `S₃` on the discs about `v₁`, `v₂`, `0` (`foldRel_screwOne`, ...): the
  tube coordinates rotate by `e^{-2πi/p}` and the fibre coordinate drops by `k = q/p`, which the
  Bézout identity `1 + a q = p b` absorbs (`tube_rot`);
* `S₃` on the disc about `v₁` (it carries the disc to its mirror, where `F = F ∘ S₃⁻¹` by
  definition) and on the wall-1 patch (wall rule `theta_wallOne`);
* `S₂⁻¹` on the wall-2 patch (wall rule `theta_wallTwo` with the closing equation).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

theorem eC_int_mul_add (a n : ℤ) (s : ℝ) : eC (a * (s + n)) = eC (a * s) := by
  rw [show (a : ℝ) * (s + n) = a * s + ((a * n : ℤ) : ℝ) by push_cast; ring, eC_add, eC_int,
    mul_one]

theorem eC_nat_mul_sub (p : ℕ) (hp : 0 < p) (q : ℤ) (s : ℝ) :
    eC (p * (s - q / p)) = eC (p * s) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [show (p : ℝ) * (s - q / p) = p * s + ((-q : ℤ) : ℝ) by push_cast; field_simp; ring, eC_add,
    eC_int, mul_one]

theorem tube_rot {p : ℕ} (hp : 0 < p) {q a b : ℤ} (hb : (p : ℤ) * b - a * q = 1) (w : ℂ)
    (s : ℝ) : ((Circle.exp (-2 * Real.pi / p) : ℂ) * w * (eC (a * (s - q / p)) : ℂ),
      eC (p * (s - q / p))) = (w * (eC (a * s) : ℂ), eC (p * s)) := by
  rw [eC_nat_mul_sub p hp]
  congr 1
  have key : Circle.exp (-2 * Real.pi / p) * eC (a * (s - q / p)) = eC (a * s) := by
    rw [eC, eC, ← Circle.exp_add]
    have hb' : ((p : ℝ) * b - a * q) = 1 := by exact_mod_cast hb
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have : -2 * Real.pi / p + 2 * Real.pi * (a * (s - q / p)) =
        2 * Real.pi * (a * s) + ((-b : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      field_simp
      linear_combination hb'
    rw [this, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  have := congrArg (fun c : Circle => (c : ℂ) * w) key
  simp only [Circle.coe_mul] at this
  linear_combination this

namespace FlatDatum

variable (K : FlatDatum)

section Deck

def deck (n : ℤ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates := fibreTranslation (n * K.ℓ)

theorem metric_deck (n : ℤ) :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric (K.deck n) = K.m.coneProfile.metric :=
  fibreTranslation_isometry _ _

theorem planeOf_deck (n : ℤ) (x : ModelCoordinates) : planeOf (K.deck n x) = planeOf x :=
  planeOf_fibreTranslation _ _

theorem two_deck (n : ℤ) (x : ModelCoordinates) : K.deck n x 2 = x 2 + n * K.ℓ :=
  fibreTranslation_two _ _

theorem div_deck (n : ℤ) (x : ModelCoordinates) : K.deck n x 2 / K.ℓ = x 2 / K.ℓ + n := by
  rw [two_deck, add_div, mul_div_cancel_right₀ _ K.ℓ_ne]

theorem liftP_shift {y y' : ModelCoordinates} (n : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.liftP y' = K.liftP y := by
  unfold liftP
  rw [hp, h2, eC_add, eC_int, mul_one]

theorem liftP_deck (n : ℤ) (x : ModelCoordinates) : K.liftP (K.deck n x) = K.liftP x :=
  K.liftP_shift n (K.planeOf_deck n x) (K.div_deck n x)

theorem liftM_deck (n : ℤ) (x : ModelCoordinates) : K.liftM (K.deck n x) = K.liftM x := by
  unfold liftM
  congr 1
  apply K.liftP_shift (-n)
  · rw [planeOf_reflectMap, planeOf_reflectMap, planeOf_deck]
  · rw [reflectMap_two, reflectMap_two, sub_div, sub_div, K.div_deck]
    push_cast
    ring

theorem tubeOne_shift {y y' : ModelCoordinates} (n : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeOne y' = K.tubeOne y := by
  unfold tubeOne sOne
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaOne (planeOf y) =
    y 2 / K.ℓ + K.betaOne (planeOf y) + n by ring, eC_int_mul_add,
    show ((K.σ.p₁ : ℕ) : ℝ) = ((K.σ.p₁ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeTwo_shift {y y' : ModelCoordinates} (n : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeTwo y' = K.tubeTwo y := by
  unfold tubeTwo sTwo
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaTwo (planeOf y) =
    y 2 / K.ℓ + K.betaTwo (planeOf y) + n by ring, eC_int_mul_add,
    show ((K.σ.p₂ : ℕ) : ℝ) = ((K.σ.p₂ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeThree_shift {y y' : ModelCoordinates} (n : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeThree y' = K.tubeThree y := by
  unfold tubeThree sThree
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaThree = y 2 / K.ℓ + K.betaThree + n by ring,
    eC_int_mul_add, show ((K.σ.p₃ : ℕ) : ℝ) = ((K.σ.p₃ : ℤ) : ℝ) by push_cast; rfl,
    eC_int_mul_add]

theorem rotThreeInv_deck (n : ℤ) (x : ModelCoordinates) :
    K.tubeOne (K.rotThreeInv (K.deck n x)) = K.tubeOne (K.rotThreeInv x) := by
  refine K.tubeOne_shift n ?_ ?_
  · rw [rotThreeInv, rotThreeInv, planeOf_ofPlane, planeOf_ofPlane, planeOf_deck]
  · rw [rotThreeInv, rotThreeInv, ofPlane_apply_two, ofPlane_apply_two, add_div, add_div,
      K.div_deck]
    ring

end Deck

end FlatDatum

theorem circle_exp_pow_eq_one {p : ℕ} (hp : 0 < p) :
    (Circle.exp (-2 * Real.pi / p) : ℂ) ^ p = 1 := by
  rw [← Circle.coe_pow, ← zpow_natCast, circle_exp_pow]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [show (((p : ℤ) : ℝ)) * (-2 * Real.pi / p) = -(2 * Real.pi) by push_cast; field_simp,
    Circle.exp_neg, Circle.exp_two_pi, inv_one, Circle.coe_one]

theorem norm_circle_mul (a : ℝ) (w : ℂ) : ‖(Circle.exp a : ℂ) * w‖ = ‖w‖ := by
  rw [norm_mul, Circle.norm_coe, one_mul]

namespace FlatDatum

variable (K : FlatDatum)

section Screws

theorem coe_pOne : ((K.pOne : ℕ) : ℝ) = K.σ.p₁ := rfl

theorem coe_pTwo : ((K.pTwo : ℕ) : ℝ) = K.σ.p₂ := rfl

theorem planeOf_screwOne (x : ModelCoordinates) : planeOf (K.screwOne x) =
    K.σ.vertexOne + (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) * (planeOf x - K.σ.vertexOne) :=
  K.planeOf_screw _ _ _ x

theorem planeOf_screwTwo (x : ModelCoordinates) : planeOf (K.screwTwo x) =
    K.σ.vertexTwo + (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) * (planeOf x - K.σ.vertexTwo) :=
  K.planeOf_screw _ _ _ x

theorem planeOf_screwThree (x : ModelCoordinates) :
    planeOf (K.screwThree x) = (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) * planeOf x := by
  rw [screwThree, K.planeOf_screw, sub_zero, zero_add]
  rfl

theorem two_screwThree (x : ModelCoordinates) :
    K.screwThree x 2 = x 2 - K.ℓ * K.q₃ / K.σ.p₃ := by
  rw [screwThree, K.two_screw]
  simp only [planeCrossC, zero_re, zero_im, zero_mul, sub_zero, mul_zero, zero_div]
  rfl

theorem rotOne_screwOne (x : ModelCoordinates) : K.σ.rotOne (planeOf (K.screwOne x)) =
    (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) * K.σ.rotOne (planeOf x) := by
  rw [K.planeOf_screwOne, EuclidShape.rotOne, EuclidShape.rotOne]
  ring

theorem rotTwo_screwTwo (x : ModelCoordinates) : K.σ.rotTwo (planeOf (K.screwTwo x)) =
    (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) * K.σ.rotTwo (planeOf x) := by
  rw [K.planeOf_screwTwo, EuclidShape.rotTwo, EuclidShape.rotTwo]
  ring

theorem apexOne_screwOne (x : ModelCoordinates) :
    K.σ.apexOne (planeOf (K.screwOne x)) = K.σ.apexOne (planeOf x) := by
  rw [EuclidShape.apexOne, EuclidShape.apexOne, K.rotOne_screwOne, mul_pow,
    circle_exp_pow_eq_one K.p₁_pos, one_mul]

theorem apexTwo_screwTwo (x : ModelCoordinates) :
    K.σ.apexTwo (planeOf (K.screwTwo x)) = K.σ.apexTwo (planeOf x) := by
  rw [EuclidShape.apexTwo, EuclidShape.apexTwo, K.rotTwo_screwTwo, mul_pow,
    circle_exp_pow_eq_one K.p₂_pos, one_mul]

theorem sOne_screwOne (x : ModelCoordinates) :
    K.sOne (K.screwOne x) = K.sOne x - K.q₁ / K.σ.p₁ := by
  have h2 := K.two_screw K.σ.vertexOne K.pOne K.q₁ x
  rw [K.coe_pOne] at h2
  change K.screwOne x 2 = _ at h2
  have hp := K.planeOf_screwOne x
  unfold sOne betaOne
  rw [K.apexOne_screwOne, h2, hp]
  set Wv := (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) * (planeOf x - K.σ.vertexOne)
  have hℓ := K.ℓ_ne
  simp only [PhaseData.psi, phase_c, planeCrossC, add_re, add_im, sub_re, sub_im]
  field_simp
  ring

theorem sTwo_screwTwo (x : ModelCoordinates) :
    K.sTwo (K.screwTwo x) = K.sTwo x - K.q₂ / K.σ.p₂ := by
  have h2 := K.two_screw K.σ.vertexTwo K.pTwo K.q₂ x
  rw [K.coe_pTwo] at h2
  change K.screwTwo x 2 = _ at h2
  have hp := K.planeOf_screwTwo x
  unfold sTwo betaTwo
  rw [K.apexTwo_screwTwo, h2, hp]
  set Wv := (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) * (planeOf x - K.σ.vertexTwo)
  have hℓ := K.ℓ_ne
  simp only [PhaseData.psi, phase_c, planeCrossC, add_re, add_im, sub_re, sub_im]
  field_simp
  ring

theorem sThree_screwThree (x : ModelCoordinates) :
    K.sThree (K.screwThree x) = K.sThree x - K.q₃ / K.σ.p₃ := by
  unfold sThree
  rw [K.two_screwThree]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem tubeOne_screwOne (x : ModelCoordinates) : K.tubeOne (K.screwOne x) = K.tubeOne x := by
  unfold tubeOne
  rw [K.rotOne_screwOne, K.sOne_screwOne]
  exact tube_rot K.p₁_pos K.bez₁ _ _

theorem tubeTwo_screwTwo (x : ModelCoordinates) : K.tubeTwo (K.screwTwo x) = K.tubeTwo x := by
  unfold tubeTwo
  rw [K.rotTwo_screwTwo, K.sTwo_screwTwo]
  exact tube_rot K.p₂_pos K.bez₂ _ _

theorem tubeThree_screwThree (x : ModelCoordinates) :
    K.tubeThree (K.screwThree x) = K.tubeThree x := by
  unfold tubeThree
  rw [K.planeOf_screwThree, K.sThree_screwThree, mul_left_comm]
  have := tube_rot K.p₃_pos K.bez₃ ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x)
    (K.sThree x)
  rw [← mul_assoc] at this ⊢
  exact this

theorem screwOne_mem_discOne {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    planeOf (K.screwOne x) ∈ discOne K.D := by
  change ‖planeOf (K.screwOne x) - K.σ.vertexOne‖ < _
  rw [K.planeOf_screwOne, add_sub_cancel_left, norm_circle_mul]
  exact hd

theorem screwTwo_mem_discTwo {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    planeOf (K.screwTwo x) ∈ discTwo K.D := by
  change ‖planeOf (K.screwTwo x) - K.σ.vertexTwo‖ < _
  rw [K.planeOf_screwTwo, add_sub_cancel_left, norm_circle_mul]
  exact hd

theorem screwThree_mem_discThree {x : ModelCoordinates} (hd : planeOf x ∈ discThree K.D) :
    planeOf (K.screwThree x) ∈ discThree K.D := by
  change ‖planeOf (K.screwThree x)‖ < _
  rw [K.planeOf_screwThree, norm_circle_mul]
  exact hd

theorem conj_planeOf_screwThree (x : ModelCoordinates) :
    conj (planeOf (K.screwThree x)) = K.σ.refl 1 (planeOf x) := by
  rw [K.planeOf_screwThree, map_mul, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  change _ = exp (2 * (K.σ.θ₃ : ℂ) * I) * conj (planeOf x)
  rw [Circle.coe_exp, p_inv_eq K.p₃_pos K.σ.θ₃_mul]
  congr 2
  push_cast
  ring

theorem screwThree_mem_discOneMirror {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    planeOf (K.screwThree x) ∈ discOneMirror K.D := by
  rw [mem_discOneMirror_iff, K.conj_planeOf_screwThree]
  exact refl_one_mem_discOne K.D hd

end Screws

section Walls

theorem liftM_screwThree {y : ModelCoordinates} (hp : planeOf y ∈ patchOne K.D) :
    K.liftM (K.screwThree y) = K.liftP y := by
  set z := planeOf y with hz
  have hV : z ∈ K.D.V 1 := patchOne_subset_V K.D hp
  have hre : 3 / 2 < (K.D.f z).re := hp.2.2.2.2.2.1
  have hfl : K.D.f (K.σ.refl 1 z) = conj (K.D.f z) := f_refl' K.D 1 hV
  have hθ := K.phase.theta_wallOne (z := z) (z' := K.σ.refl 1 z) hre
    (K.psi_vertexOne_refl_one z)
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, K.conj_planeOf_screwThree, ← hz, hfl, Complex.conj_conj,
    reflectMap_two, K.two_screwThree]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  have hp3 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  have hA : (K.c₀ - (y 2 - K.ℓ * K.q₃ / K.σ.p₃)) / K.ℓ = K.k₁ + K.k₂ + K.k₃ - y 2 / K.ℓ := by
    unfold c₀ k₃
    field_simp
    ring
  rw [hA]
  rw [phase_e] at hθ
  linear_combination hθ

theorem midpoint_refl_two (σ : EuclidShape) (z : ℂ) : ∃ τ : ℝ,
    (z + σ.refl 2 z) / 2 = σ.vertexOne + τ * (σ.vertexTwo - σ.vertexOne) := by
  set w := σ.rotTwo z with hw
  set E := exp (-((σ.θ₂ : ℂ) * I)) with hE
  have hs := σ.sin_θ₃_pos
  have hEE : E * exp ((σ.θ₂ : ℂ) * I) = 1 := by
    rw [hE, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have h1 : z - σ.vertexTwo = -(E * w) := by
    rw [hw, EuclidShape.rotTwo]
    linear_combination (-(z - σ.vertexTwo)) * hEE
  have hcE : conj E = exp ((σ.θ₂ : ℂ) * I) := by
    rw [hE, ← Complex.exp_conj]
    congr 1
    simp [map_mul, conj_ofReal, conj_I]
  have h2 : σ.refl 2 z - σ.vertexTwo = -(E * conj w) := by
    change σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo) - σ.vertexTwo = _
    rw [h1, map_neg, map_mul, hcE]
    have : exp (-(2 * (σ.θ₂ : ℂ) * I)) * exp ((σ.θ₂ : ℂ) * I) = E := by
      rw [hE, ← Complex.exp_add]
      congr 1
      ring
    linear_combination (-conj w) * this
  have h3 : σ.vertexTwo - σ.vertexOne = (Real.sin σ.θ₃ : ℂ) * E := σ.vertexTwo_sub_vertexOne
  have h4 : w + conj w = 2 * (w.re : ℂ) := by
    rw [Complex.add_conj]
    push_cast
    ring
  refine ⟨1 - w.re / Real.sin σ.θ₃, ?_⟩
  have hτ : (((1 - w.re / Real.sin σ.θ₃ : ℝ)) : ℂ) * (Real.sin σ.θ₃ : ℂ) =
      (Real.sin σ.θ₃ : ℂ) - (w.re : ℂ) := by
    rw [← ofReal_mul, ← ofReal_sub]
    congr 1
    field_simp
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2 + (-E / 2) * h4 +
    (1 - (((1 - w.re / Real.sin σ.θ₃ : ℝ)) : ℂ)) * h3 - E * hτ

def rotTwoInv (y : ModelCoordinates) : ModelCoordinates :=
  ofPlane (conj (K.σ.refl 2 (planeOf y)))
    (y 2 + K.ℓ * K.q₂ / K.σ.p₂ +
      K.c * planeCrossC K.σ.vertexTwo (planeOf y - conj (K.σ.refl 2 (planeOf y))) / 2)

theorem conj_refl_two (z : ℂ) : conj (K.σ.refl 2 z) =
    K.σ.vertexTwo + (Circle.exp (2 * Real.pi / K.σ.p₂) : ℂ) * (z - K.σ.vertexTwo) := by
  change conj (K.σ.vertexTwo + exp (-(2 * (K.σ.θ₂ : ℂ) * I)) * conj (z - K.σ.vertexTwo)) = _
  rw [map_add, map_mul, Complex.conj_conj, K.σ.conj_vertexTwo, ← Complex.exp_conj,
    Circle.coe_exp, p_inv_eq K.p₂_pos K.σ.θ₂_mul]
  congr 3
  simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ofNat]
  push_cast
  ring

theorem screwTwo_rotTwoInv (y : ModelCoordinates) : K.screwTwo (K.rotTwoInv y) = y := by
  have hcr := K.conj_refl_two (planeOf y)
  have hω : (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) * (Circle.exp (2 * Real.pi / K.σ.p₂) : ℂ) =
      1 := by
    rw [← Circle.coe_mul, ← Circle.exp_add, show -2 * Real.pi / K.σ.p₂ + 2 * Real.pi / K.σ.p₂ = 0
      by ring, Circle.exp_zero, Circle.coe_one]
  have hz : (Circle.exp (-2 * Real.pi / K.σ.p₂) : ℂ) *
      (conj (K.σ.refl 2 (planeOf y)) - K.σ.vertexTwo) = planeOf y - K.σ.vertexTwo := by
    rw [hcr, add_sub_cancel_left, ← mul_assoc, hω, one_mul]
  apply modelCoordinates_ext
  · rw [K.planeOf_screwTwo, rotTwoInv, planeOf_ofPlane, hz, add_sub_cancel]
  · have h2 := K.two_screw K.σ.vertexTwo K.pTwo K.q₂ (K.rotTwoInv y)
    rw [K.coe_pTwo] at h2
    change K.screwTwo (K.rotTwoInv y) 2 = _ at h2
    rw [h2, rotTwoInv, planeOf_ofPlane, ofPlane_apply_two, hz]
    rw [show planeOf y - K.σ.vertexTwo - (conj (K.σ.refl 2 (planeOf y)) - K.σ.vertexTwo) =
      planeOf y - conj (K.σ.refl 2 (planeOf y)) by ring]
    ring

theorem screwTwo_symm (y : ModelCoordinates) : K.screwTwo.symm y = K.rotTwoInv y := by
  conv_lhs => rw [← K.screwTwo_rotTwoInv y]
  exact K.screwTwo.symm_apply_apply _

theorem liftM_rotTwoInv {y : ModelCoordinates} (hp : planeOf y ∈ patchTwo K.D) :
    K.liftM (K.rotTwoInv y) = K.liftP y := by
  set z := planeOf y with hz
  have hV : z ∈ K.D.V 2 := patchTwo_subset_V K.D hp
  have hre1 : -(3 / 2) < (K.D.f z).re := hp.2.2.2.2.2.1
  have hre2 : (K.D.f z).re < 3 / 2 := hp.2.2.2.2.2.2.1
  have hn : normSq (K.D.f z) ≤ 25 / 4 := le_of_lt hp.2.2.2.2.2.2.2.1
  have hfl : K.D.f (K.σ.refl 2 z) = conj (K.D.f z) := f_refl' K.D 2 hV
  obtain ⟨τ, hM⟩ := midpoint_refl_two K.σ z
  have hθ := K.phase.theta_wallTwo (z := z) (z' := K.σ.refl 2 z) hre1 hre2 hn K.ℓ_ne τ hM
    K.phase_closing
  have hX : planeCrossC K.σ.vertexTwo (z - conj (K.σ.refl 2 z)) =
      2 * planeCrossC K.σ.vertexTwo ((z + K.σ.refl 2 z) / 2) := by
    simp only [planeCrossC, EuclidShape.vertexTwo, ofReal_re, ofReal_im, sub_im, conj_im,
      add_im, div_ofNat_im, sub_re, conj_re, add_re, div_ofNat_re]
    ring
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, rotTwoInv, planeOf_ofPlane, Complex.conj_conj, ← hz, hfl,
    Complex.conj_conj, reflectMap_two, ofPlane_apply_two]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add, hX]
  congr 1
  have hℓ := K.ℓ_ne
  have hp2 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
  have hA : (K.c₀ - (y 2 + K.ℓ * K.q₂ / K.σ.p₂ +
      K.c * (2 * planeCrossC K.σ.vertexTwo ((z + K.σ.refl 2 z) / 2)) / 2)) / K.ℓ =
        K.k₁ - y 2 / K.ℓ - K.c * planeCrossC K.σ.vertexTwo ((z + K.σ.refl 2 z) / 2) / K.ℓ := by
    unfold c₀ k₂
    field_simp
    ring
  rw [hA]
  simp only [phase_k₁, phase_c, phase_ℓ, phase_v₂] at hθ
  linear_combination hθ

end Walls

end FlatDatum

section Moves

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem flatMap_deck (K : FlatDatum) (n : ℤ) (x : ModelCoordinates) :
    flatMap C hc h3 K (K.deck n x) = flatMap C hc h3 K x := by
  unfold flatMap
  rw [K.planeOf_deck, K.liftP_deck, K.liftM_deck, K.rotThreeInv_deck,
    K.tubeOne_shift n (K.planeOf_deck n x) (K.div_deck n x),
    K.tubeTwo_shift n (K.planeOf_deck n x) (K.div_deck n x),
    K.tubeThree_shift n (K.planeOf_deck n x) (K.div_deck n x)]

theorem foldRel_deck (K : FlatDatum) (n : ℤ) {x : ModelCoordinates} (hx : x ∈ flatDomain K) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.deck n x) := by
  refine ⟨K.deck n, K.metric_deck n, rfl, flatDomain K, (flatDomain K).isOpen, hx, subset_rfl,
    fun y hy => ?_, fun y _ => flatMap_deck C hc h3 K n y⟩
  change planeOf (K.deck n y) ∈ flatBase K
  rw [K.planeOf_deck]
  exact hy

theorem foldRel_screwOne (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwOne x) := by
  have hU : IsOpen (planeOf ⁻¹' discOne K.D) :=
    (isOpen_discOne K.D).preimage contDiff_planeOf.continuous
  have hsub : planeOf ⁻¹' discOne K.D ⊆ flatDomain K := fun y hy => by
    change planeOf y ∈ flatBase K
    simp only [flatBase, mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hy)))
  refine ⟨K.screwOne, K.metric_screwOne, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwOne_mem_discOne hy), fun y hy => ?_⟩
  rw [flatMap_of_discOne C hc h3 K (K.screwOne_mem_discOne hy), flatMap_of_discOne C hc h3 K hy,
    K.tubeOne_screwOne]

theorem foldRel_screwTwo (K : FlatDatum) {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwTwo x) := by
  have hU : IsOpen (planeOf ⁻¹' discTwo K.D) :=
    (isOpen_discTwo K.D).preimage contDiff_planeOf.continuous
  have hsub : planeOf ⁻¹' discTwo K.D ⊆ flatDomain K := fun y hy => by
    change planeOf y ∈ flatBase K
    simp only [flatBase, mem_union]
    exact Or.inl (Or.inr hy)
  refine ⟨K.screwTwo, K.metric_screwTwo, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwTwo_mem_discTwo hy), fun y hy => ?_⟩
  rw [flatMap_of_discTwo C hc h3 K (K.screwTwo_mem_discTwo hy), flatMap_of_discTwo C hc h3 K hy,
    K.tubeTwo_screwTwo]

theorem foldRel_screwThree (K : FlatDatum) {x : ModelCoordinates}
    (hd : planeOf x ∈ discThree K.D) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwThree x) := by
  have hU : IsOpen (planeOf ⁻¹' discThree K.D) :=
    (isOpen_discThree K.D).preimage contDiff_planeOf.continuous
  have hsub : planeOf ⁻¹' discThree K.D ⊆ flatDomain K := fun y hy => by
    change planeOf y ∈ flatBase K
    simp only [flatBase, mem_union]
    exact Or.inr hy
  refine ⟨K.screwThree, K.metric_screwThree, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwThree_mem_discThree hy), fun y hy => ?_⟩
  rw [flatMap_of_discThree C hc h3 K (K.screwThree_mem_discThree hy),
    flatMap_of_discThree C hc h3 K hy, K.tubeThree_screwThree]

theorem foldRel_screwThree_discOne (K : FlatDatum) {x : ModelCoordinates}
    (hd : planeOf x ∈ discOne K.D) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x (K.screwThree x) := by
  have hU : IsOpen (planeOf ⁻¹' discOne K.D) :=
    (isOpen_discOne K.D).preimage contDiff_planeOf.continuous
  refine ⟨K.screwThree, K.metric_screwThree, rfl, _, hU, hd, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_⟩
  · change planeOf y ∈ flatBase K
    simp only [flatBase, mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hy)))
  · change planeOf (K.screwThree y) ∈ flatBase K
    simp only [flatBase, mem_union]
    exact Or.inl (Or.inl (Or.inr (K.screwThree_mem_discOneMirror hy)))
  · rw [flatMap_of_discOneMirror C hc h3 K (K.screwThree_mem_discOneMirror hy),
      flatMap_of_discOne C hc h3 K hy, ← K.screwThree_symm, Diffeomorph.symm_apply_apply]

end Moves

section PatchMoves

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

theorem main_subset_flatBase (K : FlatDatum) {z : ℂ} (hm : z ∈ mainSet K.D) :
    z ∈ flatBase K := by
  simp only [flatBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm))))

theorem conjMain_subset_flatBase (K : FlatDatum) {z : ℂ} (hm : conj z ∈ mainSet K.D) :
    z ∈ flatBase K := by
  simp only [flatBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))

theorem foldRel_screwThree_patchOne {x : ModelCoordinates} (hp : planeOf x ∈ patchOne (𝒦).D) :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x
      ((𝒦).screwThree x) := by
  have hU : IsOpen (planeOf ⁻¹' patchOne (𝒦).D) :=
    (isOpen_patchOne _).preimage contDiff_planeOf.continuous
  have hmain : ∀ {z : ℂ}, z ∈ patchOne (𝒦).D → z ∈ mainSet (𝒦).D :=
    fun h => Or.inl (Or.inr h)
  have hconj : ∀ {y : ModelCoordinates}, planeOf y ∈ patchOne (𝒦).D →
      conj (planeOf ((𝒦).screwThree y)) ∈ mainSet (𝒦).D := fun hy => by
    rw [FlatDatum.conj_planeOf_screwThree]
    exact hmain (refl_mem_patchOne _ hy)
  refine ⟨(𝒦).screwThree, (𝒦).metric_screwThree, rfl, _, hU, hp,
    fun y hy => main_subset_flatBase _ (hmain hy),
    fun y hy => conjMain_subset_flatBase _ (hconj hy), fun y hy => ?_⟩
  rw [flatMap_of_conjMain C hc h3 h0 D (hconj hy), flatMap_of_main C hc h3 h0 D (hmain hy),
    (𝒦).liftM_screwThree hy]

theorem foldRel_screwTwoInv_patchTwo {x : ModelCoordinates} (hp : planeOf x ∈ patchTwo (𝒦).D) :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x
      ((𝒦).screwTwo.symm x) := by
  have hU : IsOpen (planeOf ⁻¹' patchTwo (𝒦).D) :=
    (isOpen_patchTwo _).preimage contDiff_planeOf.continuous
  have hmain : ∀ {z : ℂ}, z ∈ patchTwo (𝒦).D → z ∈ mainSet (𝒦).D := fun h => Or.inr h
  have hconj : ∀ {y : ModelCoordinates}, planeOf y ∈ patchTwo (𝒦).D →
      conj (planeOf ((𝒦).screwTwo.symm y)) ∈ mainSet (𝒦).D := fun hy => by
    rw [FlatDatum.screwTwo_symm, FlatDatum.rotTwoInv, planeOf_ofPlane, Complex.conj_conj]
    exact hmain (refl_mem_patchTwo _ hy)
  refine ⟨(𝒦).screwTwo.symm, FoldRel.isometry_symm (𝒦).metric_screwTwo, rfl, _, hU, hp,
    fun y hy => main_subset_flatBase _ (hmain hy),
    fun y hy => conjMain_subset_flatBase _ (hconj hy), fun y hy => ?_⟩
  rw [flatMap_of_conjMain C hc h3 h0 D (hconj hy), flatMap_of_main C hc h3 h0 D (hmain hy),
    FlatDatum.screwTwo_symm, (𝒦).liftM_rotTwoInv hy]

end PatchMoves

end ClosedTriangle

end GC.Seifert
