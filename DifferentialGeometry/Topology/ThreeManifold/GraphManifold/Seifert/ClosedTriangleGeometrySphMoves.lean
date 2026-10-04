import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphLifts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatMoves

/-!
# The model side of the generator moves of a spherical closed triangle fold

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §3, §6, with
review 32 §6.3 and §7.1). For a `SphDatum` all lifts are invariant under the fibre shifts by
integer multiples of `ℓ` (`liftP_shift`, `liftM_shift`, `tube*_shift`), in particular under the
Hopf period `2π = n ℓ` (`liftP_period`, ...). The screw about the outer vertex `0` is global in the
Hopf chart (`screwDiffeomorph (-2π/p₃) (-ℓ q₃/p₃)`, the chart of `screwAtLiftS3 0`) and preserves
`tubeThree` (`tubeThree_screwZero`); it carries the wall-1 patch to the mirror side, where the
mirror lift equals the base lift by the wall-1 rule (`liftM_screwZero`). The screws about the
inner vertices are local in the chart (`screwChart`) and preserve the full tube maps
(`tubeOne_screwChart`, `tubeTwo_screwChart`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

open TwoConeFold

namespace SphDatum

variable (K : SphDatum)

section Shift

theorem liftP_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) : K.liftP y' = K.liftP y := by
  unfold liftP
  rw [hp, h2, eC_add, eC_int, mul_one]

theorem liftM_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) : K.liftM y' = K.liftM y := by
  unfold liftM
  congr 1
  apply K.liftP_shift (-m)
  · rw [planeOf_reflectMap, planeOf_reflectMap, hp]
  · rw [reflectMap_two, reflectMap_two, sub_div, sub_div, h2]
    push_cast
    ring

theorem tubeOne_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) : K.tubeOne y' = K.tubeOne y := by
  unfold tubeOne sOne
  rw [hp, h2, show y 2 / K.ℓ + m + K.betaOne (planeOf y) =
    y 2 / K.ℓ + K.betaOne (planeOf y) + m by ring, eC_int_mul_add,
    show ((K.σ.p₁ : ℕ) : ℝ) = ((K.σ.p₁ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeTwo_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) : K.tubeTwo y' = K.tubeTwo y := by
  unfold tubeTwo sTwo
  rw [hp, h2, show y 2 / K.ℓ + m + K.betaTwo (planeOf y) =
    y 2 / K.ℓ + K.betaTwo (planeOf y) + m by ring, eC_int_mul_add,
    show ((K.σ.p₂ : ℕ) : ℝ) = ((K.σ.p₂ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeThree_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) : K.tubeThree y' = K.tubeThree y := by
  unfold tubeThree sThree
  rw [hp, h2, show y 2 / K.ℓ + m + K.betaThree = y 2 / K.ℓ + K.betaThree + m by ring,
    eC_int_mul_add, show ((K.σ.p₃ : ℕ) : ℝ) = ((K.σ.p₃ : ℤ) : ℝ) by push_cast; rfl,
    eC_int_mul_add]

theorem rotThreeInv_shift {y y' : ModelCoordinates} (m : ℤ) (hp : planeOf y' = planeOf y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + m) :
    K.tubeOne (K.rotThreeInv y') = K.tubeOne (K.rotThreeInv y) := by
  refine K.tubeOne_shift m ?_ ?_
  · rw [rotThreeInv, rotThreeInv, planeOf_ofPlane, planeOf_ofPlane, hp]
  · rw [rotThreeInv, rotThreeInv, ofPlane_apply_two, ofPlane_apply_two, add_div, add_div, h2]
    ring

theorem planeOf_add_fibreShift' (x : ModelCoordinates) (s : ℝ) :
    planeOf (x + GC.Geometry.fibreShift s) = planeOf x :=
  planeOf_add_fibreShift s x

theorem period_div (x : ModelCoordinates) (m : ℤ) :
    (x + GC.Geometry.fibreShift (2 * Real.pi * m)) 2 / K.ℓ = x 2 / K.ℓ + ((K.n * m : ℤ) : ℝ) := by
  have h : (x + GC.Geometry.fibreShift (2 * Real.pi * m)) 2 = x 2 + 2 * Real.pi * m := by
    simp [GC.Geometry.fibreShift]
  rw [h, K.period]
  have hℓ := K.ℓ_ne
  push_cast
  field_simp

end Shift

section ScrewZero

def screwZeroAngle : ℝ := -2 * Real.pi / K.σ.p₃

def screwZeroShift : ℝ := -K.ℓ * K.q₃ / K.σ.p₃

theorem planeOf_screwZero (x : ModelCoordinates) :
    planeOf (screwDiffeomorph K.screwZeroAngle K.screwZeroShift x) =
      (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) * planeOf x := by
  rw [planeOf_screwDiffeomorph, Circle.coe_exp, screwZeroAngle]

theorem two_screwZero (x : ModelCoordinates) :
    screwDiffeomorph K.screwZeroAngle K.screwZeroShift x 2 = x 2 - K.ℓ * K.k₃ := by
  rw [screwDiffeomorph_two, screwZeroShift, k₃]
  ring

theorem tubeThree_screwZero (x : ModelCoordinates) :
    K.tubeThree (screwDiffeomorph K.screwZeroAngle K.screwZeroShift x) = K.tubeThree x := by
  have hs : K.sThree (screwDiffeomorph K.screwZeroAngle K.screwZeroShift x) =
      K.sThree x - K.q₃ / K.σ.p₃ := by
    simp only [sThree, two_screwZero, k₃]
    have hℓ := K.ℓ_ne
    field_simp
    ring
  unfold tubeThree
  rw [hs, planeOf_screwZero]
  have := tube_rot K.p₃_pos K.bez₃ ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x) (K.sThree x)
  rw [← this]
  congr 1
  ring

theorem conj_planeOf_screwZero (x : ModelCoordinates) :
    conj (planeOf (screwDiffeomorph K.screwZeroAngle K.screwZeroShift x)) =
      K.σ.refl 1 (planeOf x) := by
  rw [planeOf_screwZero, map_mul, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  change _ = exp (2 * (K.σ.θ₃ : ℂ) * I) * conj (planeOf x)
  rw [Circle.coe_exp, CompactShape.θ₃]
  congr 2
  push_cast
  ring

theorem liftM_screwZero {y : ModelCoordinates} (hV : planeOf y ∈ K.D.V 1)
    (hre : 3 / 2 < (K.D.f (planeOf y)).re)
    (hz : 1 + conj K.σ.vertexOne * planeOf y ∈ slitPlane) :
    K.liftM (screwDiffeomorph K.screwZeroAngle K.screwZeroShift y) = K.liftP y := by
  set z := planeOf y with hzdef
  have hfl : K.D.f (K.σ.refl 1 z) = conj (K.D.f z) := K.D.f_refl 1 z hV
  have hθ := K.phase.theta_wallOne (z := z) (z' := K.σ.refl 1 z) hre
    (K.psi_vertexOne_refl_one hz)
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, K.conj_planeOf_screwZero, ← hzdef, hfl, Complex.conj_conj,
    reflectMap_two, K.two_screwZero]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  have hA : (K.c₀ - (y 2 - K.ℓ * K.k₃)) / K.ℓ = K.k₁ + K.k₂ + K.k₃ - y 2 / K.ℓ := by
    unfold c₀
    field_simp
    ring
  rw [hA]
  rw [phase_e] at hθ
  linear_combination hθ

end ScrewZero

section ScrewInner

theorem exp_screw_pow {p : ℕ} (hp : 0 < p) :
    exp (((-2 * Real.pi / p : ℝ) : ℂ) * I) ^ p = 1 := by
  rw [← exp_nat_mul]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have : (p : ℂ) * (((-2 * Real.pi / p : ℝ) : ℂ) * I) = (-1 : ℤ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
  rw [this]
  exact exp_int_mul_two_pi_mul_I (-1)

theorem tubeOne_screwChart {x : ModelCoordinates}
    (hx : 1 + conj K.σ.vertexOne * planeOf x ≠ 0)
    (hy : 1 - conj K.σ.vertexOne * planeOf (screwDiffeomorph (-2 * Real.pi / K.σ.p₁)
      (-K.ℓ * K.q₁ / K.σ.p₁) (centred K.σ.vertexOne x)) ≠ 0)
    (hx' : 1 + conj K.σ.vertexOne * planeOf (screwChart K.σ.vertexOne (-2 * Real.pi / K.σ.p₁)
      (-K.ℓ * K.q₁ / K.σ.p₁) x) ≠ 0) :
    K.tubeOne (screwChart K.σ.vertexOne (-2 * Real.pi / K.σ.p₁) (-K.ℓ * K.q₁ / K.σ.p₁) x) =
      K.tubeOne x := by
  rw [tubeOne_eq_sphTube, tubeOne_eq_sphTube]
  refine sphTube_screwChart K.p₁_pos K.bez₁ K.ℓ_ne K.period hx hy hx' ?_
  have hd := disc_screwChart hx hy hx'
  unfold betaHatOne apexOneS
  rw [rotOne_eq_of_sph K.hσ, rotOne_eq_of_sph K.hσ, hd, mul_pow, mul_pow, mul_pow,
    exp_screw_pow K.p₁_pos, one_mul]

theorem tubeTwo_screwChart {x : ModelCoordinates}
    (hx : 1 + conj K.σ.vertexTwo * planeOf x ≠ 0)
    (hy : 1 - conj K.σ.vertexTwo * planeOf (screwDiffeomorph (-2 * Real.pi / K.σ.p₂)
      (-K.ℓ * K.q₂ / K.σ.p₂) (centred K.σ.vertexTwo x)) ≠ 0)
    (hx' : 1 + conj K.σ.vertexTwo * planeOf (screwChart K.σ.vertexTwo (-2 * Real.pi / K.σ.p₂)
      (-K.ℓ * K.q₂ / K.σ.p₂) x) ≠ 0) :
    K.tubeTwo (screwChart K.σ.vertexTwo (-2 * Real.pi / K.σ.p₂) (-K.ℓ * K.q₂ / K.σ.p₂) x) =
      K.tubeTwo x := by
  rw [tubeTwo_eq_sphTube, tubeTwo_eq_sphTube]
  refine sphTube_screwChart K.p₂_pos K.bez₂ K.ℓ_ne K.period hx hy hx' ?_
  have hd := disc_screwChart hx hy hx'
  unfold betaHatTwo apexTwoS
  rw [rotTwo_eq_of_sph K.hσ, rotTwo_eq_of_sph K.hσ, hd, mul_pow, mul_pow, mul_pow,
    exp_screw_pow K.p₂_pos, one_mul]

end ScrewInner

section WallTwo

theorem conj_refl_two_sph (z : ℂ) :
    conj (K.σ.refl 2 z) = (exp (((2 * Real.pi / K.σ.p₂ : ℝ) : ℂ) * I) *
      discV K.σ.vertexTwo z + K.σ.vertexTwo) /
        (1 - conj K.σ.vertexTwo * (exp (((2 * Real.pi / K.σ.p₂ : ℝ) : ℂ) * I) *
          discV K.σ.vertexTwo z)) := by
  have he : K.σ.eps = -1 := by
    unfold CompactShape.eps
    rw [K.hσ]
    rfl
  have hv := conj_vertexTwo_sph K.σ
  change conj (K.σ.discInv K.σ.vertexTwo (K.σ.reflTwoAux z)) = _
  unfold CompactShape.discInv CompactShape.reflTwoAux
  rw [disc_of_sph K.hσ, he]
  have hc : conj (exp (-(2 * (K.σ.θ₂ : ℂ) * I))) =
      exp (((2 * Real.pi / K.σ.p₂ : ℝ) : ℂ) * I) := by
    rw [← exp_conj, CompactShape.θ₂]
    congr 1
    simp only [map_neg, map_mul, conj_ofReal, conj_I, map_ofNat]
    push_cast
    ring
  simp only [map_div₀, map_add, map_mul, map_one, conj_conj, hv, hc, conj_ofReal]
  congr 1
  push_cast
  ring

theorem planeOf_screwChart (v : ℂ) (θ s : ℝ) (x : ModelCoordinates) :
    planeOf (screwChart v θ s x) = (exp (θ * I) * discV v (planeOf x) + v) /
      (1 - conj v * (exp (θ * I) * discV v (planeOf x))) := by
  rw [screwChart, uncentred, planeOf_ofPlane, planeOf_screwDiffeomorph, planeOf_centred]

theorem liftM_screwTwoInv {y : ModelCoordinates} (hV : planeOf y ∈ K.D.V 2)
    (hre1 : -(3 / 2) < (K.D.f (planeOf y)).re) (hre2 : (K.D.f (planeOf y)).re < 3 / 2)
    (hn : normSq (K.D.f (planeOf y)) ≤ 25 / 4)
    (hx : 1 + conj K.σ.vertexTwo * planeOf y ≠ 0)
    (hy : 1 - conj K.σ.vertexTwo * planeOf (screwDiffeomorph (2 * Real.pi / K.σ.p₂)
      (K.ℓ * K.q₂ / K.σ.p₂) (centred K.σ.vertexTwo y)) ≠ 0)
    (hx' : 1 + conj K.σ.vertexTwo * planeOf (screwChart K.σ.vertexTwo (2 * Real.pi / K.σ.p₂)
      (K.ℓ * K.q₂ / K.σ.p₂) y) ≠ 0)
    (hslit : 1 + conj K.σ.vertexTwo * K.σ.refl 2 (planeOf y) ∈ slitPlane)
    (hclose : psiS K.σ.vertexOne (planeOf y) + psiS K.σ.vertexOne (K.σ.refl 2 (planeOf y)) -
      psiS K.σ.vertexTwo (planeOf y) - psiS K.σ.vertexTwo (K.σ.refl 2 (planeOf y)) =
        K.ℓ * K.phase.e) :
    K.liftM (screwChart K.σ.vertexTwo (2 * Real.pi / K.σ.p₂) (K.ℓ * K.q₂ / K.σ.p₂) y) =
      K.liftP y := by
  set z := planeOf y with hzdef
  set y' := screwChart K.σ.vertexTwo (2 * Real.pi / K.σ.p₂) (K.ℓ * K.q₂ / K.σ.p₂) y with hy'
  have hz' : planeOf y' = conj (K.σ.refl 2 z) := by
    rw [hy', planeOf_screwChart, conj_refl_two_sph]
  have hfl : K.D.f (K.σ.refl 2 z) = conj (K.D.f z) := K.D.f_refl 2 z hV
  obtain ⟨-, m, hm⟩ := centred_screwChart hx hy hx'
  rw [← hy'] at hm
  have hψ' : psiS K.σ.vertexTwo (planeOf y') = -psiS K.σ.vertexTwo (K.σ.refl 2 z) := by
    rw [hz']
    exact psiS_conj_of_real (conj_vertexTwo_sph K.σ) hslit
  have ht : y' 2 = y 2 + K.ℓ * K.q₂ / K.σ.p₂ - psiS K.σ.vertexTwo (K.σ.refl 2 z) -
      psiS K.σ.vertexTwo z + 2 * Real.pi * m := by
    have h1 : centred K.σ.vertexTwo y' 2 = y' 2 - psiS K.σ.vertexTwo (planeOf y') := by
      simp only [centred, ofPlane_apply_two, psiS]
      ring
    have h2 : centred K.σ.vertexTwo y 2 = y 2 - psiS K.σ.vertexTwo z := by
      simp only [centred, ofPlane_apply_two, psiS, ← hzdef]
      ring
    rw [h1, h2, hψ'] at hm
    linarith
  have hθ := K.phase.theta_wallTwo (z := z) (z' := K.σ.refl 2 z) hre1 hre2 hn K.ℓ_ne hclose
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, hz', Complex.conj_conj, hfl, Complex.conj_conj, reflectMap_two]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  apply Circle.exp_eq_exp.2
  refine ⟨K.n * m, ?_⟩
  rw [ht]
  have hℓ := K.ℓ_ne
  have hp2 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
  have hper := K.period
  simp only [phase_k₁, phase_ℓ] at hθ
  have hk2 : K.k₂ = K.q₂ / K.σ.p₂ := rfl
  unfold c₀
  rw [hk2]
  push_cast
  field_simp
  field_simp at hθ
  simp only [phase_v₂] at hθ
  simp only [← hzdef]
  linear_combination (K.σ.p₂ : ℝ) * hθ + 2 * Real.pi * (K.σ.p₂ : ℝ) * m * hper

end WallTwo

end SphDatum

end Sph

end ClosedTriangle

end GC.Seifert
