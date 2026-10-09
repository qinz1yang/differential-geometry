import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphCornerThree

/-!
# The apex germs of the spherical compact fold

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §0 and §4). The rotated disc coordinates are Möbius
maps, holomorphic off the antipode of their vertex with nonvanishing derivative
(`hasDerivAt_rotOne_sph`, `hasDerivAt_rotTwo_sph`), so the apex models `3/2 + rotOne^{p₁}/2` and
`-3/2 + rotTwo^{p₂}/2` are smooth there (`contDiffAt_sphApexOne`, `contDiffAt_sphApexTwo`) and have
positive Jacobian off their vertex (`det_fderiv_sphApexOne_pos`, `det_fderiv_sphApexTwo_pos`). The
outer germ at `v₃ = 0` is the curvature-free `compactOuterGerm` (`CompactFoldGerms`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem hasDerivAt_sphMoeb {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    HasDerivAt (sphMoeb a) ((1 + conj a * a) / (1 + conj a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun u : ℂ => u - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun u : ℂ => 1 + conj a * u) (conj a) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_add 1
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

namespace CompactShape

variable {σ : CompactShape}

def sphApexOne (σ : CompactShape) (z : ℂ) : ℂ := 3 / 2 + σ.rotOne z ^ σ.p₁ / 2

def sphApexTwo (σ : CompactShape) (z : ℂ) : ℂ := -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem hasDerivAt_rotOne_sph {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0) :
    HasDerivAt σ.rotOne (-exp (-((σ.θ₃ : ℂ) * I)) *
      ((1 + conj σ.vertexOne * σ.vertexOne) / (1 + conj σ.vertexOne * z) ^ 2)) z := by
  have e : σ.rotOne = fun w => -exp (-((σ.θ₃ : ℂ) * I)) * sphMoeb σ.vertexOne w :=
    funext (rotOne_eq_mul_sph hs)
  rw [e]
  exact (hasDerivAt_sphMoeb h).const_mul _

theorem hasDerivAt_rotTwo_sph {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    HasDerivAt σ.rotTwo (-exp ((σ.θ₂ : ℂ) * I) *
      ((1 + conj σ.vertexTwo * σ.vertexTwo) / (1 + conj σ.vertexTwo * z) ^ 2)) z := by
  rw [rotTwo_eq_fun_sph hs]
  exact (hasDerivAt_sphMoeb (by rwa [conj_vertexTwo_sph])).const_mul _

theorem contDiffAt_sphApexOne {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0) :
    ContDiffAt ℝ ∞ σ.sphApexOne z :=
  contDiffAt_const.add (((contDiffAt_rotOne_sph hs h).pow σ.p₁).div_const 2)

theorem contDiffAt_sphApexTwo {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ContDiffAt ℝ ∞ σ.sphApexTwo z :=
  contDiffAt_const.add (((contDiffAt_rotTwo_sph hs h).pow σ.p₂).div_const 2)

theorem det_fderiv_sphApexOne_pos {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0)
    (hz : σ.rotOne z ≠ 0) : 0 < (fderiv ℝ σ.sphApexOne z).det := by
  have hd : HasDerivAt σ.sphApexOne ((σ.p₁ : ℂ) * σ.rotOne z ^ (σ.p₁ - 1) *
      (-exp (-((σ.θ₃ : ℂ) * I)) *
        ((1 + conj σ.vertexOne * σ.vertexOne) / (1 + conj σ.vertexOne * z) ^ 2)) / 2) z :=
    (((hasDerivAt_rotOne_sph hs h).pow σ.p₁).div_const 2).const_add (3 / 2)
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hp : (σ.p₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₁; omega)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hz))
    (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _))
      (div_ne_zero (one_add_conj_mul_self_ne_sph _) (pow_ne_zero _ h)))) two_ne_zero

theorem det_fderiv_sphApexTwo_pos {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0)
    (hz : σ.rotTwo z ≠ 0) : 0 < (fderiv ℝ σ.sphApexTwo z).det := by
  have hd : HasDerivAt σ.sphApexTwo ((σ.p₂ : ℂ) * σ.rotTwo z ^ (σ.p₂ - 1) *
      (-exp ((σ.θ₂ : ℂ) * I) *
        ((1 + conj σ.vertexTwo * σ.vertexTwo) / (1 + conj σ.vertexTwo * z) ^ 2)) / 2) z :=
    (((hasDerivAt_rotTwo_sph hs h).pow σ.p₂).div_const 2).const_add (-(3 / 2))
  rw [det_fderiv_of_hasDerivAt hd]
  apply normSq_pos.2
  have hp : (σ.p₂ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := σ.two_le_p₂; omega)
  have h' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ hz))
    (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _))
      (div_ne_zero (one_add_conj_mul_self_ne_sph _) (pow_ne_zero _ h')))) two_ne_zero

end Spherical

end CompactShape

end GC.Seifert
