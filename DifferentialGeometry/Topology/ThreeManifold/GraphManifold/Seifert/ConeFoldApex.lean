import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldTriangle
import DifferentialGeometry.Tensor.LinearAlgebra.ComplexDeterminant
import DifferentialGeometry.Compat.Ch567.Tensor.LinearAlgebra.ComplexDeterminant

/-!
# The branched model at a cone vertex

Lane A4, tier 1 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §0 (i),
§5). At the vertex `v₁` of a `ConeShape` with `θ₁ = π/p` the fold is prescribed to be
`coneApexOne σ p z = 3/2 + ω^p/2`, `ω = coneDisc v₁ z`; at a cone vertex `v₂` with `θ₂ = π/q` it
is `coneApexTwo σ q z = -3/2 - ω₂^q/2`. These are the base maps of the filled carrier's cone
chart `conePoint (3ω, 1) = 3/2 + ω^p/2` (`SF/FilledCarrier.lean:77`) and of the seam model of
`SF/BlockCharts.lean`. Both are holomorphic on the upper half-plane, so their real Jacobian is
`|f'|²` (`det_fderiv_of_hasDerivAt`), positive off the vertex and zero at it (the branched
point, review 9 §3.1). The wall reflections through the vertex act by `ω ↦ ω̄` and
`ω ↦ e^{2iθ} ω̄`, so `p θ₁ = π` gives the wall identities `f ∘ refl = conj ∘ f` on the whole
upper half-plane (`coneApexOne_refl_one`, `coneApexOne_refl_two`), and the models are invariant
under the rotation `refl 1 ∘ refl 2` about the vertex, which is `ω ↦ e^{-2iθ₁} ω`.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

theorem det_fderiv_of_hasDerivAt {f : ℂ → ℂ} {z d : ℂ} (h : HasDerivAt f d z) :
    (fderiv ℝ f z).det = normSq d := by
  have hF : HasFDerivAt f ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ)
      z := h.hasFDerivAt.restrictScalars ℝ
  rw [hF.fderiv, ContinuousLinearMap.det, LinearMap.det_complex]
  simp only [ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul, one_mul, mul_re, mul_im, I_re, I_im, normSq_apply]
  ring

theorem hasDerivAt_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    HasDerivAt (coneDisc v) ((v - conj v) / (z - conj v) ^ 2) z := by
  have h := sub_conj_ne_zero hv hz
  have h1 : HasDerivAt (fun w : ℂ => w - v) 1 z := (hasDerivAt_id z).sub_const v
  have h2 : HasDerivAt (fun w : ℂ => w - conj v) 1 z := (hasDerivAt_id z).sub_const (conj v)
  have e : (v - conj v) / (z - conj v) ^ 2 =
      (1 * (z - conj v) - (z - v) * 1) / (z - conj v) ^ 2 := by
    congr 1
    ring
  rw [e]
  exact h1.div h2 h

theorem contDiffAt_coneDisc {v z : ℂ} (hv : 0 < v.im) (hz : 0 < z.im) :
    ContDiffAt ℂ ∞ (coneDisc v) z := by
  have h := sub_conj_ne_zero hv hz
  exact (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.sub contDiffAt_const) h

namespace ConeShape

variable (σ : ConeShape)

def coneApexOne (p : ℕ) (z : ℂ) : ℂ := 3 / 2 + coneDisc σ.vertexOne z ^ p / 2

def coneApexTwo (q : ℕ) (z : ℂ) : ℂ := -(3 / 2) - coneDisc σ.vertexTwo z ^ q / 2

theorem coneApexOne_vertexOne {p : ℕ} (hp : p ≠ 0) : σ.coneApexOne p σ.vertexOne = 3 / 2 := by
  simp [coneApexOne, coneDisc_self, zero_pow hp]

theorem coneApexOne_refl_one (p : ℕ) (z : ℂ) :
    σ.coneApexOne p (σ.refl 1 z) = conj (σ.coneApexOne p z) := by
  simp [coneApexOne, coneDisc_vertexOne_refl_one, map_ofNat]

theorem exp_two_mul_pow_eq_one {θ : ℝ} {p : ℕ} (h : θ * p = Real.pi) :
    exp (2 * θ * I) ^ p = 1 := by
  rw [← Complex.exp_nat_mul, show (p : ℂ) * (2 * θ * I) = (2 * Real.pi * I) * 1 by
    rw [← h]
    push_cast
    ring]
  exact Complex.exp_int_mul_two_pi_mul_I 1 ▸ by simp

theorem coneApexOne_refl_two {p : ℕ} (hθ : σ.θ₁ * p = Real.pi) {z : ℂ} (hz : 0 < z.im) :
    σ.coneApexOne p (σ.refl 2 z) = conj (σ.coneApexOne p z) := by
  have hc : z ≠ σ.centre := sub_ne_zero.1 (σ.centre_ne hz)
  simp only [coneApexOne, σ.coneDisc_vertexOne_refl_two hc, mul_pow,
    exp_two_mul_pow_eq_one hθ, one_mul, map_add, map_div₀, map_pow, map_ofNat]

theorem coneApexOne_rotate {p : ℕ} (hθ : σ.θ₁ * p = Real.pi) {z : ℂ} (hz : 0 < z.im) :
    σ.coneApexOne p (σ.refl 1 (σ.refl 2 z)) = σ.coneApexOne p z := by
  rw [coneApexOne_refl_one, coneApexOne_refl_two σ hθ hz, Complex.conj_conj]

theorem hasDerivAt_coneApexOne (p : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (σ.coneApexOne p)
      (p * coneDisc σ.vertexOne z ^ (p - 1) *
        ((σ.vertexOne - conj σ.vertexOne) / (z - conj σ.vertexOne) ^ 2) / 2) z := by
  have h := ((hasDerivAt_coneDisc σ.vertexOne_im_pos hz).pow p).div_const 2
  exact h.const_add (3 / 2)

theorem contDiffOn_coneApexOne (p : ℕ) :
    ContDiffOn ℝ ∞ (σ.coneApexOne p) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h := ((contDiffAt_coneDisc σ.vertexOne_im_pos hz).pow p).div_const 2
  exact ((contDiffAt_const.add h).restrict_scalars ℝ).contDiffWithinAt

theorem det_fderiv_coneApexOne_pos {p : ℕ} (hp : p ≠ 0) {z : ℂ} (hz : 0 < z.im)
    (hzv : z ≠ σ.vertexOne) : 0 < (fderiv ℝ (σ.coneApexOne p) z).det := by
  rw [det_fderiv_of_hasDerivAt (σ.hasDerivAt_coneApexOne p hz)]
  apply normSq_pos.2
  have h1 : coneDisc σ.vertexOne z ≠ 0 := by
    rw [coneDisc]
    exact div_ne_zero (sub_ne_zero.2 hzv) (sub_conj_ne_zero σ.vertexOne_im_pos hz)
  have h2 : σ.vertexOne - conj σ.vertexOne ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [σ.vertexOne_im_pos]
  have h3 := sub_conj_ne_zero σ.vertexOne_im_pos hz
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hp' (pow_ne_zero _ h1))
    (div_ne_zero h2 (pow_ne_zero _ h3))) two_ne_zero

end ConeShape

end GC.Seifert
