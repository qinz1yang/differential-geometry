import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldConeCorner

/-!
# Wall equivariance of the cone corner

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §5, and the
errata after review 15). The reflections in the walls through the cone vertex `v₁` act on the
disc coordinate `ω₁ = coneDisc v₁ z` by `ω₁ ↦ conj ω₁` (wall 1) and `ω₁ ↦ e^{2iθ₁} conj ω₁`
(wall 2), so they preserve the virtual height `η₁` (`etaOne_refl_one`, `etaOne_refl_two`) and act
on the angle `φ = discAngle ω₁` by `φ ↦ -φ` (`discAngle_discOne_refl_one`) and, away from the ray
`φ = 2θ₁ - π`, by `φ ↦ 2θ₁ - φ` (`discAngle_discOne_refl_two`). The bridge angles about `-3/2`
are odd about their wall values (`angleOneCone_refl_one`, `angleTwoCone_refl_two`), and the apex
angle `π - pφ` is odd about `π` (wall 1) and about `0` (wall 2, using `p θ₁ = π`). Hence the cone
corner is equivariant (`cornerCone_refl_one` where `|φ| ≤ φa`, `cornerCone_refl_two` where
`φb ≤ φ` at the point and at its mirror), and so is the apex model before the mirror
(`apexBefore_refl_one`, `apexBefore_refl_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

theorem discAngle_conj (w : ℂ) : discAngle (conj w) = -discAngle w := by
  rw [discAngle, discAngle, Complex.norm_conj, conj_re, conj_im, halfArg_neg]

theorem discAngle_zero : discAngle 0 = 0 := by
  simp [discAngle, halfArg]

theorem norm_exp_two_mul_I (θ : ℝ) : ‖exp (2 * (θ : ℂ) * I)‖ = 1 := by
  rw [show 2 * (θ : ℂ) * I = ((2 * θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem exp_neg_mul_I_eq_conj (θ : ℝ) : exp (((-θ : ℝ) : ℂ) * I) = conj (exp ((θ : ℂ) * I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

namespace ConeShape

variable (σ : ConeShape)

theorem etaOne_refl_one (z : ℂ) : σ.etaOne (σ.refl 1 z) = σ.etaOne z := by
  simp only [etaOne, coneHeight, σ.coneDisc_vertexOne_refl_one, Complex.norm_conj]

theorem ne_centre_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ≠ σ.centre :=
  sub_ne_zero.1 (σ.centre_ne hz)

theorem discOne_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.discOne (σ.refl 2 z) = conj (σ.discOne z) * exp (((2 * σ.θ₁ : ℝ) : ℂ) * I) := by
  rw [discOne, σ.coneDisc_vertexOne_refl_two (σ.ne_centre_of_im_pos hz), mul_comm, discOne]
  push_cast
  ring_nf

theorem norm_discOne_refl_two {z : ℂ} (hz : 0 < z.im) :
    ‖σ.discOne (σ.refl 2 z)‖ = ‖σ.discOne z‖ := by
  rw [σ.discOne_refl_two hz, norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem etaOne_refl_two {z : ℂ} (hz : 0 < z.im) : σ.etaOne (σ.refl 2 z) = σ.etaOne z := by
  simp only [etaOne, coneHeight]
  rw [← discOne, ← discOne, σ.norm_discOne_refl_two hz]

theorem discAngle_discOne_refl_one (z : ℂ) :
    discAngle (σ.discOne (σ.refl 1 z)) = -discAngle (σ.discOne z) := by
  rw [discOne_refl_one, discAngle_conj]

theorem discAngle_discOne_refl_two {z : ℂ} (hz : z ∈ σ.domOne)
    (hφ : 2 * σ.θ₁ - Real.pi < discAngle (σ.discOne z)) :
    discAngle (σ.discOne (σ.refl 2 z)) = 2 * σ.θ₁ - discAngle (σ.discOne z) := by
  have hm : discAngle (σ.discOne z) ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hθ := σ.θ₁_pos
  have hθ' := σ.θ₁_le
  have h0 : conj (σ.discOne z) ≠ 0 := by
    rw [map_ne_zero]
    exact σ.discOne_ne_zero hz
  have hpos : 0 < ‖conj (σ.discOne z)‖ + (conj (σ.discOne z)).re := by
    rw [Complex.norm_conj, conj_re]
    exact hz.2
  rw [σ.discOne_refl_two hz.1, discAngle_mul_exp h0 hpos, discAngle_conj]
  · ring
  · rw [discAngle_conj]
    linarith [hm.2]
  · rw [discAngle_conj]
    linarith

theorem angleOneCone_refl_one (z : ℂ) :
    σ.angleOneCone (σ.refl 1 z) = 2 * Real.pi - σ.angleOneCone z := by
  rw [angleOneCone, angleOneCone, σ.bridgeOne_refl_one, σ.etaOne_refl_one, conj_re, conj_im,
    negHalfArg_neg]

theorem angleTwoCone_refl_two (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    σ.angleTwoCone (σ.refl 2 z) = -σ.angleTwoCone z := by
  rw [angleTwoCone, angleTwoCone, σ.bridgeTwo_refl_two hθ hz, σ.etaOne_refl_two hz, conj_re,
    conj_im, halfArg_neg]

theorem angleCone_refl_one (p : ℕ) {a b φa φb : ℝ} (hφ : φa < φb) (z : ℂ)
    (hl : |discAngle (σ.discOne z)| ≤ φa) :
    σ.angleCone p a b φa φb (σ.refl 1 z) = 2 * Real.pi - σ.angleCone p a b φa φb z := by
  have h1 : discAngle (σ.discOne z) ≤ φa := le_trans (le_abs_self _) hl
  have h2 : -discAngle (σ.discOne z) ≤ φa := le_trans (neg_le_abs _) hl
  rw [angleCone, angleCone, angleConeBlend, angleConeBlend, coneLambda, coneLambda,
    σ.etaOne_refl_one, σ.discAngle_discOne_refl_one, coneStep_eq_zero hφ h1,
    coneStep_eq_zero hφ h2, σ.angleOneCone_refl_one]
  ring

theorem cornerCone_refl_one (p : ℕ) {a b φa φb : ℝ} (hφ : φa < φb) (z : ℂ)
    (hl : |discAngle (σ.discOne z)| ≤ φa) :
    σ.cornerCone p a b φa φb (σ.refl 1 z) = conj (σ.cornerCone p a b φa φb z) := by
  rw [cornerCone, cornerCone, σ.angleCone_refl_one p hφ z hl, σ.etaOne_refl_one, map_add,
    map_mul, Complex.conj_ofReal, exp_two_pi_sub_mul_I]
  simp [map_neg, map_div₀, map_ofNat]

theorem angleCone_refl_two (hθ : σ.θ₂ = 0) {p : ℕ} (hp : σ.θ₁ * p = Real.pi) {a b φa φb : ℝ}
    (hφ : φa < φb) (hb0 : 0 < φb) {z : ℂ} (hz : z ∈ σ.domOne)
    (hl : φb ≤ discAngle (σ.discOne z)) (hl' : φb ≤ 2 * σ.θ₁ - discAngle (σ.discOne z)) :
    σ.angleCone p a b φa φb (σ.refl 2 z) = -σ.angleCone p a b φa φb z := by
  have hθ1 := σ.θ₁_le
  have hφ0 : 2 * σ.θ₁ - Real.pi < discAngle (σ.discOne z) := by linarith
  have hr := σ.discAngle_discOne_refl_two hz hφ0
  rw [angleCone, angleCone, angleConeBlend, angleConeBlend, coneLambda, coneLambda,
    σ.etaOne_refl_two hz.1, hr, coneStep_eq_one hφ hl, coneStep_eq_one hφ hl',
    σ.angleTwoCone_refl_two hθ hz.1]
  have e : (p : ℝ) * (2 * σ.θ₁ - discAngle (σ.discOne z)) =
      2 * Real.pi - p * discAngle (σ.discOne z) := by
    rw [← hp]
    ring
  rw [e]
  ring

theorem cornerCone_refl_two (hθ : σ.θ₂ = 0) {p : ℕ} (hp : σ.θ₁ * p = Real.pi) {a b φa φb : ℝ}
    (hφ : φa < φb) (hb0 : 0 < φb) {z : ℂ} (hz : z ∈ σ.domOne)
    (hl : φb ≤ discAngle (σ.discOne z)) (hl' : φb ≤ 2 * σ.θ₁ - discAngle (σ.discOne z)) :
    σ.cornerCone p a b φa φb (σ.refl 2 z) = conj (σ.cornerCone p a b φa φb z) := by
  rw [cornerCone, cornerCone, σ.angleCone_refl_two hθ hp hφ hb0 hz hl hl', σ.etaOne_refl_two hz.1,
    map_add, map_mul, Complex.conj_ofReal, ← exp_neg_mul_I_eq_conj]
  simp [map_neg, map_div₀, map_ofNat]

def apexBefore (p : ℕ) (z : ℂ) : ℂ := -(3 / 2) - conj (σ.discOne z) ^ p / 2

theorem apexBefore_eq (p : ℕ) (z : ℂ) :
    σ.apexBefore p z = -conj (σ.coneApexOne p z) := by
  simp only [apexBefore, coneApexOne, discOne, map_add, map_div₀, map_pow, map_ofNat]
  ring

theorem apexBefore_refl_one (p : ℕ) (z : ℂ) :
    σ.apexBefore p (σ.refl 1 z) = conj (σ.apexBefore p z) := by
  rw [apexBefore_eq, apexBefore_eq, σ.coneApexOne_refl_one, map_neg]

theorem apexBefore_refl_two {p : ℕ} (hp : σ.θ₁ * p = Real.pi) {z : ℂ} (hz : 0 < z.im) :
    σ.apexBefore p (σ.refl 2 z) = conj (σ.apexBefore p z) := by
  rw [apexBefore_eq, apexBefore_eq, σ.coneApexOne_refl_two hp hz, map_neg]

end ConeShape

end GC.Seifert
