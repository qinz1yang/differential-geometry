import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidBridges
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldConeCorner

/-!
# Angles of the flat bridges along circles about the vertices

Lane CF, tier 2, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The circle about `c` through `z` is
`circ c z t = c + (z - c) e^{it}`. Along it the distance to `c` is constant, and the distances to
the other vertices and the side functions have explicit derivatives
(`hasDerivAt_norm_curve`, `hasDerivAt_wallSide_*_curve`, and the inner-product identities
`inner_circ_*`): for instance along a circle about `v₁` the distance to `v₃ = 0` has derivative
`sin θ₂ · wallSide 1 / ‖z‖`.

The angles of the bridges about the centres of the target are written with A4's `halfArg` (bridge
point on the positive side of the centre) and `negHalfArg` (negative side): about `+3/2` the
angles `angleOneAtOne` (of `bridgeOne`, `0` on wall 1) and `angleTwoAtOne` (of `bridgeTwo`, `π` on
wall 2); about `-3/2` the angles `angleTwoAtTwo` (`0` on wall 2) and `angleZeroAtTwo` (`π` on
wall 0); about `0` the angles `angleOneAtThree` (`0` on wall 1) and `angleZeroAtThree` (`π` on
wall 0). By A4's derivative formula for a `twoCircle` along a curve on which its first radius
is constant (`hasDerivAt_halfArg_twoCircle'`), the angles about `±3/2` strictly increase along
the circles about `v₁`, `v₂` in the direction of increasing `t` (from the first wall of the
sector towards the second), and the angles about `0` strictly decrease along the circles about
`v₃ = 0` (from wall 0 towards wall 1): `exists_hasDerivAt_angleOneAtOne` and its five siblings.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

def circ (c z : ℂ) (t : ℝ) : ℂ := c + (z - c) * exp ((t : ℂ) * I)

theorem circ_zero (c z : ℂ) : circ c z 0 = z := by
  simp [circ]

theorem hasDerivAt_circ (c z : ℂ) : HasDerivAt (circ c z) ((z - c) * I) 0 := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp.const_mul
    (z - c)).const_add c
  have h' : HasDerivAt (circ c z)
      ((z - c) * (exp (Complex.ofRealCLM 0 * I) * (Complex.ofRealCLM 1 * I))) 0 := h
  refine h'.congr_deriv ?_
  simp

theorem continuous_circ (c z : ℂ) : Continuous (circ c z) := by
  unfold circ
  fun_prop

theorem norm_circ_sub (c z : ℂ) (t : ℝ) : ‖circ c z t - c‖ = ‖z - c‖ := by
  rw [circ, add_sub_cancel_left, norm_mul, norm_exp_ofReal_mul_I, mul_one]

theorem hasDerivAt_norm_curve {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) (q : ℂ)
    (h : γ 0 ≠ q) :
    HasDerivAt (fun t => ‖γ t - q‖)
      (((γ 0 - q).re * V.re + (γ 0 - q).im * V.im) / ‖γ 0 - q‖) 0 := by
  have hn := hasDerivAt_normSq_curve hγ q
  have h0 : normSq (γ 0 - q) ≠ 0 := normSq_eq_zero.not.2 (sub_ne_zero.2 h)
  have hs := hn.sqrt h0
  have e : (fun t => ‖γ t - q‖) = fun t => Real.sqrt (normSq (γ t - q)) := by
    funext t
    rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [e]
  refine hs.congr_deriv ?_
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem eventually_circ_mem {c z : ℂ} {s : Set ℂ} (hs : IsOpen s) (hz : z ∈ s) :
    ∀ᶠ t in 𝓝 (0 : ℝ), circ c z t ∈ s := by
  have hc : ContinuousAt (circ c z) 0 := (continuous_circ c z).continuousAt
  rw [ContinuousAt, circ_zero] at hc
  exact hc (hs.mem_nhds hz)

theorem differentiableAt_comp_circ {f : ℂ → ℝ} {c z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    DifferentiableAt ℝ (fun t => f (circ c z t)) 0 := by
  have hf' : DifferentiableAt ℝ f (circ c z 0) := by
    rw [circ_zero]
    exact hf.differentiableAt (by simp)
  exact hf'.comp 0 (hasDerivAt_circ c z).differentiableAt

theorem hasDerivAt_halfArg_circ {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ} {c z : ℂ}
    {κ w' : ℝ} (hA0 : 0 < A z) (hA : ∀ t, A (circ c z t) = A z)
    (hB : HasDerivAt (fun t => B (circ c z t)) (W z * κ) 0)
    (hW : HasDerivAt (fun t => W (circ c z t)) w' 0) (hP : ContDiffAt ℝ ∞ P z)
    {s : Set ℂ} (hs : IsOpen s) (hz : z ∈ s) (hPs : ∀ u ∈ s, 0 < P u)
    (hH : ∀ u ∈ s, ((A u + B u) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A u - B u) ^ 2) =
      W u ^ 2 * P u)
    (hpos : 0 < A z + ((twoCircle a b (A z) (B z) (W z) (P z)).re - a)) :
    HasDerivAt (fun t => halfArg (A (circ c z t))
        ((twoCircle a b (A (circ c z t)) (B (circ c z t)) (W (circ c z t))
          (P (circ c z t))).re - a)
        (twoCircle a b (A (circ c z t)) (B (circ c z t)) (W (circ c z t)) (P (circ c z t))).im)
      (if W z = 0 then w' * Real.sqrt (P z) / (2 * |b - a| * A z)
        else 2 * |b - a| * B z * κ / ((b - a) * Real.sqrt (P z))) 0 := by
  simp only [hA]
  have hev := eventually_circ_mem (c := c) hs hz
  have hB' : HasDerivAt (fun t => B (circ c z t)) ((fun t => W (circ c z t)) 0 * κ) 0 := by
    simpa only [circ_zero] using hB
  have h := hasDerivAt_halfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (circ c z t)) (w := fun t => W (circ c z t)) (P := fun t => P (circ c z t))
    hab hA0 hB' hW (differentiableAt_comp_circ hP) (hev.mono fun t ht => hPs _ ht)
    (hev.mono fun t ht => by rw [← hA t]; exact hH _ ht) (by simpa only [circ_zero] using hpos)
  simpa only [circ_zero] using h

theorem hasDerivAt_negHalfArg_circ {a b : ℝ} (hab : a ≠ b) {A B W P : ℂ → ℝ} {c z : ℂ}
    {κ w' : ℝ} (hA0 : 0 < A z) (hA : ∀ t, A (circ c z t) = A z)
    (hB : HasDerivAt (fun t => B (circ c z t)) (W z * κ) 0)
    (hW : HasDerivAt (fun t => W (circ c z t)) w' 0) (hP : ContDiffAt ℝ ∞ P z)
    {s : Set ℂ} (hs : IsOpen s) (hz : z ∈ s) (hPs : ∀ u ∈ s, 0 < P u)
    (hH : ∀ u ∈ s, ((A u + B u) ^ 2 - (b - a) ^ 2) * ((b - a) ^ 2 - (A u - B u) ^ 2) =
      W u ^ 2 * P u)
    (hpos : 0 < A z - ((twoCircle a b (A z) (B z) (W z) (P z)).re - a)) :
    HasDerivAt (fun t => negHalfArg (A (circ c z t))
        ((twoCircle a b (A (circ c z t)) (B (circ c z t)) (W (circ c z t))
          (P (circ c z t))).re - a)
        (twoCircle a b (A (circ c z t)) (B (circ c z t)) (W (circ c z t)) (P (circ c z t))).im)
      (if W z = 0 then -(w' * Real.sqrt (P z) / (2 * |b - a| * A z))
        else 2 * |b - a| * B z * κ / ((b - a) * Real.sqrt (P z))) 0 := by
  simp only [hA]
  have hev := eventually_circ_mem (c := c) hs hz
  have hB' : HasDerivAt (fun t => B (circ c z t)) ((fun t => W (circ c z t)) 0 * κ) 0 := by
    simpa only [circ_zero] using hB
  have h := hasDerivAt_negHalfArg_twoCircle' (a := a) (b := b) (A₀ := A z)
    (B := fun t => B (circ c z t)) (w := fun t => W (circ c z t)) (P := fun t => P (circ c z t))
    hab hA0 hB' hW (differentiableAt_comp_circ hP) (hev.mono fun t ht => hPs _ ht)
    (hev.mono fun t ht => by rw [← hA t]; exact hH _ ht) (by simpa only [circ_zero] using hpos)
  simpa only [circ_zero] using h

namespace EuclidShape

variable (σ : EuclidShape)

theorem hasDerivAt_wallSide_zero_curve {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => σ.wallSide 0 (γ t)) V.im 0 := by
  have h : HasDerivAt (fun t => (γ t).im) V.im 0 := by
    refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  exact h

theorem hasDerivAt_wallSide_one_curve {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => σ.wallSide 1 (γ t))
      (Real.sin σ.θ₃ * V.re - Real.cos σ.θ₃ * V.im) 0 := by
  have hre : HasDerivAt (fun t => (γ t).re) V.re 0 := by
    refine (reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have him : HasDerivAt (fun t => (γ t).im) V.im 0 := by
    refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have e : (fun t => σ.wallSide 1 (γ t)) =
      fun t => Real.sin σ.θ₃ * (γ t).re - Real.cos σ.θ₃ * (γ t).im := by
    funext t
    rw [wallSide_one_apply]
  rw [e]
  exact (hre.const_mul _).sub (him.const_mul _)

theorem hasDerivAt_wallSide_two_curve {γ : ℝ → ℂ} {V : ℂ} (hγ : HasDerivAt γ V 0) :
    HasDerivAt (fun t => σ.wallSide 2 (γ t))
      (-(Real.sin σ.θ₂ * V.re) - Real.cos σ.θ₂ * V.im) 0 := by
  have hre : HasDerivAt (fun t => (γ t).re) V.re 0 := by
    refine (reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have him : HasDerivAt (fun t => (γ t).im) V.im 0 := by
    refine (imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
    simp
  have e : (fun t => σ.wallSide 2 (γ t)) = fun t => Real.sin σ.θ₁ * Real.sin σ.θ₂ -
      Real.sin σ.θ₂ * (γ t).re - Real.cos σ.θ₂ * (γ t).im := by
    funext t
    rw [wallSide_two_apply]
  rw [e]
  refine ((hasDerivAt_const _ _).sub (hre.const_mul _)).sub (him.const_mul _) |>.congr_deriv ?_
  ring

theorem vertexOne_re' : σ.vertexOne.re = Real.sin σ.θ₂ * Real.cos σ.θ₃ := by
  simp only [vertexOne, mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem vertexOne_im' : σ.vertexOne.im = Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
  simp only [vertexOne, mul_im, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]

theorem vertexTwo_re' : σ.vertexTwo.re = Real.sin σ.θ₁ := by
  simp only [vertexTwo, ofReal_re]

theorem vertexTwo_im' : σ.vertexTwo.im = 0 := by
  simp only [vertexTwo, ofReal_im]


theorem inner_circOne_zero (z : ℂ) :
    z.re * ((z - σ.vertexOne) * I).re + z.im * ((z - σ.vertexOne) * I).im =
      Real.sin σ.θ₂ * σ.wallSide 1 z := by
  rw [wallSide_one_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexOne_re', σ.vertexOne_im']
  ring

theorem inner_circOne_two (z : ℂ) :
    (z - σ.vertexTwo).re * ((z - σ.vertexOne) * I).re +
      (z - σ.vertexTwo).im * ((z - σ.vertexOne) * I).im = -(Real.sin σ.θ₃ * σ.wallSide 2 z) := by
  have he := σ.sin_θ₁_eq
  rw [wallSide_two_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexOne_re', σ.vertexOne_im',
    σ.vertexTwo_re', σ.vertexTwo_im']
  linear_combination z.im * he

theorem inner_circTwo_zero (z : ℂ) :
    z.re * ((z - σ.vertexTwo) * I).re + z.im * ((z - σ.vertexTwo) * I).im =
      -(Real.sin σ.θ₁ * σ.wallSide 0 z) := by
  rw [wallSide_zero_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexTwo_re', σ.vertexTwo_im']
  ring

theorem inner_circTwo_one (z : ℂ) :
    (z - σ.vertexOne).re * ((z - σ.vertexTwo) * I).re +
      (z - σ.vertexOne).im * ((z - σ.vertexTwo) * I).im = Real.sin σ.θ₃ * σ.wallSide 2 z := by
  have he := σ.sin_θ₁_eq
  rw [wallSide_two_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexOne_re', σ.vertexOne_im',
    σ.vertexTwo_re', σ.vertexTwo_im']
  linear_combination (-(z.im)) * he

theorem inner_circThree_two (z : ℂ) :
    (z - σ.vertexTwo).re * (z * I).re + (z - σ.vertexTwo).im * (z * I).im =
      Real.sin σ.θ₁ * σ.wallSide 0 z := by
  rw [wallSide_zero_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexTwo_re', σ.vertexTwo_im']
  ring

theorem inner_circThree_one (z : ℂ) :
    (z - σ.vertexOne).re * (z * I).re + (z - σ.vertexOne).im * (z * I).im =
      -(Real.sin σ.θ₂ * σ.wallSide 1 z) := by
  rw [wallSide_one_apply]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, σ.vertexOne_re', σ.vertexOne_im']
  ring


theorem hasDerivAt_norm_circ_sub (c z q : ℂ) (h : z ≠ q) :
    HasDerivAt (fun t => ‖circ c z t - q‖)
      (((z - q).re * ((z - c) * I).re + (z - q).im * ((z - c) * I).im) / ‖z - q‖) 0 := by
  have h' := hasDerivAt_norm_curve (hasDerivAt_circ c z) q (by rwa [circ_zero])
  simpa only [circ_zero] using h'

theorem hasDerivAt_modOne_circ (c : ℂ) {z : ℂ} (h : z ≠ σ.vertexOne) :
    HasDerivAt (fun t => σ.modOne (circ c z t)) (profileSlope *
      (((z - σ.vertexOne).re * ((z - c) * I).re + (z - σ.vertexOne).im * ((z - c) * I).im) /
        ‖z - σ.vertexOne‖)) 0 := by
  have hn := hasDerivAt_norm_circ_sub c z σ.vertexOne h
  have h2 := ((hn.sub_const σ.radOne).const_mul profileSlope).const_add (3 / 2)
  exact h2

theorem hasDerivAt_modTwo_circ (c : ℂ) {z : ℂ} (h : z ≠ σ.vertexTwo) :
    HasDerivAt (fun t => σ.modTwo (circ c z t)) (profileSlope *
      (((z - σ.vertexTwo).re * ((z - c) * I).re + (z - σ.vertexTwo).im * ((z - c) * I).im) /
        ‖z - σ.vertexTwo‖)) 0 := by
  have hn := hasDerivAt_norm_circ_sub c z σ.vertexTwo h
  have h2 := ((hn.sub_const σ.radTwo).const_mul profileSlope).const_add (3 / 2)
  exact h2

theorem hasDerivAt_modThree_circ (c : ℂ) {z : ℂ} (h : z ≠ 0) :
    HasDerivAt (fun t => σ.modThree (circ c z t)) (-(profileSlope *
      ((z.re * ((z - c) * I).re + z.im * ((z - c) * I).im) / ‖z‖))) 0 := by
  have hn := hasDerivAt_norm_circ_sub c z 0 h
  simp only [sub_zero] at hn
  have h2 := ((hn.sub_const σ.radThree).const_mul profileSlope).const_sub 3
  exact h2

theorem modOne_circ (z : ℂ) (t : ℝ) : σ.modOne (circ σ.vertexOne z t) = σ.modOne z := by
  change 3 / 2 + profileSlope * (‖circ σ.vertexOne z t - σ.vertexOne‖ - σ.radOne) =
    3 / 2 + profileSlope * (‖z - σ.vertexOne‖ - σ.radOne)
  rw [norm_circ_sub]

theorem modTwo_circ (z : ℂ) (t : ℝ) : σ.modTwo (circ σ.vertexTwo z t) = σ.modTwo z := by
  change 3 / 2 + profileSlope * (‖circ σ.vertexTwo z t - σ.vertexTwo‖ - σ.radTwo) =
    3 / 2 + profileSlope * (‖z - σ.vertexTwo‖ - σ.radTwo)
  rw [norm_circ_sub]

theorem modThree_circ (z : ℂ) (t : ℝ) : σ.modThree (circ 0 z t) = σ.modThree z := by
  change 3 - profileSlope * (‖circ 0 z t‖ - σ.radThree) = 3 - profileSlope * (‖z‖ - σ.radThree)
  have := norm_circ_sub 0 z t
  rw [sub_zero, sub_zero] at this
  rw [this]

theorem wall_deriv_one_one (z : ℂ) :
    Real.sin σ.θ₃ * ((z - σ.vertexOne) * I).re - Real.cos σ.θ₃ * ((z - σ.vertexOne) * I).im =
      (σ.rotOne z).re := by
  simp only [rotOne, neg_re, mul_re, mul_im, sub_re, sub_im, I_re, I_im,
    σ.vertexOne_re', σ.vertexOne_im']
  rw [show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

theorem wall_deriv_one_two (z : ℂ) :
    -(Real.sin σ.θ₂ * ((z - σ.vertexOne) * I).re) - Real.cos σ.θ₂ * ((z - σ.vertexOne) * I).im =
      (σ.rotTwo z).re - Real.sin σ.θ₃ := by
  have h := σ.rotTwo_eq_rotOne z
  have e : (σ.rotTwo z).re - Real.sin σ.θ₃ = -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexOne)).re := by
    have hm := σ.vertexTwo_sub_vertexOne
    rw [rotTwo, show z - σ.vertexTwo = (z - σ.vertexOne) - (σ.vertexTwo - σ.vertexOne) by ring,
      hm, mul_sub, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    simp only [neg_re, sub_re, ofReal_re]
    ring
  rw [e]
  simp only [mul_re, mul_im, sub_re, sub_im, I_re, I_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  ring

theorem wall_deriv_two_two (z : ℂ) :
    -(Real.sin σ.θ₂ * ((z - σ.vertexTwo) * I).re) - Real.cos σ.θ₂ * ((z - σ.vertexTwo) * I).im =
      (σ.rotTwo z).re := by
  simp only [rotTwo, neg_re, mul_re, mul_im, sub_re, sub_im, I_re, I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

theorem wall_deriv_three_one (z : ℂ) :
    Real.sin σ.θ₃ * (z * I).re - Real.cos σ.θ₃ * (z * I).im =
      -(exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
  rw [show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring]
  simp only [mul_re, mul_im, I_re, I_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

def angleOneAtOne (z : ℂ) : ℝ :=
  halfArg (σ.modOne z) ((σ.bridgeOne z).re - 3 / 2) (σ.bridgeOne z).im

def angleTwoAtOne (z : ℂ) : ℝ :=
  negHalfArg (σ.modOne z) ((σ.bridgeTwo z).re - 3 / 2) (σ.bridgeTwo z).im

def angleTwoAtTwo (z : ℂ) : ℝ :=
  halfArg (σ.modTwo z) ((σ.bridgeTwo z).re + 3 / 2) (σ.bridgeTwo z).im

def angleZeroAtTwo (z : ℂ) : ℝ :=
  negHalfArg (σ.modTwo z) ((σ.bridgeZero z).re + 3 / 2) (σ.bridgeZero z).im

def angleOneAtThree (z : ℂ) : ℝ :=
  halfArg (σ.modThree z) (σ.bridgeOne z).re (σ.bridgeOne z).im

def angleZeroAtThree (z : ℂ) : ℝ :=
  negHalfArg (σ.modThree z) (σ.bridgeZero z).re (σ.bridgeZero z).im


theorem contDiffAt_modOne {z : ℂ} (h : z ≠ σ.vertexOne) : ContDiffAt ℝ ∞ σ.modOne z :=
  contDiffAt_const.add (contDiffAt_const.mul (σ.contDiffAt_canon_zero h))

theorem contDiffAt_modTwo {z : ℂ} (h : z ≠ σ.vertexTwo) : ContDiffAt ℝ ∞ σ.modTwo z :=
  contDiffAt_const.add (contDiffAt_const.mul (σ.contDiffAt_canon_one h))

theorem contDiffAt_modThree {z : ℂ} (h : z ≠ 0) : ContDiffAt ℝ ∞ σ.modThree z :=
  contDiffAt_const.sub (contDiffAt_const.mul (σ.contDiffAt_canon_two h))

theorem contDiffAt_cofBridgeOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ σ.cofBridgeOne z := by
  have hA := σ.contDiffAt_modThree (σ.ne_zero_of_mem_domOne hz)
  have hB := σ.contDiffAt_modOne (σ.ne_vertexOne_of_mem_domOne hz)
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul (σ.contDiffAt_cofOneThree hz))

theorem contDiffAt_cofBridgeZero {z : ℂ} (hz : z ∈ σ.domZero) :
    ContDiffAt ℝ ∞ σ.cofBridgeZero z := by
  have hA := σ.contDiffAt_modThree (σ.ne_zero_of_mem_domZero hz)
  have hB := σ.contDiffAt_modTwo (σ.ne_vertexTwo_of_mem_domZero hz)
  exact ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
    (contDiffAt_const.mul (σ.contDiffAt_cofZeroThree hz))

theorem contDiffAt_cofBridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ σ.cofBridgeTwo z := by
  have hA := σ.contDiffAt_modOne (σ.ne_vertexOne_of_mem_domTwo hz)
  have hB := σ.contDiffAt_modTwo (σ.ne_vertexTwo_of_mem_domTwo hz)
  exact (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
    (contDiffAt_const.mul (σ.contDiffAt_cofOneTwo hz))

theorem re_pos_of_im_eq_zero {w : ℂ} (h : 0 < ‖w‖ + w.re) (hi : w.im = 0) : 0 < w.re := by
  have hn : ‖w‖ = |w.re| := by
    rw [← Complex.re_add_im w, hi]
    simp
  rw [hn] at h
  rcases le_or_gt 0 w.re with h' | h'
  · rcases h'.lt_or_eq with h'' | h''
    · exact h''
    · rw [← h''] at h
      simp at h
  · rw [abs_of_neg h'] at h
    linarith

theorem twoCircle_div_sqrt_pos {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : 0 < κ / d) : 0 < 2 * |d| * B * κ / (d * Real.sqrt P) := by
  have hs := Real.sqrt_pos.2 hP
  have e : 2 * |d| * B * κ / (d * Real.sqrt P) = 2 * |d| * B * (κ / d) / Real.sqrt P := by
    field_simp
  rw [e]
  have := abs_pos.2 hd
  positivity

theorem twoCircle_div_sqrt_neg {d B κ P : ℝ} (hd : d ≠ 0) (hB : 0 < B) (hP : 0 < P)
    (hκ : κ / d < 0) : 2 * |d| * B * κ / (d * Real.sqrt P) < 0 := by
  have h := twoCircle_div_sqrt_pos hd hB hP (κ := -κ) (by rw [neg_div]; linarith)
  have e : 2 * |d| * B * -κ / (d * Real.sqrt P) = -(2 * |d| * B * κ / (d * Real.sqrt P)) := by
    ring
  linarith

theorem exists_hasDerivAt_angleOneAtOne {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => σ.angleOneAtOne (circ σ.vertexOne z t)) d 0 := by
  have h0 := σ.ne_zero_of_mem_domOne hz
  have hB0 := σ.modThree_pos hz.2.2
  have hA0 := σ.modOne_pos z
  have hP0 := σ.cofBridgeOne_pos hz
  have hB := σ.hasDerivAt_modThree_circ σ.vertexOne h0
  rw [σ.inner_circOne_zero z] at hB
  have hB' : HasDerivAt (fun t => σ.modThree (circ σ.vertexOne z t))
      (σ.wallSide 1 z * (-(profileSlope * Real.sin σ.θ₂ / ‖z‖))) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_one_curve (hasDerivAt_circ σ.vertexOne z)
  rw [σ.wall_deriv_one_one z] at hW
  have h := hasDerivAt_halfArg_circ (a := 3 / 2) (b := 0) (by norm_num) (A := σ.modOne)
    (B := σ.modThree) (W := σ.wallSide 1) (P := σ.cofBridgeOne) hA0 (σ.modOne_circ z) hB'
    hW (σ.contDiffAt_cofBridgeOne hz) σ.isOpen_domOne hz (fun u hu => σ.cofBridgeOne_pos hu)
    (fun u hu => by have := σ.heron_bridgeOne hu; linear_combination this)
    (by rw [← twoCircle_swap]; exact hpos)
  have e : (fun t => σ.angleOneAtOne (circ σ.vertexOne z t)) = fun t =>
      halfArg (σ.modOne (circ σ.vertexOne z t))
        ((twoCircle (3 / 2) 0 (σ.modOne (circ σ.vertexOne z t))
          (σ.modThree (circ σ.vertexOne z t)) (σ.wallSide 1 (circ σ.vertexOne z t))
          (σ.cofBridgeOne (circ σ.vertexOne z t))).re - 3 / 2)
        (twoCircle (3 / 2) 0 (σ.modOne (circ σ.vertexOne z t))
          (σ.modThree (circ σ.vertexOne z t)) (σ.wallSide 1 (circ σ.vertexOne z t))
          (σ.cofBridgeOne (circ σ.vertexOne z t))).im := by
    funext t
    rw [angleOneAtOne, bridgeOne, twoCircle_swap]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < (σ.rotOne z).re :=
      re_pos_of_im_eq_zero hψ (by rw [← wallSide_one_eq_im_rotOne]; exact hw)
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply twoCircle_div_sqrt_pos (by norm_num) hB0 hP0
    have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
    have : 0 < profileSlope * Real.sin σ.θ₂ / ‖z‖ := by
      have := σ.sin_θ₂_pos
      unfold profileSlope
      positivity
    rw [show (0 : ℝ) - 3 / 2 = -(3 / 2) by norm_num, div_neg]
    have h2 : -(profileSlope * Real.sin σ.θ₂ / ‖z‖) / (3 / 2) < 0 := by
      rw [neg_div]
      have := div_pos this (by norm_num : (0 : ℝ) < 3 / 2)
      linarith
    linarith


theorem norm_sub_vertexOne_eq_rotTwo (z : ℂ) :
    ‖z - σ.vertexOne‖ = ‖(Real.sin σ.θ₃ : ℂ) - σ.rotTwo z‖ := by
  have hm := σ.vertexTwo_sub_vertexOne
  have e : (Real.sin σ.θ₃ : ℂ) - σ.rotTwo z = exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexOne) := by
    rw [rotTwo, show z - σ.vertexTwo = (z - σ.vertexOne) - (σ.vertexTwo - σ.vertexOne) by ring,
      hm, mul_sub, mul_left_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    ring
  rw [e, norm_mul, norm_exp_mul_I, one_mul]

theorem exists_hasDerivAt_angleTwoAtOne {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => σ.angleTwoAtOne (circ σ.vertexOne z t)) d 0 := by
  have h2 := σ.ne_vertexTwo_of_mem_domTwo hz
  have hB0 := σ.modTwo_pos z
  have hA0 := σ.modOne_pos z
  have hP0 := σ.cofBridgeTwo_pos hz
  have hB := σ.hasDerivAt_modTwo_circ σ.vertexOne h2
  rw [σ.inner_circOne_two z] at hB
  have hB' : HasDerivAt (fun t => σ.modTwo (circ σ.vertexOne z t))
      (σ.wallSide 2 z * (-(profileSlope * Real.sin σ.θ₃ / ‖z - σ.vertexTwo‖))) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_two_curve (hasDerivAt_circ σ.vertexOne z)
  rw [σ.wall_deriv_one_two z] at hW
  have h := hasDerivAt_negHalfArg_circ (a := 3 / 2) (b := -(3 / 2)) (by norm_num)
    (A := σ.modOne) (B := σ.modTwo) (W := σ.wallSide 2) (P := σ.cofBridgeTwo) hA0
    (σ.modOne_circ z) hB' hW (σ.contDiffAt_cofBridgeTwo hz) σ.isOpen_domTwo hz
    (fun u hu => σ.cofBridgeTwo_pos hu) (fun u hu => σ.heron_bridgeTwo hu) hpos
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < ((Real.sin σ.θ₃ : ℂ) - σ.rotTwo z).re := by
      apply re_pos_of_im_eq_zero
      · rw [← σ.norm_sub_vertexOne_eq_rotTwo, sub_re, ofReal_re]
        exact hz.2.1
      · rw [sub_im, ofReal_im, zero_sub, neg_eq_zero]
        exact hw
    rw [sub_re, ofReal_re] at hr
    have := Real.sqrt_pos.2 hP0
    have hn : 0 < ((σ.rotTwo z).re - Real.sin σ.θ₃) * -1 := by linarith
    have e : -(((σ.rotTwo z).re - Real.sin σ.θ₃) * Real.sqrt (σ.cofBridgeTwo z) /
        (2 * |-(3 / 2) - 3 / 2| * σ.modOne z)) = (((σ.rotTwo z).re - Real.sin σ.θ₃) * -1) *
        Real.sqrt (σ.cofBridgeTwo z) / (2 * |-(3 / 2) - 3 / 2| * σ.modOne z) := by ring
    rw [e]
    positivity
  · apply twoCircle_div_sqrt_pos (by norm_num) hB0 hP0
    have hn : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have : 0 < profileSlope * Real.sin σ.θ₃ / ‖z - σ.vertexTwo‖ := by
      have := σ.sin_θ₃_pos
      unfold profileSlope
      positivity
    rw [show (-(3 / 2) - 3 / 2 : ℝ) = -3 by norm_num, div_neg, neg_div, neg_neg]
    positivity

theorem exists_hasDerivAt_angleTwoAtTwo {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => σ.angleTwoAtTwo (circ σ.vertexTwo z t)) d 0 := by
  have h1 := σ.ne_vertexOne_of_mem_domTwo hz
  have hB0 := σ.modOne_pos z
  have hA0 := σ.modTwo_pos z
  have hP0 := σ.cofBridgeTwo_pos hz
  have hB := σ.hasDerivAt_modOne_circ σ.vertexTwo h1
  rw [σ.inner_circTwo_one z] at hB
  have hB' : HasDerivAt (fun t => σ.modOne (circ σ.vertexTwo z t))
      (σ.wallSide 2 z * (profileSlope * Real.sin σ.θ₃ / ‖z - σ.vertexOne‖)) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_two_curve (hasDerivAt_circ σ.vertexTwo z)
  rw [σ.wall_deriv_two_two z] at hW
  have h := hasDerivAt_halfArg_circ (a := -(3 / 2)) (b := 3 / 2) (by norm_num)
    (A := σ.modTwo) (B := σ.modOne) (W := σ.wallSide 2) (P := σ.cofBridgeTwo) hA0
    (σ.modTwo_circ z) hB' hW (σ.contDiffAt_cofBridgeTwo hz) σ.isOpen_domTwo hz
    (fun u hu => σ.cofBridgeTwo_pos hu)
    (fun u hu => by have := σ.heron_bridgeTwo hu; linear_combination this)
    (by rw [← twoCircle_swap, sub_neg_eq_add]; exact hpos)
  have e : (fun t => σ.angleTwoAtTwo (circ σ.vertexTwo z t)) = fun t =>
      halfArg (σ.modTwo (circ σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) (3 / 2) (σ.modTwo (circ σ.vertexTwo z t))
          (σ.modOne (circ σ.vertexTwo z t)) (σ.wallSide 2 (circ σ.vertexTwo z t))
          (σ.cofBridgeTwo (circ σ.vertexTwo z t))).re - -(3 / 2))
        (twoCircle (-(3 / 2)) (3 / 2) (σ.modTwo (circ σ.vertexTwo z t))
          (σ.modOne (circ σ.vertexTwo z t)) (σ.wallSide 2 (circ σ.vertexTwo z t))
          (σ.cofBridgeTwo (circ σ.vertexTwo z t))).im := by
    funext t
    rw [angleTwoAtTwo, bridgeTwo, twoCircle_swap, sub_neg_eq_add]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < (σ.rotTwo z).re := re_pos_of_im_eq_zero hψ hw
    have := Real.sqrt_pos.2 hP0
    positivity
  · apply twoCircle_div_sqrt_pos (by norm_num) hB0 hP0
    have hn : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have : 0 < profileSlope * Real.sin σ.θ₃ / ‖z - σ.vertexOne‖ := by
      have := σ.sin_θ₃_pos
      unfold profileSlope
      positivity
    rw [show (3 / 2 - -(3 / 2) : ℝ) = 3 by norm_num]
    positivity

theorem exists_hasDerivAt_angleZeroAtTwo {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (fun t => σ.angleZeroAtTwo (circ σ.vertexTwo z t)) d 0 := by
  have h0 := σ.ne_zero_of_mem_domZero hz
  have hB0 := σ.modThree_pos hz.2.2
  have hA0 := σ.modTwo_pos z
  have hP0 := σ.cofBridgeZero_pos hz
  have hB := σ.hasDerivAt_modThree_circ σ.vertexTwo h0
  rw [σ.inner_circTwo_zero z] at hB
  have hB' : HasDerivAt (fun t => σ.modThree (circ σ.vertexTwo z t))
      (σ.wallSide 0 z * (profileSlope * Real.sin σ.θ₁ / ‖z‖)) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_zero_curve (hasDerivAt_circ σ.vertexTwo z)
  have h := hasDerivAt_negHalfArg_circ (a := -(3 / 2)) (b := 0) (by norm_num)
    (A := σ.modTwo) (B := σ.modThree) (W := σ.wallSide 0) (P := σ.cofBridgeZero) hA0
    (σ.modTwo_circ z) hB' hW (σ.contDiffAt_cofBridgeZero hz) σ.isOpen_domZero hz
    (fun u hu => σ.cofBridgeZero_pos hu)
    (fun u hu => by have := σ.heron_bridgeZero hu; linear_combination this)
    (by rw [← twoCircle_swap, sub_neg_eq_add]; exact hpos)
  have e : (fun t => σ.angleZeroAtTwo (circ σ.vertexTwo z t)) = fun t =>
      negHalfArg (σ.modTwo (circ σ.vertexTwo z t))
        ((twoCircle (-(3 / 2)) 0 (σ.modTwo (circ σ.vertexTwo z t))
          (σ.modThree (circ σ.vertexTwo z t)) (σ.wallSide 0 (circ σ.vertexTwo z t))
          (σ.cofBridgeZero (circ σ.vertexTwo z t))).re - -(3 / 2))
        (twoCircle (-(3 / 2)) 0 (σ.modTwo (circ σ.vertexTwo z t))
          (σ.modThree (circ σ.vertexTwo z t)) (σ.wallSide 0 (circ σ.vertexTwo z t))
          (σ.cofBridgeZero (circ σ.vertexTwo z t))).im := by
    funext t
    rw [angleZeroAtTwo, bridgeZero, twoCircle_swap, sub_neg_eq_add]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < (σ.vertexTwo - z).re := by
      apply re_pos_of_im_eq_zero
      · rw [← norm_neg, neg_sub, sub_re, σ.vertexTwo_re']
        exact hz.2.1
      · rw [sub_im, σ.vertexTwo_im', zero_sub, neg_eq_zero]
        exact hw
    have hv : ((σ.vertexTwo - z) * I).im = -((z - σ.vertexTwo) * I).im := by
      rw [← neg_sub, neg_mul, neg_im]
    have := Real.sqrt_pos.2 hP0
    have hr' : ((z - σ.vertexTwo) * I).im < 0 := by
      simp only [mul_im, I_re, I_im, mul_zero, mul_one, add_zero, sub_re] at hr ⊢
      linarith
    have e : -(((z - σ.vertexTwo) * I).im * Real.sqrt (σ.cofBridgeZero z) /
        (2 * |0 - -(3 / 2)| * σ.modTwo z)) = (-((z - σ.vertexTwo) * I).im) *
        Real.sqrt (σ.cofBridgeZero z) / (2 * |0 - -(3 / 2)| * σ.modTwo z) := by ring
    rw [e]
    have : 0 < -((z - σ.vertexTwo) * I).im := by linarith
    positivity
  · apply twoCircle_div_sqrt_pos (by norm_num) hB0 hP0
    have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
    have : 0 < profileSlope * Real.sin σ.θ₁ / ‖z‖ := by
      have := σ.sin_θ₁_pos
      unfold profileSlope
      positivity
    rw [show (0 - -(3 / 2) : ℝ) = 3 / 2 by norm_num]
    positivity

theorem exists_hasDerivAt_angleZeroAtThree {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modThree z - (σ.bridgeZero z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => σ.angleZeroAtThree (circ 0 z t)) d 0 := by
  have h0 := σ.ne_zero_of_mem_domZero hz
  have h2 := σ.ne_vertexTwo_of_mem_domZero hz
  have hB0 := σ.modTwo_pos z
  have hA0 := σ.modThree_pos hz.2.2
  have hP0 := σ.cofBridgeZero_pos hz
  have hB := σ.hasDerivAt_modTwo_circ 0 h2
  rw [sub_zero, σ.inner_circThree_two z] at hB
  have hB' : HasDerivAt (fun t => σ.modTwo (circ 0 z t))
      (σ.wallSide 0 z * (profileSlope * Real.sin σ.θ₁ / ‖z - σ.vertexTwo‖)) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_zero_curve (hasDerivAt_circ 0 z)
  rw [sub_zero] at hW
  have h := hasDerivAt_negHalfArg_circ (a := 0) (b := -(3 / 2)) (by norm_num)
    (A := σ.modThree) (B := σ.modTwo) (W := σ.wallSide 0) (P := σ.cofBridgeZero) hA0
    (σ.modThree_circ z) hB' hW (σ.contDiffAt_cofBridgeZero hz) σ.isOpen_domZero hz
    (fun u hu => σ.cofBridgeZero_pos hu) (fun u hu => σ.heron_bridgeZero hu)
    (by rw [sub_zero]; exact hpos)
  have e : (fun t => σ.angleZeroAtThree (circ 0 z t)) = fun t =>
      negHalfArg (σ.modThree (circ 0 z t))
        ((twoCircle 0 (-(3 / 2)) (σ.modThree (circ 0 z t)) (σ.modTwo (circ 0 z t))
          (σ.wallSide 0 (circ 0 z t)) (σ.cofBridgeZero (circ 0 z t))).re - 0)
        (twoCircle 0 (-(3 / 2)) (σ.modThree (circ 0 z t)) (σ.modTwo (circ 0 z t))
          (σ.wallSide 0 (circ 0 z t)) (σ.cofBridgeZero (circ 0 z t))).im := by
    funext t
    rw [angleZeroAtThree, bridgeZero, sub_zero]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < z.re := re_pos_of_im_eq_zero hz.1 hw
    have hr' : 0 < (z * I).im := by
      simp only [mul_im, I_re, I_im, mul_zero, mul_one, add_zero]
      exact hr
    have := Real.sqrt_pos.2 hP0
    have : 0 < (z * I).im * Real.sqrt (σ.cofBridgeZero z) /
        (2 * |-(3 / 2) - 0| * σ.modThree z) := by positivity
    linarith
  · apply twoCircle_div_sqrt_neg (by norm_num) hB0 hP0
    have hn : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    have : 0 < profileSlope * Real.sin σ.θ₁ / ‖z - σ.vertexTwo‖ := by
      have := σ.sin_θ₁_pos
      unfold profileSlope
      positivity
    rw [show (-(3 / 2) - 0 : ℝ) = -(3 / 2) by norm_num, div_neg]
    have := div_pos this (by norm_num : (0 : ℝ) < 3 / 2)
    linarith

theorem exists_hasDerivAt_angleOneAtThree {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modThree z + (σ.bridgeOne z).re) :
    ∃ d : ℝ, d < 0 ∧ HasDerivAt (fun t => σ.angleOneAtThree (circ 0 z t)) d 0 := by
  have h0 := σ.ne_zero_of_mem_domOne hz
  have h1 := σ.ne_vertexOne_of_mem_domOne hz
  have hB0 := σ.modOne_pos z
  have hA0 := σ.modThree_pos hz.2.2
  have hP0 := σ.cofBridgeOne_pos hz
  have hB := σ.hasDerivAt_modOne_circ 0 h1
  rw [sub_zero, σ.inner_circThree_one z] at hB
  have hB' : HasDerivAt (fun t => σ.modOne (circ 0 z t))
      (σ.wallSide 1 z * (-(profileSlope * Real.sin σ.θ₂ / ‖z - σ.vertexOne‖))) 0 := by
    refine hB.congr_deriv ?_
    ring
  have hW := σ.hasDerivAt_wallSide_one_curve (hasDerivAt_circ 0 z)
  rw [sub_zero, σ.wall_deriv_three_one z] at hW
  have h := hasDerivAt_halfArg_circ (a := 0) (b := 3 / 2) (by norm_num)
    (A := σ.modThree) (B := σ.modOne) (W := σ.wallSide 1) (P := σ.cofBridgeOne) hA0
    (σ.modThree_circ z) hB' hW (σ.contDiffAt_cofBridgeOne hz) σ.isOpen_domOne hz
    (fun u hu => σ.cofBridgeOne_pos hu) (fun u hu => σ.heron_bridgeOne hu)
    (by rw [sub_zero]; exact hpos)
  have e : (fun t => σ.angleOneAtThree (circ 0 z t)) = fun t =>
      halfArg (σ.modThree (circ 0 z t))
        ((twoCircle 0 (3 / 2) (σ.modThree (circ 0 z t)) (σ.modOne (circ 0 z t))
          (σ.wallSide 1 (circ 0 z t)) (σ.cofBridgeOne (circ 0 z t))).re - 0)
        (twoCircle 0 (3 / 2) (σ.modThree (circ 0 z t)) (σ.modOne (circ 0 z t))
          (σ.wallSide 1 (circ 0 z t)) (σ.cofBridgeOne (circ 0 z t))).im := by
    funext t
    rw [angleOneAtThree, bridgeOne, sub_zero]
  rw [e]
  refine ⟨_, ?_, h⟩
  split_ifs with hw
  · have hr : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
      apply re_pos_of_im_eq_zero
      · rw [norm_mul, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_mul_I, one_mul, ← show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by
            push_cast; ring]
        exact hz.1
      · have := σ.wallSide_one_eq_rotThree z
        rw [hw] at this
        linarith
    have := Real.sqrt_pos.2 hP0
    have : 0 < (exp (-((σ.θ₃ : ℂ) * I)) * z).re * Real.sqrt (σ.cofBridgeOne z) /
        (2 * |3 / 2 - 0| * σ.modThree z) := by positivity
    have e : -(exp (-((σ.θ₃ : ℂ) * I)) * z).re * Real.sqrt (σ.cofBridgeOne z) /
        (2 * |3 / 2 - 0| * σ.modThree z) = -((exp (-((σ.θ₃ : ℂ) * I)) * z).re *
        Real.sqrt (σ.cofBridgeOne z) / (2 * |3 / 2 - 0| * σ.modThree z)) := by ring
    rw [e]
    linarith
  · apply twoCircle_div_sqrt_neg (by norm_num) hB0 hP0
    have hn : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    have : 0 < profileSlope * Real.sin σ.θ₂ / ‖z - σ.vertexOne‖ := by
      have := σ.sin_θ₂_pos
      unfold profileSlope
      positivity
    rw [show (3 / 2 - 0 : ℝ) = 3 / 2 by norm_num, neg_div]
    have := div_pos this (by norm_num : (0 : ℝ) < 3 / 2)
    linarith


theorem contDiffAt_re_comp {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun u => (f u).re) z := reCLM.contDiff.contDiffAt.comp z hf

theorem contDiffAt_im_comp {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun u => (f u).im) z := imCLM.contDiff.contDiffAt.comp z hf

theorem contDiffAt_angleOneAtOne {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ σ.angleOneAtOne z :=
  ConeShape.contDiffAt_halfArg_comp (σ.contDiffAt_modOne (σ.ne_vertexOne_of_mem_domOne hz))
    ((contDiffAt_re_comp (σ.contDiffAt_bridgeOne hz)).sub contDiffAt_const)
    (contDiffAt_im_comp (σ.contDiffAt_bridgeOne hz)) hpos

theorem contDiffAt_angleTwoAtOne {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ σ.angleTwoAtOne z :=
  ConeShape.contDiffAt_negHalfArg_comp (σ.contDiffAt_modOne (σ.ne_vertexOne_of_mem_domTwo hz))
    ((contDiffAt_re_comp (σ.contDiffAt_bridgeTwo hz)).sub contDiffAt_const)
    (contDiffAt_im_comp (σ.contDiffAt_bridgeTwo hz)) hpos

theorem contDiffAt_angleTwoAtTwo {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ σ.angleTwoAtTwo z :=
  ConeShape.contDiffAt_halfArg_comp (σ.contDiffAt_modTwo (σ.ne_vertexTwo_of_mem_domTwo hz))
    ((contDiffAt_re_comp (σ.contDiffAt_bridgeTwo hz)).add contDiffAt_const)
    (contDiffAt_im_comp (σ.contDiffAt_bridgeTwo hz)) hpos

theorem contDiffAt_angleZeroAtTwo {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ σ.angleZeroAtTwo z :=
  ConeShape.contDiffAt_negHalfArg_comp (σ.contDiffAt_modTwo (σ.ne_vertexTwo_of_mem_domZero hz))
    ((contDiffAt_re_comp (σ.contDiffAt_bridgeZero hz)).add contDiffAt_const)
    (contDiffAt_im_comp (σ.contDiffAt_bridgeZero hz)) hpos

theorem contDiffAt_angleOneAtThree {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modThree z + (σ.bridgeOne z).re) :
    ContDiffAt ℝ ∞ σ.angleOneAtThree z :=
  ConeShape.contDiffAt_halfArg_comp (σ.contDiffAt_modThree (σ.ne_zero_of_mem_domOne hz))
    (contDiffAt_re_comp (σ.contDiffAt_bridgeOne hz))
    (contDiffAt_im_comp (σ.contDiffAt_bridgeOne hz)) hpos

theorem contDiffAt_angleZeroAtThree {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modThree z - (σ.bridgeZero z).re) :
    ContDiffAt ℝ ∞ σ.angleZeroAtThree z :=
  ConeShape.contDiffAt_negHalfArg_comp (σ.contDiffAt_modThree (σ.ne_zero_of_mem_domZero hz))
    (contDiffAt_re_comp (σ.contDiffAt_bridgeZero hz))
    (contDiffAt_im_comp (σ.contDiffAt_bridgeZero hz)) hpos

theorem polar_of_norm_sub (u c : ℂ) {S : ℝ} (hc : c.im = 0) (h : ‖u - c‖ = S) :
    (u.re - c.re) ^ 2 + u.im ^ 2 = S ^ 2 := by
  have := ConeShape.sq_add_sq_eq_of_norm h
  simpa [hc] using this

theorem eq_of_polar {u : ℂ} {c S θ : ℝ}
    (h : (⟨u.re - c, u.im⟩ : ℂ) = (S : ℂ) * exp ((θ : ℂ) * I)) :
    u = c + (S : ℂ) * exp ((θ : ℂ) * I) := by
  rw [← h]
  apply Complex.ext <;> simp

theorem eq_of_polar_add {u : ℂ} {c S θ : ℝ}
    (h : (⟨u.re + c, u.im⟩ : ℂ) = (S : ℂ) * exp ((θ : ℂ) * I)) :
    u = ((-c : ℝ) : ℂ) + (S : ℂ) * exp ((θ : ℂ) * I) := by
  rw [← h]
  apply Complex.ext <;> simp

theorem eq_of_polar_zero {u : ℂ} {S θ : ℝ}
    (h : (⟨u.re, u.im⟩ : ℂ) = (S : ℂ) * exp ((θ : ℂ) * I)) :
    u = ((0 : ℝ) : ℂ) + (S : ℂ) * exp ((θ : ℂ) * I) := by
  rw [← h]
  apply Complex.ext <;> simp

theorem bridgeOne_eq_polar_one {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2)) :
    σ.bridgeOne z = ((3 / 2 : ℝ) : ℂ) + (σ.modOne z : ℂ) * exp ((σ.angleOneAtOne z : ℂ) * I) := by
  have hn : ‖σ.bridgeOne z - ((3 / 2 : ℝ) : ℂ)‖ = σ.modOne z := by
    push_cast
    exact (σ.norm_bridgeOne hz).2
  have hsq := polar_of_norm_sub (σ.bridgeOne z) ((3 / 2 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re] at hsq
  exact eq_of_polar (halfArg_polar (σ.modOne_pos z) hpos hsq)

theorem bridgeTwo_eq_polar_one {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    σ.bridgeTwo z = ((3 / 2 : ℝ) : ℂ) + (σ.modOne z : ℂ) * exp ((σ.angleTwoAtOne z : ℂ) * I) := by
  have hn : ‖σ.bridgeTwo z - ((3 / 2 : ℝ) : ℂ)‖ = σ.modOne z := by
    push_cast
    exact (σ.norm_bridgeTwo hz).1
  have hsq := polar_of_norm_sub (σ.bridgeTwo z) ((3 / 2 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re] at hsq
  exact eq_of_polar (negHalfArg_polar (σ.modOne_pos z) hpos hsq)

theorem bridgeTwo_eq_polar_two {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2)) :
    σ.bridgeTwo z = ((-(3 / 2) : ℝ) : ℂ) + (σ.modTwo z : ℂ) *
      exp ((σ.angleTwoAtTwo z : ℂ) * I) := by
  have hn : ‖σ.bridgeTwo z - ((-(3 / 2) : ℝ) : ℂ)‖ = σ.modTwo z := by
    push_cast
    rw [sub_neg_eq_add]
    exact (σ.norm_bridgeTwo hz).2
  have hsq := polar_of_norm_sub (σ.bridgeTwo z) ((-(3 / 2) : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_neg_eq_add] at hsq
  exact eq_of_polar_add (halfArg_polar (σ.modTwo_pos z) hpos hsq)

theorem bridgeZero_eq_polar_two {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    σ.bridgeZero z = ((-(3 / 2) : ℝ) : ℂ) + (σ.modTwo z : ℂ) *
      exp ((σ.angleZeroAtTwo z : ℂ) * I) := by
  have hn : ‖σ.bridgeZero z - ((-(3 / 2) : ℝ) : ℂ)‖ = σ.modTwo z := by
    push_cast
    rw [sub_neg_eq_add]
    exact (σ.norm_bridgeZero hz).2
  have hsq := polar_of_norm_sub (σ.bridgeZero z) ((-(3 / 2) : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_neg_eq_add] at hsq
  exact eq_of_polar_add (negHalfArg_polar (σ.modTwo_pos z) hpos hsq)

theorem bridgeOne_eq_polar_three {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modThree z + (σ.bridgeOne z).re) :
    σ.bridgeOne z = ((0 : ℝ) : ℂ) + (σ.modThree z : ℂ) * exp ((σ.angleOneAtThree z : ℂ) * I) := by
  have hn : ‖σ.bridgeOne z - ((0 : ℝ) : ℂ)‖ = σ.modThree z := by
    push_cast
    rw [sub_zero]
    exact (σ.norm_bridgeOne hz).1
  have hsq := polar_of_norm_sub (σ.bridgeOne z) ((0 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_zero] at hsq
  exact eq_of_polar_zero (halfArg_polar (σ.modThree_pos hz.2.2) hpos hsq)

theorem bridgeZero_eq_polar_three {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modThree z - (σ.bridgeZero z).re) :
    σ.bridgeZero z = ((0 : ℝ) : ℂ) + (σ.modThree z : ℂ) *
      exp ((σ.angleZeroAtThree z : ℂ) * I) := by
  have hn : ‖σ.bridgeZero z - ((0 : ℝ) : ℂ)‖ = σ.modThree z := by
    push_cast
    rw [sub_zero]
    exact (σ.norm_bridgeZero hz).1
  have hsq := polar_of_norm_sub (σ.bridgeZero z) ((0 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_zero] at hsq
  exact eq_of_polar_zero (negHalfArg_polar (σ.modThree_pos hz.2.2) hpos hsq)


theorem halfArg_mem_Ico {S R J : ℝ} (hSR : 0 < S + R) (hJ : 0 ≤ J) :
    0 ≤ halfArg S R J ∧ halfArg S R J < Real.pi := by
  unfold halfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S + R))
  have h2 : 0 ≤ Real.arctan (J / (S + R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR.le)
  constructor <;> linarith

theorem negHalfArg_mem_Ioc {S R J : ℝ} (hSR : 0 < S - R) (hJ : 0 ≤ J) :
    0 < negHalfArg S R J ∧ negHalfArg S R J ≤ Real.pi := by
  unfold negHalfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S - R))
  have h2 : 0 ≤ Real.arctan (J / (S - R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR.le)
  constructor <;> linarith

theorem halfArg_le_negHalfArg {S R J R' J' : ℝ} (hS : 0 < S) (hSR : 0 < S + R)
    (hSR' : 0 < S - R') (h : R ^ 2 + J ^ 2 = S ^ 2) (h' : R' ^ 2 + J' ^ 2 = S ^ 2)
    (hJ : 0 ≤ J) (hJ' : 0 ≤ J') (hRR : R' ≤ R) : halfArg S R J ≤ negHalfArg S R' J' := by
  obtain ⟨a0, a1⟩ := halfArg_mem_Ico hSR hJ
  obtain ⟨b0, b1⟩ := negHalfArg_mem_Ioc hSR' hJ'
  by_contra hc
  have hlt : negHalfArg S R' J' < halfArg S R J := not_le.1 hc
  have := Real.cos_lt_cos_of_nonneg_of_le_pi b0.le a1.le hlt
  rw [halfArg_cos hS hSR h, negHalfArg_cos hS hSR' h'] at this
  rw [div_lt_div_iff_of_pos_right hS] at this
  linarith

theorem im_nonneg_of_bridge {u : ℂ} {w P : ℝ} (hw : 0 ≤ w) (hu : u.im = w * Real.sqrt P / 3) :
    0 ≤ u.im := by
  rw [hu]
  have := Real.sqrt_nonneg P
  positivity

theorem angleOneAtOne_le_angleTwoAtOne {z : ℂ} (hz1 : z ∈ σ.domOne) (hz2 : z ∈ σ.domTwo)
    (hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2))
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw2 : 0 ≤ σ.wallSide 2 z)
    (hre : (σ.bridgeTwo z).re ≤ (σ.bridgeOne z).re) :
    σ.angleOneAtOne z ≤ σ.angleTwoAtOne z := by
  have hn1 := polar_of_norm_sub (σ.bridgeOne z) (3 / 2) (by simp) (σ.norm_bridgeOne hz1).2
  have hn2 := polar_of_norm_sub (σ.bridgeTwo z) (3 / 2) (by simp) (σ.norm_bridgeTwo hz2).1
  simp only [div_ofNat_re, Complex.re_ofNat] at hn1 hn2
  have hI1 : 0 ≤ (σ.bridgeOne z).im := by
    rw [bridgeOne, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeOne z)
    positivity
  have hI2 : 0 ≤ (σ.bridgeTwo z).im := by
    rw [bridgeTwo, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeTwo z)
    positivity
  exact halfArg_le_negHalfArg (σ.modOne_pos z) hpos1 hpos2 hn1 hn2 hI1 hI2 (by linarith)

theorem angleTwoAtTwo_le_angleZeroAtTwo {z : ℂ} (hz2 : z ∈ σ.domTwo) (hz0 : z ∈ σ.domZero)
    (hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2))
    (hw2 : 0 ≤ σ.wallSide 2 z) (hw0 : 0 ≤ σ.wallSide 0 z)
    (hre : (σ.bridgeZero z).re ≤ (σ.bridgeTwo z).re) :
    σ.angleTwoAtTwo z ≤ σ.angleZeroAtTwo z := by
  have e2 : ‖σ.bridgeTwo z - -(3 / 2)‖ = σ.modTwo z := by
    rw [sub_neg_eq_add]; exact (σ.norm_bridgeTwo hz2).2
  have e0 : ‖σ.bridgeZero z - -(3 / 2)‖ = σ.modTwo z := by
    rw [sub_neg_eq_add]; exact (σ.norm_bridgeZero hz0).2
  have hn2 := polar_of_norm_sub (σ.bridgeTwo z) (-(3 / 2)) (by simp) e2
  have hn0 := polar_of_norm_sub (σ.bridgeZero z) (-(3 / 2)) (by simp) e0
  simp only [neg_re, div_ofNat_re, Complex.re_ofNat, sub_neg_eq_add] at hn2 hn0
  have hI2 : 0 ≤ (σ.bridgeTwo z).im := by
    rw [bridgeTwo, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeTwo z)
    positivity
  have hI0 : 0 ≤ (σ.bridgeZero z).im := by
    rw [bridgeZero, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeZero z)
    positivity
  exact halfArg_le_negHalfArg (σ.modTwo_pos z) hpos2 hpos0 hn2 hn0 hI2 hI0 (by linarith)

theorem angleOneAtThree_le_angleZeroAtThree {z : ℂ} (hz1 : z ∈ σ.domOne) (hz0 : z ∈ σ.domZero)
    (hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re)
    (hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re)
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw0 : 0 ≤ σ.wallSide 0 z)
    (hre : (σ.bridgeZero z).re ≤ (σ.bridgeOne z).re) :
    σ.angleOneAtThree z ≤ σ.angleZeroAtThree z := by
  have e1 : ‖σ.bridgeOne z - 0‖ = σ.modThree z := by
    rw [sub_zero]; exact (σ.norm_bridgeOne hz1).1
  have e0 : ‖σ.bridgeZero z - 0‖ = σ.modThree z := by
    rw [sub_zero]; exact (σ.norm_bridgeZero hz0).1
  have hn1 := polar_of_norm_sub (σ.bridgeOne z) 0 (by simp) e1
  have hn0 := polar_of_norm_sub (σ.bridgeZero z) 0 (by simp) e0
  simp only [zero_re, sub_zero] at hn1 hn0
  have hI1 : 0 ≤ (σ.bridgeOne z).im := by
    rw [bridgeOne, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeOne z)
    positivity
  have hI0 : 0 ≤ (σ.bridgeZero z).im := by
    rw [bridgeZero, twoCircle_im]
    have := Real.sqrt_nonneg (σ.cofBridgeZero z)
    positivity
  exact halfArg_le_negHalfArg (σ.modThree_pos hz1.2.2) hpos1 hpos0 hn1 hn0 hI1 hI0 hre


def psiOne (z : ℂ) : ℝ := discAngle (σ.rotOne z)

def psiTwo (z : ℂ) : ℝ := discAngle (σ.rotTwo z)


theorem ne_zero_of_norm_add_re_pos {w : ℂ} (h : 0 < ‖w‖ + w.re) : w ≠ 0 := by
  rintro rfl
  simp at h

theorem contDiffAt_discAngle_comp {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z)
    (h : 0 < ‖f z‖ + (f z).re) : ContDiffAt ℝ ∞ (fun u => discAngle (f u)) z :=
  ConeShape.contDiffAt_halfArg_comp (hf.norm ℝ (ne_zero_of_norm_add_re_pos h))
    (contDiffAt_re_comp hf) (contDiffAt_im_comp hf) h

theorem contDiff_rotOne : ContDiff ℝ ∞ σ.rotOne := by
  have h : σ.rotOne = fun z => -(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne)) := rfl
  rw [h]
  exact ((contDiff_mul_aux _).comp (contDiff_id.sub contDiff_const)).neg

theorem contDiffAt_psiOne {z : ℂ} (h : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    ContDiffAt ℝ ∞ σ.psiOne z :=
  contDiffAt_discAngle_comp σ.contDiff_rotOne.contDiffAt h

theorem contDiffAt_psiTwo {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    ContDiffAt ℝ ∞ σ.psiTwo z :=
  contDiffAt_discAngle_comp σ.contDiff_rotTwo.contDiffAt h

theorem contDiffAt_psiThree {z : ℂ} (h : 0 < ‖z‖ + z.re) :
    ContDiffAt ℝ ∞ (fun u : ℂ => discAngle u) z :=
  contDiffAt_discAngle_comp contDiffAt_id h

theorem hasDerivAt_discAngle_mul_exp {w : ℂ} (h : 0 < ‖w‖ + w.re) :
    HasDerivAt (fun t : ℝ => discAngle (w * exp ((t : ℂ) * I))) 1 0 := by
  have hm : discAngle w ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hc : ContinuousAt (fun t : ℝ => discAngle w + t) 0 :=
    (continuous_const.add continuous_id).continuousAt
  have h1 : ∀ᶠ t : ℝ in 𝓝 0, -Real.pi < discAngle w + t :=
    hc.eventually (lt_mem_nhds (by simpa using hm.1))
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, discAngle w + t < Real.pi :=
    hc.eventually (gt_mem_nhds (by simpa using hm.2))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, discAngle w + t = discAngle (w * exp ((t : ℂ) * I)) := by
    filter_upwards [h1, h2] with t ht1 ht2
    exact (discAngle_mul_exp (ne_zero_of_norm_add_re_pos h) h ht1 ht2).symm
  have hlin : HasDerivAt (fun t : ℝ => discAngle w + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℝ)).const_add (discAngle w)
  exact hlin.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)

theorem rotOne_circ (z : ℂ) (t : ℝ) :
    σ.rotOne (circ σ.vertexOne z t) = σ.rotOne z * exp ((t : ℂ) * I) := by
  simp only [rotOne, circ, add_sub_cancel_left]
  ring

theorem rotTwo_circ (z : ℂ) (t : ℝ) :
    σ.rotTwo (circ σ.vertexTwo z t) = σ.rotTwo z * exp ((t : ℂ) * I) := by
  simp only [rotTwo, circ, add_sub_cancel_left]
  ring

theorem circ_zero_eq (z : ℂ) (t : ℝ) : circ 0 z t = z * exp ((t : ℂ) * I) := by
  simp [circ]

theorem hasDerivAt_psiOne_circ {z : ℂ} (h : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    HasDerivAt (fun t => σ.psiOne (circ σ.vertexOne z t)) 1 0 := by
  have e : (fun t => σ.psiOne (circ σ.vertexOne z t)) =
      fun t : ℝ => discAngle (σ.rotOne z * exp ((t : ℂ) * I)) := by
    funext t
    rw [psiOne, rotOne_circ]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp h

theorem hasDerivAt_psiTwo_circ {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    HasDerivAt (fun t => σ.psiTwo (circ σ.vertexTwo z t)) 1 0 := by
  have e : (fun t => σ.psiTwo (circ σ.vertexTwo z t)) =
      fun t : ℝ => discAngle (σ.rotTwo z * exp ((t : ℂ) * I)) := by
    funext t
    rw [psiTwo, rotTwo_circ]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp h

theorem hasDerivAt_psiThree_circ {z : ℂ} (h : 0 < ‖z‖ + z.re) :
    HasDerivAt (fun t => discAngle (circ 0 z t)) 1 0 := by
  have e : (fun t => discAngle (circ 0 z t)) =
      fun t : ℝ => discAngle (z * exp ((t : ℂ) * I)) := by
    funext t
    rw [circ_zero_eq]
  rw [e]
  exact hasDerivAt_discAngle_mul_exp h

theorem discAngle_conj (w : ℂ) : discAngle (conj w) = -discAngle w := by
  simp only [discAngle, Complex.norm_conj, conj_re, conj_im, halfArg_neg]

theorem discAngle_exp_mul_conj {w : ℂ} (h : 0 < ‖w‖ + w.re) {θ : ℝ}
    (h1 : -Real.pi < θ - discAngle w) (h2 : θ - discAngle w < Real.pi) :
    discAngle (exp ((θ : ℂ) * I) * conj w) = θ - discAngle w := by
  have hc : 0 < ‖conj w‖ + (conj w).re := by rwa [Complex.norm_conj, conj_re]
  rw [mul_comm, discAngle_mul_exp (ne_zero_of_norm_add_re_pos hc) hc
    (by rw [discAngle_conj]; linarith) (by rw [discAngle_conj]; linarith), discAngle_conj]
  ring

theorem two_mul_ofReal_mul_I (θ : ℝ) : 2 * (θ : ℂ) * I = ((2 * θ : ℝ) : ℂ) * I := by
  push_cast
  ring

theorem psiOne_refl_one (z : ℂ) : σ.psiOne (σ.refl 1 z) = -σ.psiOne z := by
  rw [psiOne, rotOne_refl_one, discAngle_conj, psiOne]

theorem psiOne_refl_two {z : ℂ} (h : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re)
    (h1 : -Real.pi < 2 * σ.θ₁ - σ.psiOne z) (h2 : 2 * σ.θ₁ - σ.psiOne z < Real.pi) :
    σ.psiOne (σ.refl 2 z) = 2 * σ.θ₁ - σ.psiOne z := by
  rw [psiOne, rotOne_refl_two, two_mul_ofReal_mul_I]
  exact discAngle_exp_mul_conj h h1 h2

theorem psiTwo_refl_two (z : ℂ) : σ.psiTwo (σ.refl 2 z) = -σ.psiTwo z := by
  rw [psiTwo, rotTwo_refl_two, discAngle_conj, psiTwo]

theorem psiTwo_refl_zero {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - σ.psiTwo z) (h2 : 2 * σ.θ₂ - σ.psiTwo z < Real.pi) :
    σ.psiTwo (σ.refl 0 z) = 2 * σ.θ₂ - σ.psiTwo z := by
  rw [psiTwo, rotTwo_refl_zero, two_mul_ofReal_mul_I]
  exact discAngle_exp_mul_conj h h1 h2

theorem psiThree_refl_zero (z : ℂ) : discAngle (σ.refl 0 z) = -discAngle z :=
  discAngle_conj z

theorem psiThree_refl_one {z : ℂ} (h : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi) :
    discAngle (σ.refl 1 z) = 2 * σ.θ₃ - discAngle z := by
  change discAngle (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  rw [two_mul_ofReal_mul_I]
  exact discAngle_exp_mul_conj h h1 h2

theorem angleOneAtOne_refl_one (z : ℂ) :
    σ.angleOneAtOne (σ.refl 1 z) = -σ.angleOneAtOne z := by
  have hm : σ.modOne (σ.refl 1 z) = σ.modOne z := by
    rw [modOne, modOne, σ.canon_zero_refl 1 z σ.wallSide_one_vertexOne]
  rw [angleOneAtOne, angleOneAtOne, hm, bridgeOne_refl_one, conj_re, conj_im, halfArg_neg]

theorem angleOneAtThree_refl_one (z : ℂ) :
    σ.angleOneAtThree (σ.refl 1 z) = -σ.angleOneAtThree z := by
  have hm : σ.modThree (σ.refl 1 z) = σ.modThree z := by
    rw [modThree, modThree, σ.canon_two_refl 1 z σ.wallSide_one_zero]
  rw [angleOneAtThree, angleOneAtThree, hm, bridgeOne_refl_one, conj_re, conj_im, halfArg_neg]

theorem angleTwoAtOne_refl_two (z : ℂ) :
    σ.angleTwoAtOne (σ.refl 2 z) = 2 * Real.pi - σ.angleTwoAtOne z := by
  have hm : σ.modOne (σ.refl 2 z) = σ.modOne z := by
    rw [modOne, modOne, σ.canon_zero_refl 2 z σ.wallSide_two_vertexOne]
  rw [angleTwoAtOne, angleTwoAtOne, hm, bridgeTwo_refl_two, conj_re, conj_im, negHalfArg_neg]

theorem angleTwoAtTwo_refl_two (z : ℂ) :
    σ.angleTwoAtTwo (σ.refl 2 z) = -σ.angleTwoAtTwo z := by
  have hm : σ.modTwo (σ.refl 2 z) = σ.modTwo z := by
    rw [modTwo, modTwo, σ.canon_one_refl 2 z σ.wallSide_two_vertexTwo]
  rw [angleTwoAtTwo, angleTwoAtTwo, hm, bridgeTwo_refl_two, conj_re, conj_im, halfArg_neg]

theorem angleZeroAtTwo_refl_zero (z : ℂ) :
    σ.angleZeroAtTwo (σ.refl 0 z) = 2 * Real.pi - σ.angleZeroAtTwo z := by
  have hm : σ.modTwo (σ.refl 0 z) = σ.modTwo z := by
    rw [modTwo, modTwo, σ.canon_one_refl 0 z σ.wallSide_zero_vertexTwo]
  rw [angleZeroAtTwo, angleZeroAtTwo, hm, bridgeZero_refl_zero, conj_re, conj_im,
    negHalfArg_neg]

theorem angleZeroAtThree_refl_zero (z : ℂ) :
    σ.angleZeroAtThree (σ.refl 0 z) = 2 * Real.pi - σ.angleZeroAtThree z := by
  have hm : σ.modThree (σ.refl 0 z) = σ.modThree z := by
    rw [modThree, modThree, σ.canon_two_refl 0 z σ.wallSide_zero_zero]
  rw [angleZeroAtThree, angleZeroAtThree, hm, bridgeZero_refl_zero, conj_re, conj_im,
    negHalfArg_neg]

end EuclidShape

end GC.Seifert
