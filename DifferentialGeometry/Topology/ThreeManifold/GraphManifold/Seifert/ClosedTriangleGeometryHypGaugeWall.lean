import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypGaugeArg
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypTriangle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldGenericShape

/-!
# The wall identities of the `SL₂~` gauge on a hyperbolic triangle

Lane B3b (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §4, with
review 33 §5.2–§5.3). For CF's hyperbolic triangle `σ` (`v₃ = 0`, `v₂ = ξ` real, `v₁ = η`) the
gauges `Gⱼ = hypGauge vⱼ` satisfy, exactly on the unit disc:
* wall 0 and wall 1: `G₂ (conj w) = -G₂ w`, `G₁ (refl 1 w) = -G₁ w`
  (`hypGauge_vertexTwo_conj`, `hypGauge_vertexOne_refl_one`);
* wall 2: `(G₁ - G₂) w + (G₁ - G₂) (refl 2 w) = hypArea σ = 2 (π - θ₁ - θ₂ - θ₃) > 0`
  (`hypGauge_wallTwo`, `hypArea_pos`), a strict real identity.
The proof of the last one: with `a = 1 - η̄ ξ`, `b = η̄ - ξ`, `Q(z) = (1 - η̄ z)(1 - ξ²) =
(1 - ξ z)(a - b · mob ξ z)` (`one_sub_mul_eq_mob`), the reflection `refl 2` acts on `mob ξ` by
`w ↦ e^{-2iθ₂} w̄` and fixes `η`, which gives the product identity
`(1 - η̄ R z) conj (1 - ξ z) ā = a conj (1 - η̄ z) (1 - ξ R z)` (`wallTwo_product`); hence the
sum `wallSum` of the four principal arguments is `2 Arg a` modulo `2π` (`wallTwo_angle`), it is
continuous on the connected disc and takes the value `2 Arg a` at `z = ξ`, so it equals `2 Arg a`
(`wallSum_const`, via `const_of_angle`). Finally
`1 - ξ η = -e^{iS} a` (CF's `one_sub_mul_vertex_eq`, `S = θ₁ + θ₂ + θ₃`) gives
`2 Arg a = π - S` exactly (`two_arg_vertex`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

def hypArea (σ : CompactShape) : ℝ := 2 * (Real.pi - σ.θ₁ - σ.θ₂ - σ.θ₃)

theorem const_of_angle {S : Set ℂ} (hS : IsPreconnected S) {T : ℂ → ℝ} (hT : ContinuousOn T S)
    {θ : ℝ} (h : ∀ z ∈ S, (T z : Real.Angle) = θ) {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz : z ∈ S) :
    T z = T z₀ := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  set f : ℂ → ℝ := fun w => (T w - θ) / (2 * Real.pi) with hf
  have hmaps : MapsTo f S (range ((↑) : ℤ → ℝ)) := by
    intro w hw
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (h w hw)
    exact ⟨k, by rw [hf]; simp only; rw [hk]; field_simp⟩
  have hc : ContinuousOn f S := (hT.sub continuousOn_const).div_const _
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have := hS.constant_of_mapsTo hdisc hc hmaps hz hz₀
  simp only [hf] at this
  field_simp at this
  linarith

section Shape

variable {σ : CompactShape} (h : σ.curv = .hyperbolic)
include h

theorem hypArea_pos : 0 < hypArea σ := by
  have := CompactShape.θ_sum_of_hyp σ h
  unfold hypArea
  linarith

theorem re_vertexTwo_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - conj σ.vertexTwo * w).re :=
  re_one_sub_conj_mul_pos (HypFold.norm_vertexTwo_lt_one h) hw

theorem re_vertexOne_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - conj σ.vertexOne * w).re :=
  re_one_sub_conj_mul_pos (HypFold.norm_vertexOne_lt_one h) hw

theorem hypGauge_vertexTwo_conj {w : ℂ} (hw : ‖w‖ < 1) :
    hypGauge σ.vertexTwo (conj w) = -hypGauge σ.vertexTwo w := by
  refine hypGauge_odd (re_vertexTwo_pos h hw) ?_
  rw [map_mul, Complex.conj_conj, HypFold.conj_vertexTwo]

omit h in
theorem conj_vertexOne_mul_exp :
    conj σ.vertexOne * exp (2 * (σ.θ₃ : ℂ) * I) = σ.vertexOne := by
  rw [HypFold.vertexOne_eq, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, mul_assoc,
    ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, conj_I]
  ring

theorem hypGauge_vertexOne_refl_one {w : ℂ} (hw : ‖w‖ < 1) :
    hypGauge σ.vertexOne (σ.refl 1 w) = -hypGauge σ.vertexOne w := by
  refine hypGauge_odd (re_vertexOne_pos h hw) ?_
  change conj σ.vertexOne * (exp (2 * (σ.θ₃ : ℂ) * I) * conj w) = _
  rw [← mul_assoc, conj_vertexOne_mul_exp (σ := σ), map_mul, Complex.conj_conj]

omit h in
theorem vertexTwo_real : ((σ.vertexTwo.re : ℝ) : ℂ) = σ.vertexTwo := by
  rw [HypFold.vertexTwo_eq, ofReal_re]

theorem one_sub_mul_eq_mob {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - conj σ.vertexOne * z) * (1 - σ.vertexTwo ^ 2) =
      (1 - σ.vertexTwo * z) * ((1 - conj σ.vertexOne * σ.vertexTwo) -
        (conj σ.vertexOne - σ.vertexTwo) * HypFold.mob σ.vertexTwo z) := by
  have hY := HypFold.one_sub_vertexTwo_mul_ne_zero h hz
  rw [HypFold.mob, HypFold.conj_vertexTwo]
  have e : (1 - σ.vertexTwo * z) * ((z - σ.vertexTwo) / (1 - σ.vertexTwo * z)) =
      z - σ.vertexTwo := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hY]
  linear_combination (conj σ.vertexOne - σ.vertexTwo) * e

theorem fixed_vertexOne :
    exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo σ.vertexOne) =
      HypFold.mob σ.vertexTwo σ.vertexOne := by
  have hd := HypFold.disc_vertexTwo_vertexOne h
  rw [CompactShape.disc_eq_mob h] at hd
  rw [hd, map_neg, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have e : exp (-(2 * (σ.θ₂ : ℂ) * I)) * exp (conj (-((σ.θ₂ : ℂ) * I))) =
      exp (-((σ.θ₂ : ℂ) * I)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, conj_I]
    ring
  linear_combination (-(HypFold.sideOneTwo σ : ℂ)) * e

theorem wallTwo_K (w : ℂ) :
    conj (1 - conj σ.vertexOne * σ.vertexTwo) *
        ((1 - conj σ.vertexOne * σ.vertexTwo) - (conj σ.vertexOne - σ.vertexTwo) *
          (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj w)) =
      (1 - conj σ.vertexOne * σ.vertexTwo) *
        conj ((1 - conj σ.vertexOne * σ.vertexTwo) - (conj σ.vertexOne - σ.vertexTwo) * w) := by
  set m := HypFold.mob σ.vertexTwo σ.vertexOne with hm
  set E := exp (-(2 * (σ.θ₂ : ℂ) * I)) with hE
  have hfix : E * conj m = m := fixed_vertexOne h
  have hne := HypFold.one_sub_vertexTwo_mul_ne_zero h (HypFold.norm_vertexOne_lt_one h)
  have hmdef : m * (1 - σ.vertexTwo * σ.vertexOne) = σ.vertexOne - σ.vertexTwo := by
    rw [hm, HypFold.mob, HypFold.conj_vertexTwo, div_mul_cancel₀ _ hne]
  have hmc : conj m * (1 - σ.vertexTwo * conj σ.vertexOne) = conj σ.vertexOne - σ.vertexTwo := by
    have := congrArg conj hmdef
    simpa [map_mul, map_sub, HypFold.conj_vertexTwo] using this
  have hc2 := HypFold.conj_vertexTwo (σ := σ)
  simp only [map_sub, map_one, map_mul, Complex.conj_conj, hc2]
  linear_combination (conj w * (1 - σ.vertexTwo * σ.vertexOne) * E) * hmc -
    (conj w * (1 - σ.vertexTwo * conj σ.vertexOne) * (1 - σ.vertexTwo * σ.vertexOne)) * hfix -
    (conj w * (1 - σ.vertexTwo * conj σ.vertexOne)) * hmdef

theorem one_sub_sq_vertexTwo_ne_zero : (1 : ℂ) - σ.vertexTwo ^ 2 ≠ 0 := by
  intro h0
  have hn := HypFold.norm_vertexTwo_lt_one h
  have h1 : σ.vertexTwo ^ 2 = 1 := (sub_eq_zero.mp h0).symm
  have : ‖σ.vertexTwo‖ ^ 2 = 1 := by rw [← norm_pow, h1, norm_one]
  nlinarith [norm_nonneg σ.vertexTwo]

theorem wallTwo_product {z : ℂ} (hz : ‖z‖ < 1) :
    (1 - conj σ.vertexOne * σ.refl 2 z) * conj (1 - σ.vertexTwo * z) *
        conj (1 - conj σ.vertexOne * σ.vertexTwo) =
      (1 - conj σ.vertexOne * σ.vertexTwo) * conj (1 - conj σ.vertexOne * z) *
        (1 - σ.vertexTwo * σ.refl 2 z) := by
  have hR := HypFold.norm_refl_lt_one h 2 hz
  have QWz := one_sub_mul_eq_mob h hz
  have QWR := one_sub_mul_eq_mob h hR
  rw [HypFold.mob_vertexTwo_refl_two h hz] at QWR
  have K := wallTwo_K h (HypFold.mob σ.vertexTwo z)
  have hc2 := HypFold.conj_vertexTwo (σ := σ)
  have cQW : conj (1 - conj σ.vertexOne * z) * (1 - σ.vertexTwo ^ 2) =
      conj (1 - σ.vertexTwo * z) * conj ((1 - conj σ.vertexOne * σ.vertexTwo) -
        (conj σ.vertexOne - σ.vertexTwo) * HypFold.mob σ.vertexTwo z) := by
    have := congrArg conj QWz
    rw [map_mul, map_mul, map_sub (starRingEnd ℂ) 1 (σ.vertexTwo ^ 2), map_pow, hc2,
      map_one] at this
    exact this
  have key : ((1 - conj σ.vertexOne * σ.refl 2 z) * conj (1 - σ.vertexTwo * z) *
      conj (1 - conj σ.vertexOne * σ.vertexTwo) -
      (1 - conj σ.vertexOne * σ.vertexTwo) * conj (1 - conj σ.vertexOne * z) *
        (1 - σ.vertexTwo * σ.refl 2 z)) * (1 - σ.vertexTwo ^ 2) = 0 := by
    linear_combination (conj (1 - σ.vertexTwo * z) * conj (1 - conj σ.vertexOne * σ.vertexTwo)) *
      QWR - ((1 - conj σ.vertexOne * σ.vertexTwo) * (1 - σ.vertexTwo * σ.refl 2 z)) * cQW +
      ((1 - σ.vertexTwo * σ.refl 2 z) * conj (1 - σ.vertexTwo * z)) * K
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (one_sub_sq_vertexTwo_ne_zero h))

theorem re_vertexTwo_pos' {w : ℂ} (hw : ‖w‖ < 1) : 0 < (1 - σ.vertexTwo * w).re := by
  have := re_vertexTwo_pos h hw
  rwa [HypFold.conj_vertexTwo] at this

theorem re_a_pos : 0 < (1 - conj σ.vertexOne * σ.vertexTwo).re :=
  re_vertexOne_pos h (HypFold.norm_vertexTwo_lt_one h)

theorem wallTwo_angle {z : ℂ} (hz : ‖z‖ < 1) :
    ((arg (1 - conj σ.vertexOne * z) - arg (1 - σ.vertexTwo * z) +
      arg (1 - conj σ.vertexOne * σ.refl 2 z) - arg (1 - σ.vertexTwo * σ.refl 2 z) : ℝ) :
        Real.Angle) = ((2 * arg (1 - conj σ.vertexOne * σ.vertexTwo) : ℝ) : Real.Angle) := by
  have hR := HypFold.norm_refl_lt_one h 2 hz
  have hX := ne_zero_of_re_pos (re_vertexOne_pos h hz)
  have hY := ne_zero_of_re_pos (re_vertexTwo_pos' h hz)
  have hX' := ne_zero_of_re_pos (re_vertexOne_pos h hR)
  have hY' := ne_zero_of_re_pos (re_vertexTwo_pos' h hR)
  have ha := ne_zero_of_re_pos (re_a_pos h)
  have hP : (arg ((1 - conj σ.vertexOne * σ.refl 2 z) * conj (1 - σ.vertexTwo * z) *
      conj (1 - conj σ.vertexOne * σ.vertexTwo)) : Real.Angle) =
        arg ((1 - conj σ.vertexOne * σ.vertexTwo) * conj (1 - conj σ.vertexOne * z) *
          (1 - σ.vertexTwo * σ.refl 2 z)) := by rw [wallTwo_product h hz]
  rw [arg_mul_coe_angle (mul_ne_zero hX' ((map_ne_zero _).2 hY)) ((map_ne_zero _).2 ha),
    arg_mul_coe_angle hX' ((map_ne_zero _).2 hY),
    arg_mul_coe_angle (mul_ne_zero ha ((map_ne_zero _).2 hX)) hY',
    arg_mul_coe_angle ha ((map_ne_zero _).2 hX), arg_conj_coe_angle, arg_conj_coe_angle,
    arg_conj_coe_angle] at hP
  rw [← sub_eq_zero] at hP ⊢
  simp only [Real.Angle.coe_sub, Real.Angle.coe_add, two_mul]
  rw [← hP]
  abel

omit h in
theorem continuousAt_one_sub_mul_arg (c : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hre : 0 < (1 - c * f z).re) : ContinuousAt (fun w => arg (1 - c * f w)) z := by
  have h1 : ContinuousAt (fun w => 1 - c * f w) z :=
    continuousAt_const.sub (continuousAt_const.mul hf)
  exact ContinuousAt.comp (f := fun w => 1 - c * f w) (continuousAt_arg (Or.inl hre)) h1

theorem continuousAt_refl_two {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt (σ.refl 2) z := by
  have hξ := HypFold.norm_vertexTwo_lt_one h
  have e : σ.refl 2 = fun w => HypFold.mob (-σ.vertexTwo)
      (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo w)) := by
    funext w
    rw [HypFold.refl_two_eq h, HypFold.mobInv_eq_mob_neg]
  rw [e]
  have h1 : ContinuousAt (HypFold.mob σ.vertexTwo) z :=
    (HypFold.contDiffAt_mob (HypFold.one_sub_conj_mul_ne_zero hξ hz)).continuousAt
  have h2 : ContinuousAt (fun w => exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo w))
      z := continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp h1)
  have hw : ‖exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)‖ < 1 := by
    rw [norm_mul, Complex.norm_conj, show -(2 * (σ.θ₂ : ℂ) * I) = ((-(2 * σ.θ₂) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact HypFold.norm_mob_lt_one hξ hz
  have h3 : ContinuousAt (HypFold.mob (-σ.vertexTwo))
      (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (HypFold.mob σ.vertexTwo z)) :=
    (HypFold.contDiffAt_mob (HypFold.one_sub_conj_mul_ne_zero (by rwa [norm_neg]) hw)).continuousAt
  exact ContinuousAt.comp (f := fun w => exp (-(2 * (σ.θ₂ : ℂ) * I)) *
    conj (HypFold.mob σ.vertexTwo w)) h3 h2

def wallSum (σ : CompactShape) (z : ℂ) : ℝ :=
  arg (1 - conj σ.vertexOne * z) - arg (1 - σ.vertexTwo * z) +
    arg (1 - conj σ.vertexOne * σ.refl 2 z) - arg (1 - σ.vertexTwo * σ.refl 2 z)

theorem refl_two_vertexTwo : σ.refl 2 σ.vertexTwo = σ.vertexTwo := by
  have hξ := HypFold.norm_vertexTwo_lt_one h
  have hm := HypFold.mob_vertexTwo_refl_two h hξ
  rw [HypFold.mob_self, map_zero, mul_zero] at hm
  have hR := HypFold.norm_refl_lt_one h 2 hξ
  have hne := HypFold.one_sub_conj_mul_ne_zero hξ hR
  rw [HypFold.mob, div_eq_zero_iff] at hm
  rcases hm with hm | hm
  · exact sub_eq_zero.mp hm
  · exact absurd hm hne

theorem wallSum_vertexTwo :
    wallSum σ σ.vertexTwo = 2 * arg (1 - conj σ.vertexOne * σ.vertexTwo) := by
  have hξ := HypFold.norm_vertexTwo_lt_one h
  have hreal : (1 : ℂ) - σ.vertexTwo * σ.vertexTwo = ((1 - σ.vertexTwo.re ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [← vertexTwo_real (σ := σ)]
    push_cast
    ring
  have hpos : 0 ≤ 1 - σ.vertexTwo.re ^ 2 := by
    have := abs_re_le_norm σ.vertexTwo
    nlinarith [abs_nonneg σ.vertexTwo.re, sq_abs σ.vertexTwo.re]
  rw [wallSum, refl_two_vertexTwo h, hreal, arg_ofReal_of_nonneg hpos]
  ring

theorem wallSum_const {z : ℂ} (hz : ‖z‖ < 1) :
    wallSum σ z = 2 * arg (1 - conj σ.vertexOne * σ.vertexTwo) := by
  have hξ := HypFold.norm_vertexTwo_lt_one h
  have hS : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball 0 1).isPreconnected
  have hT : ContinuousOn (wallSum σ) (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    have hR := HypFold.norm_refl_lt_one h 2 hw
    have c1 := continuousAt_one_sub_mul_arg (conj σ.vertexOne) continuousAt_id
      (re_vertexOne_pos h hw)
    have c2 := continuousAt_one_sub_mul_arg σ.vertexTwo continuousAt_id (re_vertexTwo_pos' h hw)
    have c3 := continuousAt_one_sub_mul_arg (conj σ.vertexOne) (continuousAt_refl_two h hw)
      (re_vertexOne_pos h hR)
    have c4 := continuousAt_one_sub_mul_arg σ.vertexTwo (continuousAt_refl_two h hw)
      (re_vertexTwo_pos' h hR)
    exact (((c1.sub c2).add c3).sub c4).continuousWithinAt
  have hconst := const_of_angle hS hT (θ := 2 * arg (1 - conj σ.vertexOne * σ.vertexTwo))
    (fun w hw => wallTwo_angle h (mem_ball_zero_iff.mp hw)) (mem_ball_zero_iff.mpr hξ)
    (mem_ball_zero_iff.mpr hz)
  rw [hconst, wallSum_vertexTwo h]

theorem two_arg_vertex :
    2 * arg (1 - conj σ.vertexOne * σ.vertexTwo) = Real.pi - (σ.θ₁ + σ.θ₂ + σ.θ₃) := by
  set a := 1 - conj σ.vertexOne * σ.vertexTwo with ha
  set S := σ.θ₁ + σ.θ₂ + σ.θ₃ with hS
  have hS1 := CompactShape.θ_sum_of_hyp σ h
  have hS0 : 0 < S := by
    have := CompactShape.θ₁_pos σ; have := CompactShape.θ₂_pos σ; have := CompactShape.θ₃_pos σ
    rw [hS]; linarith
  have hre := re_a_pos h
  have ha0 := ne_zero_of_re_pos hre
  have hca : conj a = -exp ((S : ℂ) * I) * a := by
    rw [ha, map_sub, map_one, map_mul, Complex.conj_conj, HypFold.conj_vertexTwo, mul_comm,
      HypFold.one_sub_mul_vertex_eq h, hS]
  have hexp : arg (exp ((S : ℂ) * I)) = S := by
    rw [exp_mul_I, arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith⟩]
  have e : ((-arg a : ℝ) : Real.Angle) =
      (S : Real.Angle) + (arg a : Real.Angle) + (Real.pi : Real.Angle) := by
    rw [Real.Angle.coe_neg, ← arg_conj_coe_angle, hca, neg_mul,
      arg_neg_coe_angle (mul_ne_zero (Complex.exp_ne_zero _) ha0),
      arg_mul_coe_angle (Complex.exp_ne_zero _) ha0, hexp]
  have hπ2 : (Real.pi : Real.Angle) + (Real.pi : Real.Angle) = 0 := by
    rw [← Real.Angle.coe_add, ← two_mul, Real.Angle.coe_two_pi]
  have hb := abs_lt.mp (abs_arg_lt_of_re_pos hre)
  apply eq_of_angle_eq
  · simp only [two_mul, Real.Angle.coe_add, Real.Angle.coe_sub]
    rw [Real.Angle.coe_neg] at e
    rw [← sub_eq_zero]
    have hE : (S : Real.Angle) + (arg a : Real.Angle) + (Real.pi : Real.Angle) -
        -(arg a : Real.Angle) = 0 := sub_eq_zero.mpr e.symm
    calc (arg a : Real.Angle) + (arg a : Real.Angle) - ((Real.pi : Real.Angle) - (S : Real.Angle))
        = ((S : Real.Angle) + (arg a : Real.Angle) + (Real.pi : Real.Angle) -
            -(arg a : Real.Angle)) - ((Real.pi : Real.Angle) + (Real.pi : Real.Angle)) := by abel
      _ = 0 := by rw [hE, hπ2, sub_zero]
  · rw [abs_lt]
    constructor <;> linarith

theorem hypGauge_wallTwo {w : ℂ} (hw : ‖w‖ < 1) :
    (hypGauge σ.vertexOne w - hypGauge σ.vertexTwo w) +
      (hypGauge σ.vertexOne (σ.refl 2 w) - hypGauge σ.vertexTwo (σ.refl 2 w)) = hypArea σ := by
  have hc := wallSum_const h hw
  have hv := two_arg_vertex h
  simp only [hypGauge, HypFold.conj_vertexTwo]
  rw [wallSum] at hc
  unfold hypArea
  linarith

end Shape

end Hyp

end ClosedTriangle

end GC.Seifert
