import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# Disc automorphisms for the hyperbolic compact fold

Lane CF-H, tier 1 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§1, curvature `-1`). For `ε = 1` the disc coordinate of `CompactShape` is the disc automorphism
`mob a z = (z - a)/(1 - ā z)` (`disc_eq_mob`), with inverse `mobInv a w = (w + a)/(1 + ā w)`
(`disc_eq_mob`, `discInv_eq_mobInv`, `mob_mobInv`, `mobInv_mob`). On the open unit disc its
denominator does not vanish, it maps the disc into itself with
`1 - |mob a z|² = (1 - |a|²)(1 - |z|²)/|1 - ā z|²` (`one_sub_normSq_mob`), and it is holomorphic
with derivative `(1 - |a|²)/(1 - ā z)²` (`hasDerivAt_mob`), so its real Jacobian is positive.

The pseudo-hyperbolic distance `‖mob a z‖ = tanh (d(a, z)/2)` is invariant under every disc
automorphism: `mob (mob v a) (mob v z) = mob a z · (1 - v ā)/(1 - v̄ a)`
(`mob_mob_mob`, `norm_mob_mob_mob`), under rotations (`mob_mul_mul`) and under complex conjugation
(`mob_conj_conj`). Along a circle `e^{it} W` about the origin the squared distance to a point `p`
has the explicit derivative `2 Im (p̄ W) (1 - |p|²)(1 - |W|²)/|1 - p̄ W|⁴`
(`hasDerivAt_normSq_mob_circle`): it is the source of every strict angle derivative of the
corners.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace HypFold

def mob (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

def mobInv (a w : ℂ) : ℂ := (w + a) / (1 + conj a * w)

theorem mob_self (a : ℂ) : mob a a = 0 := by
  simp [mob]

theorem mob_zero_left (z : ℂ) : mob 0 z = z := by
  simp [mob]

theorem mob_zero_right (a : ℂ) : mob a 0 = -a := by
  simp [mob]

theorem normSq_lt_one_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : normSq z < 1 := by
  rw [← Complex.sq_norm]
  nlinarith [norm_nonneg z]

theorem norm_conj_mul_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖conj a * z‖ < 1 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg a, norm_nonneg z]

theorem one_sub_conj_mul_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := (sub_eq_zero.1 h).symm
  have := norm_conj_mul_lt_one ha hz
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem one_add_conj_mul_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 + conj a * w ≠ 0 := by
  have h := one_sub_conj_mul_ne_zero ha (show ‖-w‖ < 1 by rwa [norm_neg])
  rwa [mul_neg, sub_neg_eq_add] at h

theorem normSq_one_sub_conj_mul_sub (a z : ℂ) :
    normSq (1 - conj a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

theorem one_sub_normSq_mob {a z : ℂ} (h : 1 - conj a * z ≠ 0) :
    1 - normSq (mob a z) = (1 - normSq a) * (1 - normSq z) / normSq (1 - conj a * z) := by
  have hp : normSq (1 - conj a * z) ≠ 0 := normSq_eq_zero.not.2 h
  rw [mob, map_div₀, eq_div_iff hp, sub_mul, div_mul_cancel₀ _ hp, one_mul,
    ← normSq_one_sub_conj_mul_sub]

theorem normSq_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : normSq (mob a z) < 1 := by
  have h := one_sub_normSq_mob (one_sub_conj_mul_ne_zero ha hz)
  have h1 := normSq_lt_one_of_norm_lt ha
  have h2 := normSq_lt_one_of_norm_lt hz
  have hp : 0 < normSq (1 - conj a * z) := normSq_pos.2 (one_sub_conj_mul_ne_zero ha hz)
  have : 0 < (1 - normSq a) * (1 - normSq z) / normSq (1 - conj a * z) := by
    apply div_pos _ hp
    nlinarith
  linarith

theorem norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have h := normSq_mob_lt_one ha hz
  rw [← Complex.sq_norm] at h
  nlinarith [norm_nonneg (mob a z)]

theorem one_sub_conj_mul_self_ne_zero {a : ℂ} (ha : normSq a ≠ 1) : (1 : ℂ) - conj a * a ≠ 0 := by
  rw [mul_comm, Complex.mul_conj]
  intro h
  apply ha
  have := congrArg Complex.re h
  simp at this
  linarith

theorem mob_mobInv {a w : ℂ} (ha : normSq a ≠ 1) (hw : 1 + conj a * w ≠ 0) :
    mob a (mobInv a w) = w := by
  have ha' := one_sub_conj_mul_self_ne_zero ha
  have hnum : (w + a) / (1 + conj a * w) - a = w * (1 - conj a * a) / (1 + conj a * w) := by
    rw [eq_div_iff hw, sub_mul, div_mul_cancel₀ _ hw]
    ring
  have hden : 1 - conj a * ((w + a) / (1 + conj a * w)) =
      (1 - conj a * a) / (1 + conj a * w) := by
    rw [eq_div_iff hw, sub_mul, mul_assoc, div_mul_cancel₀ _ hw]
    ring
  rw [mob, mobInv, hnum, hden, div_div_div_cancel_right₀ hw, mul_div_assoc, div_self ha', mul_one]

theorem mobInv_mob {a z : ℂ} (ha : normSq a ≠ 1) (hz : 1 - conj a * z ≠ 0) :
    mobInv a (mob a z) = z := by
  have ha' := one_sub_conj_mul_self_ne_zero ha
  have hnum : (z - a) / (1 - conj a * z) + a = z * (1 - conj a * a) / (1 - conj a * z) := by
    rw [eq_div_iff hz, add_mul, div_mul_cancel₀ _ hz]
    ring
  have hden : 1 + conj a * ((z - a) / (1 - conj a * z)) =
      (1 - conj a * a) / (1 - conj a * z) := by
    rw [eq_div_iff hz, add_mul, mul_assoc, div_mul_cancel₀ _ hz]
    ring
  rw [mobInv, mob, hnum, hden, div_div_div_cancel_right₀ hz, mul_div_assoc, div_self ha', mul_one]

theorem one_add_conj_mul_mob {a z : ℂ} (h : 1 - conj a * z ≠ 0) :
    1 + conj a * mob a z = (1 - normSq a) / (1 - conj a * z) := by
  rw [mob, Complex.normSq_eq_conj_mul_self]
  field_simp
  ring

theorem one_sub_conj_mul_mobInv {a w : ℂ} (h : 1 + conj a * w ≠ 0) :
    1 - conj a * mobInv a w = (1 - normSq a) / (1 + conj a * w) := by
  rw [mobInv, Complex.normSq_eq_conj_mul_self]
  field_simp
  ring

theorem mob_sub_mob {v a z : ℂ} (ha : 1 - conj v * a ≠ 0) (hz : 1 - conj v * z ≠ 0) :
    mob v z - mob v a = (z - a) * (1 - normSq v) / ((1 - conj v * z) * (1 - conj v * a)) := by
  rw [mob, mob, Complex.normSq_eq_conj_mul_self, div_sub_div _ _ hz ha]
  congr 1
  ring

theorem conj_one_sub_conj_mul (v a : ℂ) : conj (1 - conj v * a) = 1 - v * conj a := by
  simp [map_sub, map_mul]

theorem one_sub_conj_mob_mul_mob {v a z : ℂ} (ha : 1 - conj v * a ≠ 0)
    (hz : 1 - conj v * z ≠ 0) :
    1 - conj (mob v a) * mob v z =
      (1 - normSq v) * (1 - conj a * z) / ((1 - v * conj a) * (1 - conj v * z)) := by
  have ha' : 1 - v * conj a ≠ 0 := by
    rw [← conj_one_sub_conj_mul]
    exact (map_ne_zero (starRingEnd ℂ)).2 ha
  rw [mob, mob, map_div₀, conj_one_sub_conj_mul, eq_div_iff (mul_ne_zero ha' hz),
    Complex.normSq_eq_conj_mul_self, sub_mul, one_mul, div_mul_div_comm,
    div_mul_cancel₀ _ (mul_ne_zero ha' hz)]
  simp only [map_sub]
  ring

theorem mob_mob_mob {v a z : ℂ} (hv : normSq v ≠ 1) (ha : 1 - conj v * a ≠ 0)
    (hz : 1 - conj v * z ≠ 0) (haz : 1 - conj a * z ≠ 0) :
    mob (mob v a) (mob v z) = mob a z * ((1 - v * conj a) / (1 - conj v * a)) := by
  have hv' : (1 : ℂ) - (normSq v : ℂ) ≠ 0 := by
    intro h
    apply hv
    exact_mod_cast (sub_eq_zero.1 h).symm
  have ha' : 1 - v * conj a ≠ 0 := by
    rw [← conj_one_sub_conj_mul]
    exact (map_ne_zero (starRingEnd ℂ)).2 ha
  rw [show mob (mob v a) (mob v z) = (mob v z - mob v a) / (1 - conj (mob v a) * mob v z) from rfl,
    mob_sub_mob ha hz, one_sub_conj_mob_mul_mob ha hz, mob, div_div_div_eq,
    div_mul_div_comm, div_eq_div_iff (mul_ne_zero (mul_ne_zero hz ha) (mul_ne_zero hv' haz))
      (mul_ne_zero haz ha)]
  ring

theorem norm_one_sub_mul_conj {v a : ℂ} :
    ‖1 - v * conj a‖ = ‖1 - conj v * a‖ := by
  rw [← Complex.norm_conj]
  simp [map_sub, map_mul]

theorem norm_mob_mob_mob {v a z : ℂ} (hv : normSq v ≠ 1) (ha : 1 - conj v * a ≠ 0)
    (hz : 1 - conj v * z ≠ 0) (haz : 1 - conj a * z ≠ 0) :
    ‖mob (mob v a) (mob v z)‖ = ‖mob a z‖ := by
  rw [mob_mob_mob hv ha hz haz, norm_mul, norm_div, norm_one_sub_mul_conj,
    div_self (norm_ne_zero_iff.2 ha), mul_one]

theorem mob_mul_mul {u : ℂ} (hu : ‖u‖ = 1) (a z : ℂ) : mob (u * a) (u * z) = u * mob a z := by
  have hcu : conj u * u = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have e : 1 - conj (u * a) * (u * z) = 1 - conj a * z := by
    rw [map_mul]
    linear_combination (-(conj a * z)) * hcu
  rw [mob, mob, e, ← mul_sub, mul_div_assoc]

theorem mob_conj_conj (a z : ℂ) : mob (conj a) (conj z) = conj (mob a z) := by
  simp [mob, map_div₀, map_sub, map_mul]

theorem norm_mob_comm (a z : ℂ) : ‖mob a z‖ = ‖mob z a‖ := by
  rw [mob, mob, norm_div, norm_div, ← norm_neg (z - a), neg_sub]
  congr 1
  rw [← Complex.norm_conj (1 - conj z * a)]
  simp [map_sub, map_mul, mul_comm]

theorem mob_mul_normSq {a z : ℂ} (h : 1 - conj a * z ≠ 0) :
    mob a z * (normSq (1 - conj a * z) : ℂ) = (z - a) * conj (1 - conj a * z) := by
  rw [mob, Complex.normSq_eq_conj_mul_self, div_mul_eq_mul_div, mul_div_assoc,
    mul_div_cancel_right₀ _ h]

theorem im_mob_mul_normSq (a z : ℂ) :
    (mob a z).im * normSq (1 - conj a * z) = ((z - a) * conj (1 - conj a * z)).im := by
  by_cases h : 1 - conj a * z = 0
  · simp [h]
  · rw [← mob_mul_normSq h, Complex.mul_im, ofReal_re, ofReal_im, mul_zero, zero_add]

theorem hasDerivAt_mob {a z : ℂ} (h : 1 - conj a * z ≠ 0) :
    HasDerivAt (mob a) ((1 - conj a * a) / (1 - conj a * z) ^ 2) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-(conj a)) z := by
    simpa using ((hasDerivAt_id z).const_mul (conj a)).const_sub 1
  have h3 := h1.div h2 h
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem contDiffAt_mob {a z : ℂ} (h : 1 - conj a * z ≠ 0) : ContDiffAt ℝ ∞ (mob a) z := by
  have h1 : ContDiffAt ℂ ∞ (fun w : ℂ => w - a) z := contDiffAt_id.sub contDiffAt_const
  have h2 : ContDiffAt ℂ ∞ (fun w : ℂ => 1 - conj a * w) z :=
    contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)
  exact (h1.div h2 h).restrict_scalars ℝ

theorem det_fderiv_mob_pos {a z : ℂ} (ha : normSq a ≠ 1) (h : 1 - conj a * z ≠ 0) :
    0 < (fderiv ℝ (mob a) z).det := by
  rw [det_fderiv_of_hasDerivAt (hasDerivAt_mob h)]
  apply normSq_pos.2
  apply div_ne_zero _ (pow_ne_zero 2 h)
  rw [mul_comm, Complex.mul_conj]
  intro h0
  apply ha
  have := congrArg Complex.re h0
  simp at this
  linarith

theorem normSq_mob_eq (p W : ℂ) :
    normSq (mob p W) = normSq (W - p) / normSq (1 - conj p * W) := by
  rw [mob, map_div₀]

theorem normSq_sub_circle (p W : ℂ) (t : ℝ) :
    normSq (W * exp ((t : ℂ) * I) - p) =
      normSq W - 2 * (conj p * (W * exp ((t : ℂ) * I))).re + normSq p := by
  have hn : normSq (exp ((t : ℂ) * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have e : normSq (W * exp ((t : ℂ) * I) - p) =
      normSq (W * exp ((t : ℂ) * I)) - 2 * (conj p * (W * exp ((t : ℂ) * I))).re + normSq p := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im]
    ring
  rw [e, map_mul, hn, mul_one]

theorem normSq_one_sub_circle (p W : ℂ) (t : ℝ) :
    normSq (1 - conj p * (W * exp ((t : ℂ) * I))) =
      1 - 2 * (conj p * (W * exp ((t : ℂ) * I))).re + normSq p * normSq W := by
  have hn : normSq (exp ((t : ℂ) * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  have e : normSq (1 - conj p * (W * exp ((t : ℂ) * I))) =
      1 - 2 * (conj p * (W * exp ((t : ℂ) * I))).re +
        normSq (conj p * (W * exp ((t : ℂ) * I))) := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
    ring
  rw [e, map_mul, map_mul, hn, mul_one, Complex.normSq_conj]

theorem hasDerivAt_re_conj_mul_circle (p W : ℂ) :
    HasDerivAt (fun t : ℝ => (conj p * (W * exp ((t : ℂ) * I))).re)
      (-(conj p * W).im) 0 := by
  have h : HasDerivAt (fun t : ℝ => conj p * (W * exp ((t : ℂ) * I))) (conj p * W * I) 0 := by
    have he : HasDerivAt (fun t : ℝ => exp ((t : ℂ) * I)) I 0 := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const I).cexp
      simpa using this
    have := (he.const_mul W).const_mul (conj p)
    simpa [mul_assoc] using this
  have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h)
  refine hre.congr_deriv ?_
  simp [mul_re, I_re, I_im]

theorem hasDerivAt_normSq_mob_circle {p W : ℂ} (h : 1 - conj p * W ≠ 0) :
    HasDerivAt (fun t : ℝ => normSq (mob p (W * exp ((t : ℂ) * I))))
      (2 * (conj p * W).im * (1 - normSq p) * (1 - normSq W) /
        normSq (1 - conj p * W) ^ 2) 0 := by
  have hq : (fun t : ℝ => normSq (mob p (W * exp ((t : ℂ) * I)))) = fun t : ℝ =>
      (normSq W - 2 * (conj p * (W * exp ((t : ℂ) * I))).re + normSq p) /
        (1 - 2 * (conj p * (W * exp ((t : ℂ) * I))).re + normSq p * normSq W) := by
    funext t
    rw [normSq_mob_eq, normSq_sub_circle, normSq_one_sub_circle]
  rw [hq]
  have hr := hasDerivAt_re_conj_mul_circle p W
  have hN := ((hr.const_mul 2).const_sub (normSq W)).add_const (normSq p)
  have hD := ((hr.const_mul 2).const_sub 1).add_const (normSq p * normSq W)
  have hD0 : 1 - 2 * (conj p * (W * exp (((0 : ℝ) : ℂ) * I))).re + normSq p * normSq W ≠ 0 := by
    rw [← normSq_one_sub_circle]
    simpa using normSq_eq_zero.not.2 h
  have hdiv := hN.div hD hD0
  refine hdiv.congr_deriv ?_
  have e1 : 1 - 2 * (conj p * (W * exp (((0 : ℝ) : ℂ) * I))).re + normSq p * normSq W =
      normSq (1 - conj p * W) := by
    rw [← normSq_one_sub_circle]
    simp
  have e2 : normSq W - 2 * (conj p * (W * exp (((0 : ℝ) : ℂ) * I))).re + normSq p =
      normSq (W - p) := by
    rw [← normSq_sub_circle]
    simp
  rw [e1, e2]
  have hp : normSq (1 - conj p * W) ≠ 0 := normSq_eq_zero.not.2 h
  rw [div_eq_div_iff (pow_ne_zero 2 hp) (pow_ne_zero 2 hp)]
  have := normSq_one_sub_conj_mul_sub p W
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re,
    one_im] at this ⊢
  linear_combination (-(2 * (p.re * W.im - p.im * W.re)) *
    ((1 - (p.re * W.re + p.im * W.im)) ^ 2 + (-(p.re * W.im - p.im * W.re)) ^ 2)) * this

end HypFold

namespace CompactShape

variable {σ : CompactShape}

theorem eps_hyp (h : σ.curv = .hyperbolic) : σ.eps = 1 := by
  unfold eps
  rw [h]
  rfl

theorem disc_eq_mob (h : σ.curv = .hyperbolic) (v z : ℂ) : σ.disc v z = HypFold.mob v z := by
  rw [disc, eps_hyp h, HypFold.mob]
  simp

theorem discInv_eq_mobInv (h : σ.curv = .hyperbolic) (v w : ℂ) :
    σ.discInv v w = HypFold.mobInv v w := by
  rw [discInv, eps_hyp h, HypFold.mobInv]
  simp

theorem plane_hyp (h : σ.curv = .hyperbolic) : σ.plane = Metric.ball 0 1 := by
  ext z
  simp only [plane, eps_hyp h, one_mul, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
  constructor
  · intro hz
    nlinarith [norm_nonneg z]
  · intro hz
    nlinarith [norm_nonneg z]

end CompactShape

end GC.Seifert
