import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldOneConeLayout

/-!
# The bridges of the two-cone shapes `(p₁, p₂, ⊤)`

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §2 and §4, and
erratum 4). For a shape with a second cone at `v₂ = i sin θ₂/4` (`θ₂ > 0`) the wall bridges at the
walls through `v₂` use the virtual height `η₂ = coneHeight v₂`:
* wall 0: `bridgeZeroC = outerBridge K (3/2) y η₂ w₀ q₀` with the `σ₀`-odd wall function
  `w₀ = -Im ω₂` (`ω₂ = coneDisc v₂ z`) and the factorization `η₂ - y = w₀² q₀`
  (`etaTwoC_sub_im`, from `coneHeight_sub_im` at `v₂`);
* wall 2: `bridgeTwoC = innerBridge K η₂ η₁ w q` with the `σ₂`-odd wall function `w = wallTwo` and
  the factorization `η₁ η₂ - K = w² q` (`etaOne_mul_etaTwoC_sub`): the product identity
  `product_identity_two` and the bracket identity `bracket_identity` in the rotated disc coordinate
  `ω' = e^{-iθ₁} ω₁ = X + iY` at `v₁`, with `t = |coneDisc v₁ v₂|` and `μ = |ω₂|` related by the
  Möbius identity `μ² |1 - t ω'|² = |ω' - t|²` (`norm_coneDisc_moebius`); the cofactor is positive
  on `domTwoC` (`μ + (t - X)/(1 - tX) > 0`, off the geodesic ray beyond `v₂`), which contains every
  point with `Y ≠ 0` (`mu_add_pos_of_im_ne`).
Both bridges have the expected moduli and imaginary parts of the sign of the wall function, and
are equivariant for their wall reflections (`bridgeZeroC_refl_zero`, `bridgeTwoC_refl_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

/-! ### Data at the second cone -/

def discTwo (z : ℂ) : ℂ := coneDisc σ.vertexTwo z

def etaTwoC (z : ℂ) : ℝ := coneHeight σ.vertexTwo z

def tCone : ℝ := Real.cos ((σ.θ₁ + σ.θ₂) / 2) / Real.cos ((σ.θ₁ - σ.θ₂) / 2)

def rotOne (z : ℂ) : ℂ := exp (-(σ.θ₁ * I)) * σ.discOne z

theorem tCone_pos : 0 < σ.tCone := div_pos σ.cos_half_sum_pos σ.cos_half_diff_pos

theorem tCone_lt_one (hθ : 0 < σ.θ₂) : σ.tCone < 1 := by
  rw [tCone, div_lt_one σ.cos_half_diff_pos, ← Real.cos_abs ((σ.θ₁ - σ.θ₂) / 2)]
  have h1 := σ.θ₁_pos
  have h2 := σ.sum_lt
  apply Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
  rw [abs_lt]
  constructor <;> linarith

theorem norm_rotOne (z : ℂ) : ‖σ.rotOne z‖ = ‖σ.discOne z‖ := by
  rw [rotOne, norm_mul, show -((σ.θ₁ : ℂ) * I) = ((-σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem rotOne_im (z : ℂ) : (σ.rotOne z).im = -σ.wallTwo z := by
  rw [wallTwo, rotOne, neg_neg]

theorem vertexTwo_im_pos' (hθ : 0 < σ.θ₂) : 0 < σ.vertexTwo.im := σ.vertexTwo_im_pos hθ

theorem norm_discTwo_lt_one (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) : ‖σ.discTwo z‖ < 1 :=
  norm_coneDisc_lt_one (σ.vertexTwo_im_pos hθ) hz

theorem moebius_rel (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    ‖σ.discTwo z‖ ^ 2 * ((1 - σ.tCone * (σ.rotOne z).re) ^ 2 +
        σ.tCone ^ 2 * (σ.rotOne z).im ^ 2) =
      ((σ.rotOne z).re - σ.tCone) ^ 2 + (σ.rotOne z).im ^ 2 := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have h := norm_coneDisc_moebius hv1 hv2 hz
  rw [σ.coneDisc_vertexOne_vertexTwo hθ] at h
  set e := exp ((σ.θ₁ : ℂ) * I) with he
  have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hee : conj e * e = 1 := by
    rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq, hen]; norm_num
  have hrot : σ.rotOne z = conj e * σ.discOne z := by
    rw [rotOne, he, ← Complex.exp_conj]
    congr 2
    simp
  have e1 : 1 - conj ((σ.tCone : ℂ) * e) * coneDisc σ.vertexOne z = 1 - σ.tCone * σ.rotOne z := by
    rw [hrot, map_mul, Complex.conj_ofReal, tCone, discOne]
    ring
  have e2 : coneDisc σ.vertexOne z - (σ.tCone : ℂ) * e = e * (σ.rotOne z - σ.tCone) := by
    rw [hrot, discOne]
    linear_combination (-coneDisc σ.vertexOne z) * hee
  rw [show ((Real.cos ((σ.θ₁ + σ.θ₂) / 2) / Real.cos ((σ.θ₁ - σ.θ₂) / 2) : ℝ) : ℂ) =
    (σ.tCone : ℂ) from rfl, e1, e2, norm_mul, hen, one_mul] at h
  have h2 : ‖σ.discTwo z‖ ^ 2 * ‖1 - (σ.tCone : ℂ) * σ.rotOne z‖ ^ 2 =
      ‖σ.rotOne z - σ.tCone‖ ^ 2 := by
    rw [← mul_pow, discTwo, h]
  have n1 : ‖1 - (σ.tCone : ℂ) * σ.rotOne z‖ ^ 2 =
      (1 - σ.tCone * (σ.rotOne z).re) ^ 2 + σ.tCone ^ 2 * (σ.rotOne z).im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  have n2 : ‖σ.rotOne z - σ.tCone‖ ^ 2 = ((σ.rotOne z).re - σ.tCone) ^ 2 + (σ.rotOne z).im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp; ring
  rw [n1, n2] at h2
  exact h2

/-! ### The wall-2 bridge -/

def cofTwoC (z : ℂ) : ℝ :=
  2 * (σ.vertexOne.im * σ.vertexTwo.im / (1 - σ.tCone)) *
    (((1 - σ.tCone * ‖σ.discTwo z‖) / (‖σ.discOne z‖ + (σ.rotOne z).re) +
      (1 - σ.tCone ^ 2) * (1 - 2 * σ.tCone * (σ.rotOne z).re + σ.tCone ^ 2) /
        ((1 - σ.tCone * (σ.rotOne z).re) * ((1 - σ.tCone * (σ.rotOne z).re) ^ 2 +
          σ.tCone ^ 2 * (σ.rotOne z).im ^ 2) * (‖σ.discTwo z‖ +
            (σ.tCone - (σ.rotOne z).re) / (1 - σ.tCone * (σ.rotOne z).re)))) /
      ((1 - ‖σ.discOne z‖) * (1 - ‖σ.discTwo z‖)))

def domTwoC : Set ℂ :=
  {z | 0 < z.im ∧ 0 < ‖σ.discOne z‖ + (σ.rotOne z).re ∧
    0 < ‖σ.discTwo z‖ + (σ.tCone - (σ.rotOne z).re) / (1 - σ.tCone * (σ.rotOne z).re)}

def bridgeTwoC (z : ℂ) : ℂ :=
  innerBridge σ.constK (σ.etaTwoC z) (σ.etaOne z) (σ.wallTwo z) (σ.cofTwoC z)

theorem one_sub_t_rot_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    0 < 1 - σ.tCone * (σ.rotOne z).re := by
  have ht := σ.tCone_lt_one hθ
  have ht0 := σ.tCone_pos
  have hX : (σ.rotOne z).re ≤ ‖σ.rotOne z‖ := Complex.re_le_norm _
  rw [σ.norm_rotOne] at hX
  have h1 := σ.norm_discOne_lt_one hz
  nlinarith

theorem etaOne_mul_etaTwoC_sub (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    σ.etaOne z * σ.etaTwoC z - σ.constK = σ.wallTwo z ^ 2 * σ.cofTwoC z := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hr1 := σ.norm_discOne_lt_one hz.1
  have hμ1 := σ.norm_discTwo_lt_one hθ hz.1
  have ht := σ.tCone_lt_one hθ
  have hK := σ.constK_eq_cones hθ
  have hprod := product_identity_two σ.vertexOne.im σ.vertexTwo.im ‖σ.discOne z‖ ‖σ.discTwo z‖
    σ.tCone hr1 hμ1 ht
  have hr : ‖σ.discOne z‖ ^ 2 = (σ.rotOne z).re ^ 2 + (σ.rotOne z).im ^ 2 := by
    rw [← σ.norm_rotOne, Complex.sq_norm, normSq_apply]; ring
  have hbr := bracket_identity ‖σ.discOne z‖ ‖σ.discTwo z‖ σ.tCone (σ.rotOne z).re
    (σ.rotOne z).im hr (σ.moebius_rel hθ hz.1) hz.2.1 (σ.one_sub_t_rot_pos hθ hz.1) hz.2.2
  rw [σ.rotOne_im, neg_sq] at hbr
  change σ.vertexOne.im * (1 + ‖σ.discOne z‖) / (1 - ‖σ.discOne z‖) *
    (σ.vertexTwo.im * (1 + ‖σ.discTwo z‖) / (1 - ‖σ.discTwo z‖)) - σ.constK = _
  rw [hK, ← tCone, hprod, hbr, cofTwoC, σ.rotOne_im, neg_sq]
  ring

theorem mu_add_pos_of_im_ne (hθ : 0 < σ.θ₂) {z : ℂ} (hz : 0 < z.im) (hY : σ.wallTwo z ≠ 0) :
    0 < ‖σ.discTwo z‖ + (σ.tCone - (σ.rotOne z).re) / (1 - σ.tCone * (σ.rotOne z).re) := by
  have hm := σ.moebius_rel hθ hz
  have hd := σ.one_sub_t_rot_pos hθ hz
  have ht := σ.tCone_lt_one hθ
  have ht0 := σ.tCone_pos
  set X := (σ.rotOne z).re
  set Y := (σ.rotOne z).im
  set μ := ‖σ.discTwo z‖
  set t := σ.tCone
  have hY2 : 0 < Y ^ 2 := by
    have : Y ≠ 0 := by rw [show Y = -σ.wallTwo z from σ.rotOne_im z]; exact neg_ne_zero.2 hY
    positivity
  have hX : X ≤ 1 := by
    have := Complex.re_le_norm (σ.rotOne z)
    rw [σ.norm_rotOne] at this
    linarith [σ.norm_discOne_lt_one hz]
  have hD : 0 < (1 - t * X) ^ 2 + t ^ 2 * Y ^ 2 := by positivity
  have hgap : ((t - X) / (1 - t * X)) ^ 2 < μ ^ 2 := by
    rw [div_pow, div_lt_iff₀ (by positivity)]
    have key : μ ^ 2 * (1 - t * X) ^ 2 - (t - X) ^ 2 =
        Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) / ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) *
          (1 - t * X) ^ 2 / (1 - t * X) ^ 2 * 1 := by
      field_simp
      nlinarith [hm]
    have hpos : 0 < Y ^ 2 * ((1 - t ^ 2) * (1 - 2 * t * X + t ^ 2)) /
        ((1 - t * X) ^ 2 + t ^ 2 * Y ^ 2) * (1 - t * X) ^ 2 / (1 - t * X) ^ 2 * 1 := by
      have h1 : 0 < 1 - t ^ 2 := by nlinarith
      have h2 : 0 < 1 - 2 * t * X + t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
      positivity
    linarith
  have hμ0 : 0 ≤ μ := norm_nonneg _
  have habs : |(t - X) / (1 - t * X)| < μ := by
    rw [← abs_of_nonneg hμ0]; exact sq_lt_sq.1 hgap
  linarith [neg_abs_le ((t - X) / (1 - t * X))]

theorem cofTwoC_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) : 0 < σ.cofTwoC z := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hr1 := σ.norm_discOne_lt_one hz.1
  have hμ1 := σ.norm_discTwo_lt_one hθ hz.1
  have hμ0 := norm_nonneg (σ.discTwo z)
  have ht := σ.tCone_lt_one hθ
  have ht0 := σ.tCone_pos
  have hd := σ.one_sub_t_rot_pos hθ hz.1
  have hX : (σ.rotOne z).re ≤ 1 := by
    have := Complex.re_le_norm (σ.rotOne z)
    rw [σ.norm_rotOne] at this
    linarith
  have h1 : 0 < 1 - σ.tCone * ‖σ.discTwo z‖ := by nlinarith
  have h2 : 0 < 1 - σ.tCone ^ 2 := by nlinarith
  have h3 : 0 < 1 - 2 * σ.tCone * (σ.rotOne z).re + σ.tCone ^ 2 := by
    nlinarith [sq_nonneg (1 - σ.tCone)]
  have h4 : 0 < (1 - σ.tCone * (σ.rotOne z).re) ^ 2 + σ.tCone ^ 2 * (σ.rotOne z).im ^ 2 := by
    positivity
  have h5 := hz.2.1
  have h6 := hz.2.2
  have h7 : 0 < 1 - ‖σ.discOne z‖ := by linarith
  have h8 : 0 < 1 - ‖σ.discTwo z‖ := by linarith
  have h9 : 0 < 1 - σ.tCone := by linarith
  unfold cofTwoC
  positivity

theorem norm_bridgeTwoC_sub (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ‖σ.bridgeTwoC z - 3 / 2‖ = coneProfile σ.constK (σ.etaTwoC z) :=
  norm_innerBridge_sub σ.constK_pos (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1)
    (σ.etaOne_pos hz.1) (σ.cofTwoC_pos hθ hz) (σ.etaOne_mul_etaTwoC_sub hθ hz)

theorem norm_bridgeTwoC_add (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ‖σ.bridgeTwoC z + 3 / 2‖ = coneProfile σ.constK (σ.etaOne z) :=
  norm_innerBridge_add σ.constK_pos (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1)
    (σ.etaOne_pos hz.1) (σ.cofTwoC_pos hθ hz) (σ.etaOne_mul_etaTwoC_sub hθ hz)

theorem norm_bridgeTwoC_lt_two (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ‖σ.bridgeTwoC z‖ < 2 :=
  norm_innerBridge_lt_two σ.constK_pos (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1)
    (σ.etaOne_pos hz.1) (σ.cofTwoC_pos hθ hz) (σ.etaOne_mul_etaTwoC_sub hθ hz)

theorem bridgeTwoC_im_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) (hw : 0 < σ.wallTwo z) :
    0 < (σ.bridgeTwoC z).im :=
  innerBridge_im_pos σ.constK_pos (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1)
    (σ.etaOne_pos hz.1) (σ.cofTwoC_pos hθ hz) hw

theorem norm_discTwo_refl_two {z : ℂ} (hz : 0 < z.im) :
    ‖σ.discTwo (σ.refl 2 z)‖ = ‖σ.discTwo z‖ := by
  rw [discTwo, discTwo, σ.coneDisc_vertexTwo_refl_two (σ.ne_centre_of_im_pos hz), norm_mul,
    Complex.norm_conj]
  rw [show 2 * ((Real.pi - σ.θ₂ : ℝ) : ℂ) * I = ((2 * (Real.pi - σ.θ₂) : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem rotOne_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.rotOne (σ.refl 2 z) = conj (σ.rotOne z) := by
  have hd : σ.discOne (σ.refl 2 z) = exp (2 * σ.θ₁ * I) * conj (σ.discOne z) :=
    σ.coneDisc_vertexOne_refl_two (σ.ne_centre_of_im_pos hz)
  rw [rotOne, rotOne, hd, map_mul, ← Complex.exp_conj, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp
  ring

theorem etaTwoC_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.etaTwoC (σ.refl 2 z) = σ.etaTwoC z := by
  simp only [etaTwoC, coneHeight]
  rw [← discTwo, ← discTwo, σ.norm_discTwo_refl_two hz]

theorem wallTwo_refl_two {z : ℂ} (hz : 0 < z.im) : σ.wallTwo (σ.refl 2 z) = -σ.wallTwo z := by
  rw [← neg_neg (σ.wallTwo (σ.refl 2 z)), ← σ.rotOne_im, σ.rotOne_refl_two hz, conj_im,
    σ.rotOne_im, neg_neg]

theorem cofTwoC_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.cofTwoC (σ.refl 2 z) = σ.cofTwoC z := by
  have h1 : ‖σ.discOne (σ.refl 2 z)‖ = ‖σ.discOne z‖ := σ.norm_discOne_refl_two hz
  simp only [cofTwoC, σ.norm_discTwo_refl_two hz, h1, σ.rotOne_refl_two hz, conj_re, conj_im,
    neg_sq]

theorem bridgeTwoC_refl_two {z : ℂ} (hz : 0 < z.im) :
    σ.bridgeTwoC (σ.refl 2 z) = conj (σ.bridgeTwoC z) := by
  rw [bridgeTwoC, bridgeTwoC, σ.etaTwoC_refl_two hz, σ.etaOne_refl_two hz,
    σ.wallTwo_refl_two hz, σ.cofTwoC_refl_two hz, innerBridge_neg]

theorem isOpen_domTwoC (hθ : 0 < σ.θ₂) : IsOpen σ.domTwoC := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hd1 : ContinuousAt σ.discOne z := (σ.contDiffAt_discOne hz.1).continuousAt
  have hd2 : ContinuousAt σ.discTwo z :=
    (contDiffAt_coneDisc (σ.vertexTwo_im_pos hθ) hz.1).continuousAt
  have hrot : ContinuousAt (fun u => (σ.rotOne u).re) z :=
    continuous_re.continuousAt.comp (continuousAt_const.mul hd1)
  have hc1 : ContinuousAt (fun u => ‖σ.discOne u‖ + (σ.rotOne u).re) z := hd1.norm.add hrot
  have hc2 : ContinuousAt (fun u => ‖σ.discTwo u‖ + (σ.tCone - (σ.rotOne u).re) /
      (1 - σ.tCone * (σ.rotOne u).re)) z :=
    hd2.norm.add ((continuousAt_const.sub hrot).div (continuousAt_const.sub
      (continuousAt_const.mul hrot)) (σ.one_sub_t_rot_pos hθ hz.1).ne')
  filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hz.1,
    continuousAt_const.eventually_lt hc1 hz.2.1, continuousAt_const.eventually_lt hc2 hz.2.2]
    with w hw h1 h2
  exact ⟨hw, h1, h2⟩

/-! ### The wall-0 bridge -/

def wallZeroC (z : ℂ) : ℝ := -(σ.discTwo z).im

def cofZeroC (z : ℂ) : ℝ :=
  2 * σ.vertexTwo.im * (1 - ‖σ.discTwo z‖ ^ 2) /
    ((‖σ.discTwo z‖ + (σ.discTwo z).re) * (1 - ‖σ.discTwo z‖) ^ 2 *
      ((1 - (σ.discTwo z).re) ^ 2 + (σ.discTwo z).im ^ 2))

def domZeroC : Set ℂ := {z | 0 < z.im ∧ 0 < ‖σ.discTwo z‖ + (σ.discTwo z).re}

def bridgeZeroC (z : ℂ) : ℂ :=
  outerBridge σ.constK (3 / 2) z.im (σ.etaTwoC z) (σ.wallZeroC z) (σ.cofZeroC z)

theorem etaTwoC_sub_im (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domZeroC) :
    σ.etaTwoC z - z.im = σ.wallZeroC z ^ 2 * σ.cofZeroC z := by
  rw [etaTwoC, coneHeight_sub_im (σ.vertexTwo_im_pos hθ) hz.1 hz.2, wallZeroC, cofZeroC, neg_sq,
    discTwo]
  ring

theorem cofZeroC_pos (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domZeroC) : 0 < σ.cofZeroC z := by
  have h1 := σ.norm_discTwo_lt_one hθ hz.1
  have h2 := σ.vertexTwo_im_pos hθ
  have h3 := hz.2
  have h4 : 0 < 1 - ‖σ.discTwo z‖ := by linarith
  have h5 : 0 < 1 - ‖σ.discTwo z‖ ^ 2 := by nlinarith [norm_nonneg (σ.discTwo z)]
  have h6 : 0 < (1 - (σ.discTwo z).re) ^ 2 + (σ.discTwo z).im ^ 2 := by
    have : (σ.discTwo z).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) h1
    have : 0 < (1 - (σ.discTwo z).re) ^ 2 := by nlinarith
    positivity
  unfold cofZeroC
  positivity

theorem norm_bridgeZeroC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domZeroC) :
    ‖σ.bridgeZeroC z‖ = 3 / 2 + coneProfile σ.constK z.im :=
  norm_outerBridge σ.constK_pos (Or.inl rfl) hz.1 (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1)
    (σ.cofZeroC_pos hθ hz) (σ.etaTwoC_sub_im hθ hz)

theorem norm_bridgeZeroC_sub (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domZeroC) :
    ‖σ.bridgeZeroC z - 3 / 2‖ = coneProfile σ.constK (σ.etaTwoC z) := by
  have h := norm_outerBridge_sub σ.constK_pos (Or.inl rfl) hz.1
    (coneHeight_pos (σ.vertexTwo_im_pos hθ) hz.1) (σ.cofZeroC_pos hθ hz) (σ.etaTwoC_sub_im hθ hz)
  rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by norm_num] at h
  exact h

theorem bridgeZeroC_re_pos {z : ℂ} (hz : 0 < z.im) : 0 < (σ.bridgeZeroC z).re := by
  have := outerBridge_re_mul_pos σ.constK_pos (Or.inl rfl) hz (η := σ.etaTwoC z)
    (w := σ.wallZeroC z) (q := σ.cofZeroC z)
  rw [bridgeZeroC]
  linarith

theorem discTwo_refl_zero (z : ℂ) : σ.discTwo (σ.refl 0 z) = conj (σ.discTwo z) :=
  σ.coneDisc_vertexTwo_refl_zero z

theorem bridgeZeroC_refl_zero (z : ℂ) : σ.bridgeZeroC (σ.refl 0 z) = conj (σ.bridgeZeroC z) := by
  have e0 : (σ.refl 0 z).im = z.im := by simp [refl]
  have e1 : σ.etaTwoC (σ.refl 0 z) = σ.etaTwoC z := by
    simp only [etaTwoC, coneHeight]
    rw [← discTwo, ← discTwo, σ.discTwo_refl_zero, Complex.norm_conj]
  have e2 : σ.wallZeroC (σ.refl 0 z) = -σ.wallZeroC z := by
    simp [wallZeroC, σ.discTwo_refl_zero]
  have e3 : σ.cofZeroC (σ.refl 0 z) = σ.cofZeroC z := by
    simp only [cofZeroC, σ.discTwo_refl_zero, Complex.norm_conj, conj_re, conj_im, neg_sq]
  rw [bridgeZeroC, bridgeZeroC, e0, e1, e2, e3, outerBridge_neg]

/-! ### Smoothness -/

theorem rotOne_vertexTwo (hθ : 0 < σ.θ₂) : σ.rotOne σ.vertexTwo = σ.tCone := by
  rw [rotOne, discOne, σ.coneDisc_vertexOne_vertexTwo hθ, mul_left_comm, ← Complex.exp_add]
  rw [show -((σ.θ₁ : ℂ) * I) + (σ.θ₁ : ℂ) * I = 0 by ring, Complex.exp_zero, mul_one]
  rfl

theorem ne_vertexTwo_of_domTwoC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    z ≠ σ.vertexTwo := by
  rintro rfl
  have h := hz.2.2
  rw [σ.rotOne_vertexTwo hθ, discTwo, coneDisc_self, norm_zero, ofReal_re, sub_self,
    zero_div, add_zero] at h
  exact lt_irrefl _ h

theorem discOne_ne_zero_of_domTwoC {z : ℂ} (hz : z ∈ σ.domTwoC) : σ.discOne z ≠ 0 := by
  intro h
  have := hz.2.1
  rw [rotOne, h, mul_zero, zero_re, norm_zero, add_zero] at this
  exact lt_irrefl _ this

theorem contDiffAt_cofTwoC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ σ.cofTwoC z := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have hd1 := σ.contDiffAt_discOne hz.1
  have hd2 : ContDiffAt ℝ ∞ σ.discTwo z :=
    (contDiffAt_coneDisc hv2 hz.1).restrict_scalars ℝ
  have hn1 : ContDiffAt ℝ ∞ (fun u => ‖σ.discOne u‖) z :=
    hd1.norm ℝ (σ.discOne_ne_zero_of_domTwoC hz)
  have hn2 : ContDiffAt ℝ ∞ (fun u => ‖σ.discTwo u‖) z :=
    hd2.norm ℝ (coneDisc_ne_zero hv2 hz.1 (σ.ne_vertexTwo_of_domTwoC hθ hz))
  have hrot : ContDiffAt ℝ ∞ σ.rotOne z := contDiffAt_const.mul hd1
  have hX : ContDiffAt ℝ ∞ (fun u => (σ.rotOne u).re) z := reCLM.contDiff.contDiffAt.comp z hrot
  have hY : ContDiffAt ℝ ∞ (fun u => (σ.rotOne u).im) z := imCLM.contDiff.contDiffAt.comp z hrot
  have hr1 := σ.norm_discOne_lt_one hz.1
  have hμ1 := σ.norm_discTwo_lt_one hθ hz.1
  have ht := σ.tCone_lt_one hθ
  have hd := σ.one_sub_t_rot_pos hθ hz.1
  have hD : 0 < (1 - σ.tCone * (σ.rotOne z).re) ^ 2 + σ.tCone ^ 2 * (σ.rotOne z).im ^ 2 := by
    positivity
  have hμ₀ : ContDiffAt ℝ ∞ (fun u => (σ.tCone - (σ.rotOne u).re) /
      (1 - σ.tCone * (σ.rotOne u).re)) z :=
    (contDiffAt_const.sub hX).div (contDiffAt_const.sub (contDiffAt_const.mul hX)) hd.ne'
  have hden1 : (1 - σ.tCone * (σ.rotOne z).re) * ((1 - σ.tCone * (σ.rotOne z).re) ^ 2 +
      σ.tCone ^ 2 * (σ.rotOne z).im ^ 2) * (‖σ.discTwo z‖ +
        (σ.tCone - (σ.rotOne z).re) / (1 - σ.tCone * (σ.rotOne z).re)) ≠ 0 :=
    (mul_pos (mul_pos hd hD) hz.2.2).ne'
  have hden2 : (1 - ‖σ.discOne z‖) * (1 - ‖σ.discTwo z‖) ≠ 0 :=
    (mul_pos (by linarith) (by linarith)).ne'
  have hB : ContDiffAt ℝ ∞ (fun u => (1 - σ.tCone * ‖σ.discTwo u‖) /
      (‖σ.discOne u‖ + (σ.rotOne u).re) +
      (1 - σ.tCone ^ 2) * (1 - 2 * σ.tCone * (σ.rotOne u).re + σ.tCone ^ 2) /
        ((1 - σ.tCone * (σ.rotOne u).re) * ((1 - σ.tCone * (σ.rotOne u).re) ^ 2 +
          σ.tCone ^ 2 * (σ.rotOne u).im ^ 2) * (‖σ.discTwo u‖ +
            (σ.tCone - (σ.rotOne u).re) / (1 - σ.tCone * (σ.rotOne u).re)))) z := by
    refine ((contDiffAt_const.sub (contDiffAt_const.mul hn2)).div (hn1.add hX) hz.2.1.ne').add ?_
    refine (contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_const.mul hX) |>.add
      contDiffAt_const)).div ?_ hden1
    exact ((contDiffAt_const.sub (contDiffAt_const.mul hX)).mul
      (((contDiffAt_const.sub (contDiffAt_const.mul hX)).pow 2).add
        (contDiffAt_const.mul (hY.pow 2)))).mul (hn2.add hμ₀)
  unfold cofTwoC
  exact contDiffAt_const.mul (hB.div ((contDiffAt_const.sub hn1).mul (contDiffAt_const.sub hn2))
    hden2)

theorem contDiffAt_bridgeTwoC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domTwoC) :
    ContDiffAt ℝ ∞ σ.bridgeTwoC z := by
  have hv1 := σ.vertexOne_im_pos
  have hv2 := σ.vertexTwo_im_pos hθ
  have hzv1 : z ≠ σ.vertexOne := fun h => σ.discOne_ne_zero_of_domTwoC hz (by
    rw [h, discOne, coneDisc_self])
  have h2 : ContDiffAt ℝ ∞ σ.etaTwoC z :=
    contDiffAt_coneHeight hv2 hz.1 (σ.ne_vertexTwo_of_domTwoC hθ hz)
  have h1 : ContDiffAt ℝ ∞ σ.etaOne z := contDiffAt_coneHeight hv1 hz.1 hzv1
  exact contDiffAt_innerBridge σ.constK_pos h2 h1 (σ.contDiffAt_wallTwo hz.1)
    (σ.contDiffAt_cofTwoC hθ hz) (coneHeight_pos hv2 hz.1) (σ.etaOne_pos hz.1)
    (σ.cofTwoC_pos hθ hz)

theorem contDiffAt_bridgeZeroC (hθ : 0 < σ.θ₂) {z : ℂ} (hz : z ∈ σ.domZeroC) :
    ContDiffAt ℝ ∞ σ.bridgeZeroC z := by
  have hv2 := σ.vertexTwo_im_pos hθ
  have hd2 : ContDiffAt ℝ ∞ σ.discTwo z :=
    (contDiffAt_coneDisc hv2 hz.1).restrict_scalars ℝ
  have hne : σ.discTwo z ≠ 0 := by
    intro h
    have := hz.2
    rw [h, norm_zero, zero_re, add_zero] at this
    exact lt_irrefl _ this
  have hzv2 : z ≠ σ.vertexTwo := fun h => hne (by rw [h, discTwo, coneDisc_self])
  have hn : ContDiffAt ℝ ∞ (fun u => ‖σ.discTwo u‖) z := hd2.norm ℝ hne
  have hre : ContDiffAt ℝ ∞ (fun u => (σ.discTwo u).re) z := reCLM.contDiff.contDiffAt.comp z hd2
  have him : ContDiffAt ℝ ∞ (fun u => (σ.discTwo u).im) z := imCLM.contDiff.contDiffAt.comp z hd2
  have h1 := σ.norm_discTwo_lt_one hθ hz.1
  have h6 : 0 < (1 - (σ.discTwo z).re) ^ 2 + (σ.discTwo z).im ^ 2 := by
    have : (σ.discTwo z).re < 1 := lt_of_le_of_lt (Complex.re_le_norm _) h1
    have : 0 < (1 - (σ.discTwo z).re) ^ 2 := by nlinarith
    positivity
  have hden : (‖σ.discTwo z‖ + (σ.discTwo z).re) * (1 - ‖σ.discTwo z‖) ^ 2 *
      ((1 - (σ.discTwo z).re) ^ 2 + (σ.discTwo z).im ^ 2) ≠ 0 :=
    (mul_pos (mul_pos hz.2 (by nlinarith)) h6).ne'
  have hq : ContDiffAt ℝ ∞ σ.cofZeroC z := by
    unfold cofZeroC
    exact (contDiffAt_const.mul (contDiffAt_const.sub (hn.pow 2))).div
      (((hn.add hre).mul ((contDiffAt_const.sub hn).pow 2)).mul
        (((contDiffAt_const.sub hre).pow 2).add (him.pow 2))) hden
  exact contDiffAt_outerBridge σ.constK_pos (Or.inl rfl) imCLM.contDiff.contDiffAt
    (contDiffAt_coneHeight hv2 hz.1 hzv2) (him.neg : ContDiffAt ℝ ∞ σ.wallZeroC z) hq hz.1
    (coneHeight_pos hv2 hz.1) (σ.cofZeroC_pos hθ hz)

end ConeShape

end GC.Seifert
