import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometrySeam

/-!
# The fibre phase on the base of a two-cone block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.2,
replaced after review 21 §5 by a closed formula on the base). For a real centre `c`,
`phaseArg c u = arg(-i (u - c)) + π/2` is the angle of `u - c` with values in `(-π/2, 3π/2]`;
it is smooth off the downward ray `{Re u = c, Im u ≤ 0}` (`contDiffAt_phaseArg`) and satisfies the
exact reflection rules `phaseArg c (conj u) = -phaseArg c u` for `Re u > c` and
`= 2π - phaseArg c u` for `Re u < c` (`phaseArg_conj_of_lt`, `phaseArg_conj_of_gt`). The base
phase of the block with cones `(p₁, q₁)` at `3/2` and `(p₂, q₂)` at `-3/2` is
`basePhase k₁ k₂ u = exp(-i (k₁ phaseArg (3/2) u + k₂ phaseArg (-3/2) u))` with `kᵢ = qᵢ/pᵢ`.
Its reflection rules on the three real segments `(3/2, 3)`, `(-3/2, 3/2)`, `(-3, -3/2)` carry the
fibre shifts `c₁ = 0`, `c₂ = k₁`, `c₀ = k₁ + k₂` of the design (`basePhase_conj_of_gt`,
`basePhase_conj_of_mid`, `basePhase_conj_of_lt`), with no partition of unity: the circle-valued
phase is single valued on the base minus the two downward rays. At a cone apex
`u = c + w^p/2` with `p arg w ∈ (-π/2, 3π/2]`, `phaseArg c u = p arg w` (`phaseArg_apex`), so the
phase is `unit(w)^(-q)` times the smooth factor coming from the other cone.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

namespace GC.Seifert

theorem contDiffAt_arg_slit {z : ℂ} (hz : z ∈ slitPlane) : ContDiffAt ℝ ∞ arg z := by
  have hlog : ContDiffAt ℝ ∞ log z := (contDiffAt_log hz).restrict_scalars ℝ
  have him : ContDiffAt ℝ ∞ (fun w : ℂ => (log w).im) z :=
    (Complex.imCLM.contDiff.contDiffAt).comp z hlog
  refine him.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  exact (log_im w).symm

def phaseArg (c : ℝ) (u : ℂ) : ℝ := arg (-I * (u - c)) + Real.pi / 2

def phaseDomain (c : ℝ) : Set ℂ := {u | -I * (u - c) ∈ slitPlane}

theorem mem_phaseDomain_iff {c : ℝ} {u : ℂ} : u ∈ phaseDomain c ↔ 0 < u.im ∨ u.re ≠ c := by
  change -I * (u - c) ∈ slitPlane ↔ _
  rw [mem_slitPlane_iff]
  simp only [mul_re, neg_re, I_re, sub_re, ofReal_re, zero_mul, neg_im, I_im, one_mul,
    sub_im, ofReal_im, sub_zero, zero_sub, mul_im, zero_add, neg_mul, ne_eq, neg_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; intro he; apply h; linarith
  · rintro (h | h)
    · left; linarith
    · right; intro he; apply h; linarith

theorem isOpen_phaseDomain (c : ℝ) : IsOpen (phaseDomain c) :=
  isOpen_slitPlane.preimage (continuous_const.mul (continuous_id.sub continuous_const))

theorem mem_phaseDomain_of_re_ne {c : ℝ} {u : ℂ} (h : u.re ≠ c) : u ∈ phaseDomain c :=
  mem_phaseDomain_iff.2 (Or.inr h)

theorem contDiffAt_phaseArg {c : ℝ} {u : ℂ} (hu : u ∈ phaseDomain c) :
    ContDiffAt ℝ ∞ (phaseArg c) u := by
  have h1 : ContDiffAt ℝ ∞ (fun v : ℂ => -I * (v - c)) u :=
    (contDiff_const.mul (contDiff_id.sub contDiff_const)).contDiffAt
  exact ((contDiffAt_arg_slit hu).comp u h1).add contDiffAt_const

theorem phaseArg_conj_of_lt {c : ℝ} {u : ℂ} (h : c < u.re) :
    phaseArg c (conj u) = -phaseArg c u := by
  unfold phaseArg
  have hw : 0 < (I * (u - c)).im := by simp; linarith
  have e1 : -I * (conj u - c) = conj (I * (u - c)) := by
    simp [map_sub, map_mul, conj_I, conj_ofReal]
  have e2 : -I * (u - c) = -(I * (u - c)) := by ring
  rw [e1, e2, arg_neg_eq_arg_sub_pi_of_im_pos hw, arg_conj,
    ite_eq_right (fun h => by linarith [arg_lt_pi_iff.mpr (Or.inr hw.ne')])]
  ring

theorem phaseArg_conj_of_gt {c : ℝ} {u : ℂ} (h : u.re < c) :
    phaseArg c (conj u) = 2 * Real.pi - phaseArg c u := by
  unfold phaseArg
  have hw : (I * (u - c)).im < 0 := by simp; linarith
  have e1 : -I * (conj u - c) = conj (I * (u - c)) := by
    simp [map_sub, map_mul, conj_I, conj_ofReal]
  have e2 : -I * (u - c) = -(I * (u - c)) := by ring
  rw [e1, e2, arg_neg_eq_arg_add_pi_of_im_neg hw, arg_conj,
    ite_eq_right (fun h => by linarith [arg_lt_pi_iff.mpr (Or.inr hw.ne)])]
  ring

theorem phaseArg_apex (c : ℝ) {p : ℕ} {w : ℂ} (hw : w ≠ 0)
    (h1 : -(Real.pi / 2) < p * arg w) (h2 : p * arg w ≤ 3 * Real.pi / 2) :
    phaseArg c (c + w ^ p / 2) = p * arg w := by
  unfold phaseArg
  have hw' := norm_mul_exp_arg_mul_I w
  have hr : 0 < ‖w‖ ^ p / 2 := by
    have := norm_pos_iff.mpr hw
    positivity
  have hpow : w ^ p = ((‖w‖ ^ p : ℝ) : ℂ) * exp (((p * arg w : ℝ) : ℂ) * I) := by
    conv_lhs => rw [← hw']
    rw [mul_pow, ← exp_nat_mul]
    push_cast
    ring_nf
  have hmI : exp (((-(Real.pi / 2) : ℝ) : ℂ) * I) = -I := by
    rw [exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  have e : -I * (↑c + w ^ p / 2 - ↑c) =
      ((‖w‖ ^ p / 2 : ℝ) : ℂ) * exp (((p * arg w - Real.pi / 2 : ℝ) : ℂ) * I) := by
    rw [add_sub_cancel_left, hpow, show ((p * arg w - Real.pi / 2 : ℝ) : ℂ) * I =
      ((p * arg w : ℝ) : ℂ) * I + ((-(Real.pi / 2) : ℝ) : ℂ) * I by push_cast; ring, exp_add, hmI]
    push_cast
    ring
  rw [e, arg_real_mul _ hr, exp_mul_I, arg_cos_add_sin_mul_I ⟨by linarith, by linarith⟩]
  ring

def basePhase (k₁ k₂ : ℝ) (u : ℂ) : Circle :=
  Circle.exp (-(k₁ * phaseArg (3 / 2) u + k₂ * phaseArg (-(3 / 2)) u))

theorem contMDiffAt_basePhase (k₁ k₂ : ℝ) {u : ℂ} (h₁ : u ∈ phaseDomain (3 / 2))
    (h₂ : u ∈ phaseDomain (-(3 / 2))) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓡 1) ∞ (basePhase k₁ k₂) u := by
  have h : ContDiffAt ℝ ∞
      (fun v : ℂ => -(k₁ * phaseArg (3 / 2) v + k₂ * phaseArg (-(3 / 2)) v)) u :=
    ((contDiffAt_const.mul (contDiffAt_phaseArg h₁)).add
      (contDiffAt_const.mul (contDiffAt_phaseArg h₂))).neg
  exact contMDiff_circleExp.contMDiffAt.comp u h.contMDiffAt

theorem basePhase_conj_of_gt (k₁ k₂ : ℝ) {u : ℂ} (h : 3 / 2 < u.re) :
    basePhase k₁ k₂ (conj u) = (basePhase k₁ k₂ u)⁻¹ := by
  unfold basePhase
  rw [phaseArg_conj_of_lt h, phaseArg_conj_of_lt (by linarith : (-(3 / 2) : ℝ) < u.re),
    ← Circle.exp_neg]
  congr 1
  ring

theorem basePhase_conj_of_mid (k₁ k₂ : ℝ) {u : ℂ} (h1 : -(3 / 2) < u.re) (h2 : u.re < 3 / 2) :
    basePhase k₁ k₂ (conj u) =
      Circle.exp (-(2 * Real.pi * k₁)) * (basePhase k₁ k₂ u)⁻¹ := by
  unfold basePhase
  rw [phaseArg_conj_of_gt h2, phaseArg_conj_of_lt h1, ← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

theorem basePhase_conj_of_lt (k₁ k₂ : ℝ) {u : ℂ} (h : u.re < -(3 / 2)) :
    basePhase k₁ k₂ (conj u) =
      Circle.exp (-(2 * Real.pi * (k₁ + k₂))) * (basePhase k₁ k₂ u)⁻¹ := by
  unfold basePhase
  rw [phaseArg_conj_of_gt (by linarith : u.re < (3 / 2 : ℝ)), phaseArg_conj_of_gt h,
    ← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

end GC.Seifert
