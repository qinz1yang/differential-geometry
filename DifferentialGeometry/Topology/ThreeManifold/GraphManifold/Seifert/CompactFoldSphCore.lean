import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidCore

/-!
# The spherical compact fold with its core replaced

Lane CF-S3w (for CF-S2), tier 3, curvature `+1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §6, review 23 §6). Template: `CompactFoldEuclidCore`.
Every declaration carries `sph`.

**Image bounds (layout-free).** Every branch of `sphPreFold` is `c + S e^{iΘ}` with `c` real,
`0 ≤ S`, `|c| + S < 7/2` and `Θ ∈ [0, π]`, strictly `0 < S`, `Θ ∈ (0, π)` where all three side
functions are positive: the disc angles lie in the sectors of the vertices, and the bridge angles
are `halfArg`/`negHalfArg` of points of the upper half plane at the distance given by the modulus.
Hence `‖sphPreFold‖ < 7/2` and `0 ≤ Im` on `T \ {0}`, `0 < Im` on the open triangle
(`norm_sphPreFold_lt`, `im_sphPreFold_nonneg`, `im_sphPreFold_pos`); near `v₃ = 0` the fold is the
outer germ (`sphPreFold_eq_outerGerm_of_mem`).

**The chart of the core.** The core is a Euclidean disc in `ζ = rotTwo z` (CF-S2's `sphCoreCenter`,
`sphCoreRadius`, `sphCoreMargin`). `sphChartTwo` is the inverse Möbius map (`rotTwo_sphChartTwo`,
`sphChartTwo_rotTwo`, both with positive Jacobian). In `ζ` the triangle is the convex region
`sphChartRegion = {Im ζ ≥ 0, f₀ ≥ 0, f₁ ≥ 0}`: `f₀ = Im(e^{iθ₂} ζ̄)` is linear and `f₁` (wall 1, a
disc in this chart) is concave with `f₁(segment) = interpolation + sin θ₁ t₁₂ s(1-s)|b - a|²`
(`sphChartSideOne_segment`); `mem_triangle_sphChartTwo`, `chartRegion_of_mem_triangle_sph`, and
`wallSide_pos_sphChartTwo` (strict inequalities in `ζ` ⇒ open triangle, for the hypothesis `hin`).

**Core replacement** (`exists_sphFoldCore_of`, `exists_sphFoldCore`). K16f's
`exists_core_replacement` is applied to `E' = sphPreFold ∘ sphChartTwo` on the `ζ`-annulus; `hout`
uses `E'(coreOut) ∪ ray`, `coreOut = {ζ ∈ region, ζ ≠ rotTwo 0, ‖ζ - c‖ > r}` being preconnected by
segments towards the centre (convexity of the region), and a point of `coreOut` close to
`rotTwo 0 = v₃` where `sphPreFold` is the outer germ of modulus close to `7/2`. The fold is
`Q ∘ rotTwo` on the core and `sphPreFold` elsewhere; the set `{r < ‖rotTwo z - c‖}` is open also at
the pole of `rotTwo` (`isOpen_rotTwo_far_sph`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem halfArg_mem_Icc_sph {S R J : ℝ} (hSR : 0 ≤ S + R) (hJ : 0 ≤ J) :
    0 ≤ halfArg S R J ∧ halfArg S R J ≤ Real.pi := by
  unfold halfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S + R))
  have h2 : 0 ≤ Real.arctan (J / (S + R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR)
  constructor <;> linarith

theorem negHalfArg_mem_Icc_sph {S R J : ℝ} (hSR : 0 ≤ S - R) (hJ : 0 ≤ J) :
    0 ≤ negHalfArg S R J ∧ negHalfArg S R J ≤ Real.pi := by
  unfold negHalfArg
  have h1 := Real.arctan_lt_pi_div_two (J / (S - R))
  have h2 : 0 ≤ Real.arctan (J / (S - R)) := Real.arctan_nonneg.2 (div_nonneg hJ hSR)
  constructor <;> linarith

theorem halfArg_mem_Ioo_sph {S R J : ℝ} (hSR : 0 < S + R) (hJ : 0 < J) :
    0 < halfArg S R J ∧ halfArg S R J < Real.pi :=
  ⟨halfArg_pos hSR hJ, (halfArg_mem S R J).2⟩

theorem negHalfArg_mem_Ioo_sph {S R J : ℝ} (hSR : 0 < S - R) (hJ : 0 < J) :
    0 < negHalfArg S R J ∧ negHalfArg S R J < Real.pi :=
  ⟨(negHalfArg_mem (S := S) (R := R) (J := J)).1, negHalfArg_lt_pi hSR hJ⟩

theorem combo_mem_Icc_sph {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ Real.pi) (hy : 0 ≤ y ∧ y ≤ Real.pi) :
    0 ≤ (1 - τ) * x + τ * y ∧ (1 - τ) * x + τ * y ≤ Real.pi := by
  have a := mul_nonneg (sub_nonneg.2 h1) hx.1
  have b := mul_nonneg h0 hy.1
  have c := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hx.2)
  have d := mul_nonneg h0 (sub_nonneg.2 hy.2)
  constructor <;> nlinarith

theorem combo_mem_Icc_sph' {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ Real.pi) (hy : 0 ≤ y ∧ y ≤ Real.pi) :
    0 ≤ τ * x + (1 - τ) * y ∧ τ * x + (1 - τ) * y ≤ Real.pi := by
  have e := combo_mem_Icc_sph (τ := 1 - τ) (by linarith) (by linarith) hx hy
  rwa [sub_sub_cancel] at e

theorem combo_mem_Ioo_sph' {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hx : 0 < x ∧ x < Real.pi) (hy : 0 < y ∧ y < Real.pi) :
    0 < τ * x + (1 - τ) * y ∧ τ * x + (1 - τ) * y < Real.pi := by
  have e := angle_open_combo (τ := 1 - τ) (by linarith) (by linarith) hx hy
  rwa [sub_sub_cancel] at e

theorem im_polar_nonneg_sph {c S Θ : ℝ} (hS : 0 ≤ S) (hΘ : 0 ≤ Θ ∧ Θ ≤ Real.pi) :
    0 ≤ ((c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)).im := by
  rw [im_real_add_polar]
  exact mul_nonneg hS (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)

theorem im_polar_pos_sph {c S Θ : ℝ} (hS : 0 < S) (hΘ : 0 < Θ ∧ Θ < Real.pi) :
    0 < ((c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)).im := by
  rw [im_real_add_polar]
  exact mul_pos hS (Real.sin_pos_of_pos_of_lt_pi hΘ.1 hΘ.2)

theorem norm_polar_le_sph (c : ℝ) {S : ℝ} (Θ : ℝ) (hS : 0 ≤ S) :
    ‖(c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)‖ ≤ |c| + S := by
  calc ‖(c : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)‖
      ≤ ‖(c : ℂ)‖ + ‖(S : ℂ) * exp ((Θ : ℂ) * I)‖ := norm_add_le _ _
    _ = |c| + S := by
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hS, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem mul_mem_Icc_sph {p : ℕ} {θ ψ : ℝ} (hθ : θ * p = Real.pi) (h0 : 0 ≤ ψ) (h1 : ψ ≤ θ) :
    0 ≤ (p : ℝ) * ψ ∧ (p : ℝ) * ψ ≤ Real.pi := by
  refine ⟨by positivity, ?_⟩
  rw [← hθ, mul_comm θ]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg p)

theorem mul_mem_Ioo_sph {p : ℕ} (hp : 1 ≤ p) {θ ψ : ℝ} (hθ : θ * p = Real.pi) (h0 : 0 < ψ)
    (h1 : ψ < θ) : 0 < (p : ℝ) * ψ ∧ (p : ℝ) * ψ < Real.pi := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨by positivity, ?_⟩
  rw [← hθ, mul_comm θ]
  exact mul_lt_mul_of_pos_left h1 hp'

theorem re_add_nonneg_sph {w : ℂ} {S : ℝ} (h : ‖w‖ = S) : 0 ≤ S + w.re ∧ 0 ≤ S - w.re := by
  have := Complex.abs_re_le_norm w
  rw [h] at this
  constructor <;> linarith [le_abs_self w.re, neg_abs_le w.re]

theorem re_add_pos_sph {w : ℂ} {S : ℝ} (h : ‖w‖ = S) (hJ : w.im ≠ 0) :
    0 < S + w.re ∧ 0 < S - w.re := by
  have := Complex.abs_re_lt_norm.2 hJ
  rw [h] at this
  constructor <;> linarith [le_abs_self w.re, neg_abs_le w.re]

theorem sphCanonF_lt_one {τ x : ℝ} (hτ0 : 0 < τ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    sphCanonF τ x < 1 := by
  have hd : 0 < 1 + x * τ := by nlinarith
  rw [sphCanonF, div_lt_one hd]
  nlinarith

theorem sphInnerRadial_lt_two {p : ℕ} {a b τ x : ℝ} (hτ0 : 0 < τ) (hx0 : 0 ≤ x) (hx : x ≤ 1) :
    sphInnerRadial p a b τ x < 2 := by
  have hs0 := coneStep_nonneg a b x
  have hs1 := coneStep_le_one a b x
  have hF := sphCanonF_lt_one hτ0 hx0 hx
  have hxp : x ^ p ≤ 1 := pow_le_one₀ hx0 hx
  have hA : 0 < 2 - x ^ p / 2 := by linarith
  have hB : 0 < 2 - (3 / 2 + compactProfileSlope * sphCanonF τ x) := by
    unfold compactProfileSlope
    linarith
  have := convex_comb_pos hs0 hs1 hA hB
  unfold sphInnerRadial
  nlinarith

theorem sphOuterRadial_lt_sph {p : ℕ} {a b τ x : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hx : 0 < x) :
    sphOuterRadial p a b τ x < 7 / 2 := by
  have hs0 := coneStep_nonneg a b x
  have hs1 := coneStep_le_one a b x
  have hF := sphCanonF_ge hτ0 hτ1 hx.le
  have hA : 0 < 7 / 2 - (7 / 2 - x ^ p / 2) := by
    have : 0 < x ^ p := by positivity
    linarith
  have hB : 0 < 7 / 2 - (3 - compactProfileSlope * sphCanonF τ x) := by
    unfold compactProfileSlope
    linarith
  have := convex_comb_pos hs0 hs1 hA hB
  unfold sphOuterRadial
  nlinarith

theorem re_sphMoeb_real_sph (s : ℝ) {w : ℂ} (h0 : 1 + (s : ℂ) * w ≠ 0) :
    (sphMoeb s w).re * Complex.normSq (1 + s * w) = w.re + s * ‖w‖ ^ 2 - s - s ^ 2 * w.re := by
  rw [sphMoeb, Complex.conj_ofReal]
  have hN : Complex.normSq (1 + (s : ℂ) * w) ≠ 0 := (Complex.normSq_pos.2 h0).ne'
  rw [Complex.div_re, add_mul, div_mul_cancel₀ _ hN, div_mul_cancel₀ _ hN,
    CompactShape.sq_norm_eq_sph]
  simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re,
    one_im]
  ring

theorem im_rot_sphMoeb_real_sph (θ t : ℝ) {ζ : ℂ} (h : 1 + (t : ℂ) * ζ ≠ 0) :
    (-(exp ((θ : ℂ) * I) * sphMoeb t ζ)).im * Complex.normSq (1 + t * ζ) =
      Real.sin θ * t * (1 - ‖ζ‖ ^ 2) - Real.sin θ * (1 - t ^ 2) * ζ.re -
        Real.cos θ * (1 + t ^ 2) * ζ.im := by
  have e1 := CompactShape.im_sphMoeb_real t ζ
  have e2 := re_sphMoeb_real_sph t h
  rw [neg_im, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  linear_combination (-Real.cos θ) * e1 - Real.sin θ * e2

theorem det_fderiv_comp_sph {f g : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    (fderiv ℝ (f ∘ g) x).det = (fderiv ℝ f (g x)).det * (fderiv ℝ g x).det := by
  rw [fderiv_comp x hf hg]
  change LinearMap.det ((fderiv ℝ f (g x) : ℂ →ₗ[ℝ] ℂ) ∘ₗ (fderiv ℝ g x : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp]

namespace CompactShape

variable {σ : CompactShape}

variable (σ) in
def sphChartTwo (ζ : ℂ) : ℂ := sphMoebInv σ.vertexTwo (-exp (-((σ.θ₂ : ℂ) * I)) * ζ)

variable (σ) in
def sphChartSideZero (ζ : ℂ) : ℝ := (exp ((σ.θ₂ : ℂ) * I) * conj ζ).im

variable (σ) in
def sphChartSideOne (ζ : ℂ) : ℝ :=
  Real.sin σ.θ₁ * σ.sphTOneTwo * (1 - ‖ζ‖ ^ 2) - Real.sin σ.θ₁ * (1 - σ.sphTOneTwo ^ 2) * ζ.re -
    Real.cos σ.θ₁ * (1 + σ.sphTOneTwo ^ 2) * ζ.im

variable (σ) in
def sphChartRegion : Set ℂ :=
  {ζ | 0 ≤ ζ.im ∧ 0 ≤ σ.sphChartSideZero ζ ∧ 0 ≤ σ.sphChartSideOne ζ}

theorem sphChartSideZero_segment (a b : ℂ) (s : ℝ) :
    σ.sphChartSideZero (a + (s : ℂ) * (b - a)) =
      (1 - s) * σ.sphChartSideZero a + s * σ.sphChartSideZero b := by
  simp only [sphChartSideZero]
  rw [im_exp_mul_conj_sph, im_exp_mul_conj_sph, im_exp_mul_conj_sph]
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, zero_mul,
    sub_zero, add_zero]
  ring

theorem sphChartSideOne_segment (a b : ℂ) (s : ℝ) :
    σ.sphChartSideOne (a + (s : ℂ) * (b - a)) =
      (1 - s) * σ.sphChartSideOne a + s * σ.sphChartSideOne b +
        Real.sin σ.θ₁ * σ.sphTOneTwo * (s * (1 - s)) * ‖b - a‖ ^ 2 := by
  simp only [sphChartSideOne, sq_norm_eq_sph, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, sub_re, sub_im, zero_mul, sub_zero, add_zero]
  ring

theorem im_segment_sph (a b : ℂ) (s : ℝ) :
    (a + (s : ℂ) * (b - a)).im = (1 - s) * a.im + s * b.im := by
  simp only [add_im, mul_im, ofReal_re, ofReal_im, sub_im, sub_re, zero_mul, add_zero]
  ring

omit σ in
theorem segment_nonneg_sph {s x y : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (1 - s) * x + s * y := by
  have := mul_nonneg (sub_nonneg.2 h1) hx
  have := mul_nonneg h0 hy
  linarith

theorem segment_mem_sphChartRegion (ht : 0 ≤ σ.sphTOneTwo) {a b : ℂ}
    (ha : a ∈ σ.sphChartRegion) (hb : b ∈ σ.sphChartRegion) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    a + (s : ℂ) * (b - a) ∈ σ.sphChartRegion := by
  refine ⟨?_, ?_, ?_⟩
  · rw [im_segment_sph]
    exact segment_nonneg_sph h0 h1 ha.1 hb.1
  · rw [sphChartSideZero_segment]
    exact segment_nonneg_sph h0 h1 ha.2.1 hb.2.1
  · rw [sphChartSideOne_segment]
    have := segment_nonneg_sph h0 h1 ha.2.2 hb.2.2
    have hk : 0 ≤ Real.sin σ.θ₁ * σ.sphTOneTwo * (s * (1 - s)) * ‖b - a‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg σ.sin_θ₁_pos_sph.le ht)
        (mul_nonneg h0 (sub_nonneg.2 h1))) (sq_nonneg _)
    linarith

theorem im_outerGerm_eq_sph {z : ℂ} (hψ : 0 < ‖z‖ + z.re) :
    (compactOuterGerm σ.p₃ z).im = (7 / 2 - ‖z‖ ^ σ.p₃ / 2) * Real.sin (σ.p₃ * discAngle z) := by
  rw [compactOuterGerm, EuclidShape.conj_div_norm_eq_exp hψ, ← Complex.exp_nat_mul,
    show (σ.p₃ : ℂ) * (((-discAngle z : ℝ) : ℂ) * I) = ((-(σ.p₃ * discAngle z) : ℝ) : ℂ) * I by
      push_cast; ring, neg_im, im_ofReal_mul, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sector_rotOne_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotOne z).im ∧ 0 ≤ -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im := by
  obtain ⟨s1, s2⟩ := sector_one_sph hs hz
  rw [im_exp_mul_conj_eq_neg_sph] at s2
  exact ⟨s1, s2⟩

theorem sector_rotTwo_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.rotTwo z).im ∧ 0 ≤ -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im := by
  obtain ⟨s1, s2⟩ := sector_two_sph hs hz
  rw [im_exp_mul_conj_eq_neg_sph] at s2
  exact ⟨s1, s2⟩

theorem sector_three_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ z.im ∧ 0 ≤ -(exp (-((σ.θ₃ : ℂ) * I)) * z).im :=
  ⟨im_nonneg_of_mem_sph hs hz, by
    rw [← wallSide_one_eq_neg_im_sph]
    exact ((mem_triangle_iff_sph hs).1 hz).2.1⟩

theorem sector_rotOne_pos_sph {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.rotOne z).im ∧ 0 < -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hv2' : 1 + conj σ.vertexTwo * z ≠ 0 := by rw [conj_vertexTwo_sph]; exact hv2
  constructor
  · have e := wallSide_one_eq_rotOne_sph hs z
    have : 0 < σ.wallSide 1 z * (1 + σ.sphTOneThree ^ 2) := mul_pos (hpos 1) (by positivity)
    rw [e] at this
    exact (mul_pos_iff_of_pos_right (Complex.normSq_pos.2 hv1)).1 this
  · have e := wallSide_two_eq_rotOne_sph hs hv1 hv2'
    rw [im_exp_mul_conj_eq_neg_sph] at e
    have hY : 0 < (σ.rotTwo z).im := by
      have := hpos 2
      rw [wallSide_two_eq_sph hs] at this
      exact (mul_pos_iff_of_pos_right (Complex.normSq_pos.2 hv2)).1 this
    have hN := lt_of_lt_of_le one_pos (one_le_normSq_rotTwo_sph hs hz)
    have : 0 < -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im *
        Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) := by
      rw [e]
      exact mul_pos (by positivity) hY
    exact (mul_pos_iff_of_pos_right hN).1 this

theorem sector_rotTwo_pos_sph {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.rotTwo z).im ∧ 0 < -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im := by
  have hN := Complex.normSq_pos.2 (one_add_vertexTwo_ne_sph hs hz)
  constructor
  · have := hpos 2
    rw [wallSide_two_eq_sph hs] at this
    exact (mul_pos_iff_of_pos_right hN).1 this
  · have e := wallSide_zero_eq_rotTwo_sph hs z
    rw [im_exp_mul_conj_eq_neg_sph] at e
    have : 0 < σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) := mul_pos (hpos 0) (by positivity)
    rw [e] at this
    exact (mul_pos_iff_of_pos_right hN).1 this

omit hs in
theorem sector_three_pos_sph {z : ℂ} (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < z.im ∧ 0 < -(exp (-((σ.θ₃ : ℂ) * I)) * z).im :=
  ⟨hpos 0, by rw [← wallSide_one_eq_neg_im_sph]; exact hpos 1⟩

omit hs in
theorem discAngle_mem_Icc_sph {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 2) (hw : w ≠ 0)
    (h : 0 ≤ w.im ∧ 0 ≤ -(exp (-((θ : ℂ) * I)) * w).im) :
    0 < ‖w‖ + w.re ∧ 0 ≤ discAngle w ∧ discAngle w ≤ θ := by
  have h2 := h.2
  rw [← im_exp_mul_conj_eq_neg_sph] at h2
  have hψ := pos_norm_add_re_sph hw (re_nonneg_of_sector_sph hθ0 hθ1 h.1 h2)
  obtain ⟨d0, d1, -⟩ := discAngle_sector hθ0 hθ1 hψ h.1 (by rwa [im_exp_mul_conj_eq_neg_sph] at h2)
  exact ⟨hψ, d0, d1⟩

omit hs in
theorem discAngle_mem_Ioo_sph {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 2)
    (h : 0 < w.im ∧ 0 < -(exp (-((θ : ℂ) * I)) * w).im) :
    0 < ‖w‖ + w.re ∧ 0 < discAngle w ∧ discAngle w < θ := by
  have hw : w ≠ 0 := fun h0 => by rw [h0, zero_im] at h; exact lt_irrefl 0 h.1
  obtain ⟨hψ, -, -⟩ := discAngle_mem_Icc_sph hθ0 hθ1 hw ⟨h.1.le, h.2.le⟩
  obtain ⟨-, -, d2, d3, -⟩ := discAngle_sector hθ0 hθ1 hψ h.1.le h.2.le
  exact ⟨hψ, d2 h.1, d3 h.2⟩

theorem ne_vertices_of_pos_sph {z : ℂ} (hpos : ∀ i, 0 < σ.wallSide i z) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have := hpos 0
    rw [wallSide_zero_zero_sph] at this
    exact lt_irrefl 0 this
  · have := hpos 2
    rw [wallSide_two_vertexOne_sph hs] at this
    exact lt_irrefl 0 this
  · have := hpos 2
    rw [wallSide_two_vertexTwo_sph hs] at this
    exact lt_irrefl 0 this

omit hs in
theorem norm_apex_le_sph {c : ℂ} (hc : ‖c‖ = 3 / 2) {w : ℂ} (hw : ‖w‖ ≤ 1) (p : ℕ) :
    ‖c + w ^ p / 2‖ ≤ 2 := by
  calc ‖c + w ^ p / 2‖ ≤ ‖c‖ + ‖w ^ p / 2‖ := norm_add_le _ _
    _ ≤ 2 := by
      rw [hc, norm_div, norm_pow, Complex.norm_two]
      have := pow_le_one₀ (norm_nonneg w) hw (n := p)
      linarith

omit hs in
theorem im_apex_eq_sph (c : ℝ) {w : ℂ} (hψ : 0 < ‖w‖ + w.re) (p : ℕ) :
    ((c : ℂ) + w ^ p / 2).im = ‖w‖ ^ p / 2 * Real.sin (p * discAngle w) := by
  rw [add_im, ofReal_im, zero_add, div_ofNat_im, EuclidShape.polar_pow hψ, im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]
  ring

omit hs in
theorem norm_three_halves_sph : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
  rw [show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]
  norm_num

theorem sphApexOne_bounds {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.sphApexOne z).im ∧ ‖σ.sphApexOne z‖ ≤ 2 := by
  refine ⟨?_, norm_apex_le_sph (norm_three_halves_sph) (norm_rotOne_le_one_sph hs hz) _⟩
  by_cases h0 : σ.rotOne z = 0
  · rw [sphApexOne, h0, zero_pow (by have := σ.two_le_p₁; omega)]
    simp
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₁_pos_sph σ.θ₁_le_sph h0
    (sector_rotOne_sph hs hz)
  rw [sphApexOne, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
    im_apex_eq_sph _ hψ]
  have hb := mul_mem_Icc_sph σ.θ₁_mul_sph d0 d1
  exact mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2)

theorem im_sphApexOne_pos {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.sphApexOne z).im := by
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₁_pos_sph σ.θ₁_le_sph
    (sector_rotOne_pos_sph hs hz hpos)
  have hne : σ.rotOne z ≠ 0 := EuclidShape.ne_zero_of_norm_add_re_pos hψ
  rw [sphApexOne, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
    im_apex_eq_sph _ hψ]
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₁; omega) σ.θ₁_mul_sph d0 d1
  have : 0 < ‖σ.rotOne z‖ := norm_pos_iff.2 hne
  exact mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2)

theorem sphApexTwo_bounds {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (σ.sphApexTwo z).im ∧ ‖σ.sphApexTwo z‖ ≤ 2 := by
  refine ⟨?_, norm_apex_le_sph (by rw [norm_neg]; exact norm_three_halves_sph)
    (norm_rotTwo_le_one_sph hs hz) _⟩
  by_cases h0 : σ.rotTwo z = 0
  · rw [sphApexTwo, h0, zero_pow (by have := σ.two_le_p₂; omega)]
    simp
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₂_pos_sph σ.θ₂_le_sph h0
    (sector_rotTwo_sph hs hz)
  rw [sphApexTwo, show (-(3 / 2) : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
    im_apex_eq_sph _ hψ]
  have hb := mul_mem_Icc_sph σ.θ₂_mul_sph d0 d1
  exact mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2)

theorem im_sphApexTwo_pos {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.sphApexTwo z).im := by
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₂_pos_sph σ.θ₂_le_sph
    (sector_rotTwo_pos_sph hs hz hpos)
  have hne : σ.rotTwo z ≠ 0 := EuclidShape.ne_zero_of_norm_add_re_pos hψ
  rw [sphApexTwo, show (-(3 / 2) : ℂ) = ((-(3 / 2) : ℝ) : ℂ) by push_cast; ring,
    im_apex_eq_sph _ hψ]
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₂; omega) σ.θ₂_mul_sph d0 d1
  have : 0 < ‖σ.rotTwo z‖ := norm_pos_iff.2 hne
  exact mul_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2)

theorem outerGerm_bounds_sph {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ (compactOuterGerm σ.p₃ z).im ∧ ‖compactOuterGerm σ.p₃ z‖ < 7 / 2 := by
  have hn := norm_le_one_of_mem_sph hs hz
  have hp1 : ‖z‖ ^ σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg z) hn
  have hp0 : 0 < ‖z‖ ^ σ.p₃ := pow_pos (norm_pos_iff.2 h0) _
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₃_pos_sph σ.θ₃_le_sph h0
    (sector_three_sph hs hz)
  have hb := mul_mem_Icc_sph σ.θ₃_mul_sph d0 d1
  refine ⟨?_, ?_⟩
  · rw [im_outerGerm_eq_sph hψ]
    exact mul_nonneg (by linarith) (Real.sin_nonneg_of_nonneg_of_le_pi hb.1 hb.2)
  · rw [norm_compactOuterGerm h0 (by linarith)]
    linarith

theorem im_outerGerm_pos_sph {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (compactOuterGerm σ.p₃ z).im := by
  have hn := norm_le_one_of_mem_sph hs hz
  obtain ⟨hψ, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₃_pos_sph σ.θ₃_le_sph
    (sector_three_pos_sph hpos)
  have hp1 : ‖z‖ ^ σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg z) hn
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₃; omega) σ.θ₃_mul_sph d0 d1
  rw [im_outerGerm_eq_sph hψ]
  exact mul_pos (by linarith) (Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2)

theorem im_sphBridgeOne_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.sphBridgeOne z).im := by
  rw [sphBridgeOne, twoCircle_im]
  exact div_nonneg (mul_nonneg ((mem_triangle_iff_sph hs).1 hz).2.1 (Real.sqrt_nonneg _))
    (by positivity)

theorem im_sphBridgeZero_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.sphBridgeZero z).im := by
  rw [sphBridgeZero, twoCircle_im]
  exact div_nonneg (mul_nonneg ((mem_triangle_iff_sph hs).1 hz).1 (Real.sqrt_nonneg _))
    (by positivity)

theorem im_sphBridgeTwo_nonneg {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ (σ.sphBridgeTwo z).im := by
  rw [sphBridgeTwo, twoCircle_im]
  exact div_nonneg (mul_nonneg (sector_two_sph hs hz).1 (Real.sqrt_nonneg _)) (by positivity)

theorem sphAngleCornerOne_mem_Icc (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.sphAngleCornerOne a b β β' z ∧ σ.sphAngleCornerOne a b β β' z ≤ Real.pi := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₁_pos_sph σ.θ₁_le_sph
    (rotOne_ne_zero_sph hs hv1 h1) (sector_rotOne_sph hs hz)
  have hb := mul_mem_Icc_sph σ.θ₁_mul_sph d0 d1
  have r1 := re_add_nonneg_sph (norm_sphBridgeOne hs (mem_sphDomOne hs hz h0 h1)).2
  have r2 := re_add_nonneg_sph (norm_sphBridgeTwo hs (mem_sphDomTwo hs hz h1 h2)).1
  simp only [sub_re, div_ofNat_re, Complex.re_ofNat] at r1 r2
  have a1 := halfArg_mem_Icc_sph r1.1 (im_sphBridgeOne_nonneg hs hz)
  have a2 := negHalfArg_mem_Icc_sph r2.2 (im_sphBridgeTwo_nonneg hs hz)
  unfold sphAngleCornerOne sphLensSwitch sphPsiOne sphAngleOneAtOne sphAngleTwoAtOne
  exact combo_mem_Icc_sph (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb
    (combo_mem_Icc_sph' (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a1 a2)

theorem sphAngleCornerOne_mem_Ioo (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < σ.sphAngleCornerOne a b β β' z ∧ σ.sphAngleCornerOne a b β β' z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := ne_vertices_of_pos_sph hs hpos
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₁_pos_sph σ.θ₁_le_sph
    (sector_rotOne_pos_sph hs hz hpos)
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₁; omega) σ.θ₁_mul_sph d0 d1
  have hd1 := mem_sphDomOne hs hz h0 h1
  have hd2 := mem_sphDomTwo hs hz h1 h2
  have j1 := im_sphBridgeOne_pos hs hd1 (hpos 1)
  have j2 := im_sphBridgeTwo_pos hs hd2 (sector_rotTwo_pos_sph hs hz hpos).1
  have r1 := re_add_pos_sph (norm_sphBridgeOne hs hd1).2
    (by simp only [sub_im, div_ofNat_im, Complex.im_ofNat, zero_div, sub_zero]; exact j1.ne')
  have r2 := re_add_pos_sph (norm_sphBridgeTwo hs hd2).1
    (by simp only [sub_im, div_ofNat_im, Complex.im_ofNat, zero_div, sub_zero]; exact j2.ne')
  simp only [sub_re, div_ofNat_re, Complex.re_ofNat] at r1 r2
  have a1 := halfArg_mem_Ioo_sph r1.1 j1
  have a2 := negHalfArg_mem_Ioo_sph r2.2 j2
  unfold sphAngleCornerOne sphLensSwitch sphPsiOne sphAngleOneAtOne sphAngleTwoAtOne
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb
    (combo_mem_Ioo_sph' (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a1 a2)

theorem sphAngleCornerTwo_mem_Icc (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.sphAngleCornerTwo a b β β' z ∧ σ.sphAngleCornerTwo a b β β' z ≤ Real.pi := by
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₂_pos_sph σ.θ₂_le_sph
    (rotTwo_ne_zero_sph hs hv2 h2) (sector_rotTwo_sph hs hz)
  have hb := mul_mem_Icc_sph σ.θ₂_mul_sph d0 d1
  have r2 := re_add_nonneg_sph (norm_sphBridgeTwo hs (mem_sphDomTwo hs hz h1 h2)).2
  have r0 := re_add_nonneg_sph (norm_sphBridgeZero hs (mem_sphDomZero hs hz h0 h2)).2
  simp only [add_re, div_ofNat_re, Complex.re_ofNat] at r2 r0
  have a2 := halfArg_mem_Icc_sph r2.1 (im_sphBridgeTwo_nonneg hs hz)
  have a0 := negHalfArg_mem_Icc_sph r0.2 (im_sphBridgeZero_nonneg hs hz)
  unfold sphAngleCornerTwo sphLensSwitch sphPsiTwo sphAngleTwoAtTwo sphAngleZeroAtTwo
  exact combo_mem_Icc_sph (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb
    (combo_mem_Icc_sph (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a2 a0)

theorem sphAngleCornerTwo_mem_Ioo (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < σ.sphAngleCornerTwo a b β β' z ∧ σ.sphAngleCornerTwo a b β β' z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := ne_vertices_of_pos_sph hs hpos
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₂_pos_sph σ.θ₂_le_sph
    (sector_rotTwo_pos_sph hs hz hpos)
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₂; omega) σ.θ₂_mul_sph d0 d1
  have hd2 := mem_sphDomTwo hs hz h1 h2
  have hd0 := mem_sphDomZero hs hz h0 h2
  have j2 := im_sphBridgeTwo_pos hs hd2 (sector_rotTwo_pos_sph hs hz hpos).1
  have j0 := im_sphBridgeZero_pos hs hd0 (hpos 0)
  have r2 := re_add_pos_sph (norm_sphBridgeTwo hs hd2).2
    (by simp only [add_im, div_ofNat_im, Complex.im_ofNat, zero_div, add_zero]; exact j2.ne')
  have r0 := re_add_pos_sph (norm_sphBridgeZero hs hd0).2
    (by simp only [add_im, div_ofNat_im, Complex.im_ofNat, zero_div, add_zero]; exact j0.ne')
  simp only [add_re, div_ofNat_re, Complex.re_ofNat] at r2 r0
  have a2 := halfArg_mem_Ioo_sph r2.1 j2
  have a0 := negHalfArg_mem_Ioo_sph r0.2 j0
  unfold sphAngleCornerTwo sphLensSwitch sphPsiTwo sphAngleTwoAtTwo sphAngleZeroAtTwo
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb
    (angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a2 a0)

theorem sphAngleCornerThree_mem_Icc (a b w δ : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ σ.sphAngleCornerThree a b w δ z ∧ σ.sphAngleCornerThree a b w δ z ≤ Real.pi := by
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Icc_sph σ.θ₃_pos_sph σ.θ₃_le_sph h0
    (sector_three_sph hs hz)
  have hb := mul_mem_Icc_sph σ.θ₃_mul_sph d0 d1
  have hb' : 0 ≤ Real.pi - σ.p₃ * discAngle z ∧ Real.pi - σ.p₃ * discAngle z ≤ Real.pi :=
    ⟨by linarith, by linarith⟩
  have r0 := re_add_nonneg_sph (norm_sphBridgeZero hs (mem_sphDomZero hs hz h0 h2)).1
  have r1 := re_add_nonneg_sph (norm_sphBridgeOne hs (mem_sphDomOne hs hz h0 h1)).1
  have a0 := negHalfArg_mem_Icc_sph r0.2 (im_sphBridgeZero_nonneg hs hz)
  have a1 := halfArg_mem_Icc_sph r1.1 (im_sphBridgeOne_nonneg hs hz)
  unfold sphAngleCornerThree sphNuThree sphAngleZeroAtThree sphAngleOneAtThree
  exact combo_mem_Icc_sph (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb'
    (combo_mem_Icc_sph (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a0 a1)

theorem sphAngleCornerThree_mem_Ioo (a b w δ : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < σ.sphAngleCornerThree a b w δ z ∧ σ.sphAngleCornerThree a b w δ z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := ne_vertices_of_pos_sph hs hpos
  obtain ⟨-, d0, d1⟩ := discAngle_mem_Ioo_sph σ.θ₃_pos_sph σ.θ₃_le_sph
    (sector_three_pos_sph hpos)
  have hb := mul_mem_Ioo_sph (by have := σ.two_le_p₃; omega) σ.θ₃_mul_sph d0 d1
  have hb' : 0 < Real.pi - σ.p₃ * discAngle z ∧ Real.pi - σ.p₃ * discAngle z < Real.pi :=
    ⟨by linarith, by linarith⟩
  have hd0 := mem_sphDomZero hs hz h0 h2
  have hd1 := mem_sphDomOne hs hz h0 h1
  have j0 := im_sphBridgeZero_pos hs hd0 (hpos 0)
  have j1 := im_sphBridgeOne_pos hs hd1 (hpos 1)
  have r0 := re_add_pos_sph (norm_sphBridgeZero hs hd0).1 j0.ne'
  have r1 := re_add_pos_sph (norm_sphBridgeOne hs hd1).1 j1.ne'
  have a0 := negHalfArg_mem_Ioo_sph r0.2 j0
  have a1 := halfArg_mem_Ioo_sph r1.1 j1
  unfold sphAngleCornerThree sphNuThree sphAngleZeroAtThree sphAngleOneAtThree
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) hb'
    (angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) a0 a1)

theorem sphCornerOne_bounds (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ (σ.sphCornerOne a b β β' z).im ∧ ‖σ.sphCornerOne a b β β' z‖ < 7 / 2 := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hS2 := sphInnerRadial_lt_two (p := σ.p₁) (a := a) (b := b) (sphTau_pos hs 0)
    (norm_nonneg _) (norm_rotOne_le_one_sph hs hz)
  have hS0 := sphInnerRadial_pos (p := σ.p₁) (a := a) (b := b) (sphTau_pos hs 0).le
    (sphTau_lt_one hs 0) (norm_pos_iff.2 (rotOne_ne_zero_sph hs hv1 h1))
  have hΘ := sphAngleCornerOne_mem_Icc hs a b β β' hz h0 h1 h2
  have hn := norm_polar_le_sph (3 / 2) (σ.sphAngleCornerOne a b β β' z) hS0.le
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hn
  rw [sphCornerOne]
  exact ⟨im_polar_nonneg_sph hS0.le hΘ, by linarith⟩

theorem im_sphCornerOne_pos (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) : 0 < (σ.sphCornerOne a b β β' z).im := by
  obtain ⟨-, h1, -⟩ := ne_vertices_of_pos_sph hs hpos
  have hS0 := sphInnerRadial_pos (p := σ.p₁) (a := a) (b := b) (sphTau_pos hs 0).le
    (sphTau_lt_one hs 0)
    (norm_pos_iff.2 (rotOne_ne_zero_sph hs (one_add_conj_vertexOne_ne_sph hs hz) h1))
  rw [sphCornerOne]
  exact im_polar_pos_sph hS0 (sphAngleCornerOne_mem_Ioo hs a b β β' hz hpos)

theorem sphCornerTwo_bounds (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ (σ.sphCornerTwo a b β β' z).im ∧ ‖σ.sphCornerTwo a b β β' z‖ < 7 / 2 := by
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have hS2 := sphInnerRadial_lt_two (p := σ.p₂) (a := a) (b := b) (sphTau_pos hs 1)
    (norm_nonneg _) (norm_rotTwo_le_one_sph hs hz)
  have hS0 := sphInnerRadial_pos (p := σ.p₂) (a := a) (b := b) (sphTau_pos hs 1).le
    (sphTau_lt_one hs 1) (norm_pos_iff.2 (rotTwo_ne_zero_sph hs hv2 h2))
  have hΘ := sphAngleCornerTwo_mem_Icc hs a b β β' hz h0 h1 h2
  have hn := norm_polar_le_sph (-(3 / 2)) (σ.sphAngleCornerTwo a b β β' z) hS0.le
  rw [abs_of_neg (by norm_num : (-(3 / 2) : ℝ) < 0)] at hn
  rw [sphCornerTwo]
  exact ⟨im_polar_nonneg_sph hS0.le hΘ, by linarith⟩

theorem im_sphCornerTwo_pos (a b β β' : ℝ) {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) : 0 < (σ.sphCornerTwo a b β β' z).im := by
  obtain ⟨-, -, h2⟩ := ne_vertices_of_pos_sph hs hpos
  have hS0 := sphInnerRadial_pos (p := σ.p₂) (a := a) (b := b) (sphTau_pos hs 1).le
    (sphTau_lt_one hs 1)
    (norm_pos_iff.2 (rotTwo_ne_zero_sph hs (one_add_vertexTwo_ne_sph hs hz) h2))
  rw [sphCornerTwo]
  exact im_polar_pos_sph hS0 (sphAngleCornerTwo_mem_Ioo hs a b β β' hz hpos)

theorem sphCornerThree_bounds {a b : ℝ} (hab : a < b) (hb : b ≤ 1 / 5) (w δ : ℝ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 ≤ (σ.sphCornerThree a b w δ z).im ∧ ‖σ.sphCornerThree a b w δ z‖ < 7 / 2 := by
  have hn1 := norm_le_one_of_mem_sph hs hz
  have hS0 := sphOuterRadial_pos (p := σ.p₃) hab hb (sphTau_pos hs 2).le (norm_nonneg z)
    (by linarith)
  have hS7 := sphOuterRadial_lt_sph (p := σ.p₃) (a := a) (b := b) (sphTau_pos hs 2).le
    (sphTau_lt_one hs 2) (norm_pos_iff.2 h0)
  have hΘ := sphAngleCornerThree_mem_Icc hs a b w δ hz h0 h1 h2
  have hn := norm_polar_le_sph 0 (σ.sphAngleCornerThree a b w δ z) hS0.le
  rw [abs_zero, zero_add] at hn
  rw [sphCornerThree]
  exact ⟨im_polar_nonneg_sph hS0.le hΘ, by linarith⟩

theorem im_sphCornerThree_pos {a b : ℝ} (hab : a < b) (hb : b ≤ 1 / 5) (w δ : ℝ) {z : ℂ}
    (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.sphCornerThree a b w δ z).im := by
  have hS0 := sphOuterRadial_pos (p := σ.p₃) hab hb (sphTau_pos hs 2).le (norm_nonneg z)
    (by linarith [norm_le_one_of_mem_sph hs hz])
  rw [sphCornerThree]
  exact im_polar_pos_sph hS0 (sphAngleCornerThree_mem_Ioo hs a b w δ hz hpos)

theorem ne_vertexOne_of_germ_le_sph {z : ℂ} (h : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius) :
    z ≠ σ.vertexOne := by
  rintro rfl
  rw [rotOne_vertexOne_sph hs, norm_zero] at h
  exact h (sphParams hs).2.2.2.1

theorem ne_vertexTwo_of_germ_le_sph {z : ℂ} (h : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius) :
    z ≠ σ.vertexTwo := by
  rintro rfl
  rw [rotTwo_vertexTwo_sph hs, norm_zero] at h
  exact h (sphParams hs).2.2.2.1

theorem sphPreFold_bounds {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ (σ.sphPreFold z).im ∧ ‖σ.sphPreFold z‖ < 7 / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ho, ho'⟩ := sphParams hs
  unfold sphPreFold
  split_ifs with c1 c2 c3 c4 c5 c6
  · obtain ⟨a, b⟩ := sphApexOne_bounds hs hz
    exact ⟨a, by linarith⟩
  · obtain ⟨a, b⟩ := sphApexTwo_bounds hs hz
    exact ⟨a, by linarith⟩
  · exact outerGerm_bounds_sph hs hz h0
  · exact sphCornerOne_bounds hs _ _ _ _ hz h0 (ne_vertexOne_of_germ_le_sph hs c1)
      (ne_vertexTwo_of_germ_le_sph hs c2)
  · exact sphCornerTwo_bounds hs _ _ _ _ hz h0 (ne_vertexOne_of_germ_le_sph hs c1)
      (ne_vertexTwo_of_germ_le_sph hs c2)
  · have := norm_sphBridgeTwo_lt hs hz (ne_vertexOne_of_germ_le_sph hs c1)
      (ne_vertexTwo_of_germ_le_sph hs c2)
    exact ⟨im_sphBridgeTwo_nonneg hs hz, by linarith⟩
  · exact sphCornerThree_bounds hs ho ho' _ _ hz h0 (ne_vertexOne_of_germ_le_sph hs c1)
      (ne_vertexTwo_of_germ_le_sph hs c2)

theorem norm_sphPreFold_lt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    ‖σ.sphPreFold z‖ < 7 / 2 := (sphPreFold_bounds hs hz h0).2

theorem im_sphPreFold_nonneg {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ (σ.sphPreFold z).im := (sphPreFold_bounds hs hz h0).1

theorem im_sphPreFold_pos {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.sphPreFold z).im := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ho, ho'⟩ := sphParams hs
  obtain ⟨-, h1, h2⟩ := ne_vertices_of_pos_sph hs hpos
  unfold sphPreFold
  split_ifs with c1 c2 c3 c4 c5 c6
  · exact im_sphApexOne_pos hs hz hpos
  · exact im_sphApexTwo_pos hs hz hpos
  · exact im_outerGerm_pos_sph hs hz hpos
  · exact im_sphCornerOne_pos hs _ _ _ _ hz hpos
  · exact im_sphCornerTwo_pos hs _ _ _ _ hz hpos
  · exact im_sphBridgeTwo_pos hs (mem_sphDomTwo hs hz h1 h2) (sector_rotTwo_pos_sph hs hz hpos).1
  · exact im_sphCornerThree_pos hs ho ho' _ _ hz hpos

theorem sphGermRadius_lt_tau (j : Fin 3) (hj : j ≠ 2) : σ.sphGermRadius < σ.sphTau j := by
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have m0 : σ.sphInnerScale ≤ σ.sphTau 0 := min_le_left _ _
  have m1 : σ.sphInnerScale ≤ σ.sphTau 1 := min_le_right _ _
  have hm : 0 < σ.sphInnerScale := lt_min t0 t1
  unfold sphGermRadius
  fin_cases j
  · change σ.sphInnerScale / 8 < σ.sphTau 0
    linarith
  · change σ.sphInnerScale / 8 < σ.sphTau 1
    linarith
  · exact absurd rfl hj

theorem sphCanon_two_neg_of_lt {z : ℂ} (h : ‖z‖ < σ.sphTau 2) : σ.sphCanon 2 z < 0 := by
  rw [sphCanon]
  exact div_neg_of_neg_of_pos (by change ‖z‖ - _ < 0; linarith)
    (one_add_sphDist_mul_pos hs 2 z)

theorem sphPreFold_eq_outerGerm_of_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h : ‖z‖ < σ.sphOuterGermRadius) : σ.sphPreFold z = compactOuterGerm σ.p₃ z := by
  have ht : ‖z‖ < σ.sphTau 2 := by
    have := sphTau_pos hs 2
    unfold sphOuterGermRadius at h
    linarith
  have c2 := sphCanon_two_neg_of_lt hs ht
  have e0 : σ.sphTau 0 ≤ ‖σ.rotOne z‖ :=
    tau_le_of_sphCanon_nonneg hs (by linarith [sphCanon_add_one_nonneg hs hz])
  have e1 : σ.sphTau 1 ≤ ‖σ.rotTwo z‖ :=
    tau_le_of_sphCanon_nonneg hs (by linarith [sphCanon_add_zero_nonneg hs hz])
  have g0 := sphGermRadius_lt_tau hs 0 (by decide)
  have g1 := sphGermRadius_lt_tau hs 1 (by decide)
  have n1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have n2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have _ := h0
  simp only [sphPreFold, n1, n2, h, ite_false, ite_true]

omit hs in
theorem sphChartTwo_dom_of_ne_zero {ζ : ℂ} (h : σ.sphChartTwo ζ ≠ 0) :
    1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0 := by
  intro h'
  apply h
  rw [sphChartTwo, sphMoebInv, h', div_zero]

omit hs in
theorem sphChartTwo_zero : σ.sphChartTwo 0 = σ.vertexTwo := by
  simp [sphChartTwo, sphMoebInv]

theorem rotTwo_sphChartTwo {ζ : ℂ}
    (hd : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0) :
    σ.rotTwo (σ.sphChartTwo ζ) = ζ := by
  rw [rotTwo_eq_mul_sph hs, sphChartTwo, sphMoeb_sphMoebInv hd]
  linear_combination ζ * exp_mul_exp_neg_sph σ.θ₂

theorem sphChartTwo_rotTwo {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    σ.sphChartTwo (σ.rotTwo z) = z := by
  rw [sphChartTwo, rotTwo_eq_mul_sph hs]
  have e : -exp (-((σ.θ₂ : ℂ) * I)) * (-exp ((σ.θ₂ : ℂ) * I) * sphMoeb σ.vertexTwo z) =
      sphMoeb σ.vertexTwo z := by
    linear_combination sphMoeb σ.vertexTwo z * exp_mul_exp_neg_sph σ.θ₂
  rw [e]
  exact sphMoebInv_sphMoeb (by rwa [conj_vertexTwo_sph])

omit hs in
theorem one_add_vertexTwo_sphChartTwo {ζ : ℂ}
    (hd : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0) :
    1 + σ.vertexTwo * σ.sphChartTwo ζ ≠ 0 := by
  have e := one_add_conj_mul_sphMoebInv hd
  rw [conj_vertexTwo_sph] at e hd
  rw [sphChartTwo, e]
  exact div_ne_zero one_add_vertexTwo_mul_self_ne_sph hd

theorem rotTwo_of_pole_sph {z : ℂ} (h : 1 + σ.vertexTwo * z = 0) : σ.rotTwo z = 0 := by
  rw [rotTwo_eq_mul_sph hs, sphMoeb, conj_vertexTwo_sph, h, div_zero, mul_zero]

theorem sphChartTwo_dom_of_re {ζ : ℂ} (h1 : 0 ≤ ζ.re) (h2 : 0 ≤ ζ.im) :
    1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0 := by
  have e : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) =
      1 + (σ.sphTTwoThree : ℂ) * (exp (((-σ.θ₂ : ℝ) : ℂ) * I) * ζ) := by
    rw [conj_vertexTwo_sph, vertexTwo_eq_sph, exp_neg_ofReal_mul_I_sph]
    ring
  rw [e]
  apply one_add_ne_of_re_nonneg_sph
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  have := σ.cos_θ₂_nonneg_sph
  have := σ.sin_θ₂_pos_sph
  have := tTwoThree_pos_sph hs
  have : 0 ≤ Real.cos σ.θ₂ * ζ.re - -Real.sin σ.θ₂ * ζ.im := by nlinarith
  positivity

omit hs in
theorem hasDerivAt_sphChartTwo {ζ : ℂ}
    (hd : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0) :
    HasDerivAt σ.sphChartTwo ((1 + conj σ.vertexTwo * σ.vertexTwo) /
      (1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ)) ^ 2 *
        (-exp (-((σ.θ₂ : ℂ) * I)))) ζ := by
  have h1 : HasDerivAt (fun u : ℂ => -exp (-((σ.θ₂ : ℂ) * I)) * u)
      (-exp (-((σ.θ₂ : ℂ) * I))) ζ := by
    simpa using (hasDerivAt_id ζ).const_mul (-exp (-((σ.θ₂ : ℂ) * I)))
  exact (hasDerivAt_sphMoebInv hd).comp ζ h1

omit hs in
theorem contDiffAt_sphChartTwo {ζ : ℂ}
    (hd : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0) :
    ContDiffAt ℝ ∞ σ.sphChartTwo ζ := by
  have h1 : ContDiffAt ℂ ∞ (fun u : ℂ => -exp (-((σ.θ₂ : ℂ) * I)) * u + σ.vertexTwo) ζ :=
    (contDiffAt_const.mul contDiffAt_id).add contDiffAt_const
  have h2 : ContDiffAt ℂ ∞
      (fun u : ℂ => 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * u)) ζ :=
    contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_const.mul contDiffAt_id))
  exact (h1.div h2 hd).restrict_scalars ℝ

omit hs in
theorem det_fderiv_sphChartTwo_pos {ζ : ℂ}
    (hd : 1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0) :
    0 < (fderiv ℝ σ.sphChartTwo ζ).det := by
  rw [det_fderiv_of_hasDerivAt (hasDerivAt_sphChartTwo hd)]
  exact Complex.normSq_pos.2 (mul_ne_zero (div_ne_zero (one_add_conj_mul_self_ne_sph _)
    (pow_ne_zero _ hd)) (neg_ne_zero.2 (Complex.exp_ne_zero _)))

theorem det_fderiv_rotTwo_pos_sph {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    0 < (fderiv ℝ σ.rotTwo z).det := by
  rw [det_fderiv_of_hasDerivAt (hasDerivAt_rotTwo_sph hs hv2)]
  have h' : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  exact Complex.normSq_pos.2 (mul_ne_zero (neg_ne_zero.2 (Complex.exp_ne_zero _))
    (div_ne_zero (one_add_conj_mul_self_ne_sph _) (pow_ne_zero _ h')))

theorem one_add_tOneTwo_rotTwo_eq_sph {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z =
      (1 + conj σ.vertexTwo * σ.vertexTwo) * (1 + conj σ.vertexOne * z) /
        ((1 + σ.vertexTwo * conj σ.vertexOne) * (1 + conj σ.vertexTwo * z)) := by
  have hv : 1 + conj σ.vertexTwo * σ.vertexOne ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_vertexOne_ne_sph hs
  have hz2 : 1 + conj σ.vertexTwo * z ≠ 0 := by rwa [conj_vertexTwo_sph]
  rw [← one_add_conj_sphMoeb_mul hz2 hv, sphMoeb_vertexTwo_vertexOne hs, rotTwo_eq_mul_sph hs,
    map_neg, map_mul, conj_exp_neg_sph, Complex.conj_ofReal]
  ring

theorem one_add_conj_vertexOne_ne_of_chart_sph {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0)
    (ht : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0) : 1 + conj σ.vertexOne * z ≠ 0 := by
  intro h
  rw [one_add_tOneTwo_rotTwo_eq_sph hs hv2, h, mul_zero, zero_div] at ht
  exact ht rfl

theorem one_add_tOneTwo_ne_of_re_sph {ζ : ℂ} (h : 0 ≤ ζ.re) : 1 + (σ.sphTOneTwo : ℂ) * ζ ≠ 0 := by
  apply one_add_ne_of_re_nonneg_sph
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (tOneTwo_pos_sph hs).le h

theorem wallSide_one_chart_sph {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hv2 : 1 + σ.vertexTwo * z ≠ 0) (ht : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0) :
    σ.wallSide 1 z * (1 + σ.sphTOneThree ^ 2) * Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z) =
      σ.sphChartSideOne (σ.rotTwo z) * Complex.normSq (1 + conj σ.vertexOne * z) := by
  have e := wallSide_one_eq_rotOne_sph hs z
  have e2 := im_rot_sphMoeb_real_sph σ.θ₁ σ.sphTOneTwo ht
  rw [e, rotOne_eq_rotTwo_sph hs hv1 (by rwa [conj_vertexTwo_sph]), sphChartSideOne, ← e2]
  ring

theorem wallSide_zero_chart_sph (z : ℂ) :
    σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) =
      σ.sphChartSideZero (σ.rotTwo z) * Complex.normSq (1 + σ.vertexTwo * z) :=
  wallSide_zero_eq_rotTwo_sph hs z

omit hs in
theorem re_nonneg_of_chartRegion_sph {ζ : ℂ} (h : ζ ∈ σ.sphChartRegion) : 0 ≤ ζ.re :=
  re_nonneg_of_sector_sph σ.θ₂_pos_sph σ.θ₂_le_sph h.1 h.2.1

theorem chartRegion_of_mem_triangle_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    σ.rotTwo z ∈ σ.sphChartRegion := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have ht := one_add_tOneTwo_ne_of_re_sph hs (re_rotTwo_nonneg_sph hs hz)
  obtain ⟨w0, w1, -⟩ := (mem_triangle_iff_sph hs).1 hz
  refine ⟨(sector_two_sph hs hz).1, ?_, ?_⟩
  · have e := wallSide_zero_chart_sph hs z
    have : 0 ≤ σ.sphChartSideZero (σ.rotTwo z) * Complex.normSq (1 + σ.vertexTwo * z) := by
      rw [← e]; exact mul_nonneg w0 (by positivity)
    exact nonneg_of_mul_nonneg_left this (Complex.normSq_pos.2 hv2)
  · have e := wallSide_one_chart_sph hs hv1 hv2 ht
    have : 0 ≤ σ.sphChartSideOne (σ.rotTwo z) * Complex.normSq (1 + conj σ.vertexOne * z) := by
      rw [← e]; exact mul_nonneg (mul_nonneg w1 (by positivity)) (Complex.normSq_nonneg _)
    exact nonneg_of_mul_nonneg_left this (Complex.normSq_pos.2 hv1)

theorem chartSide_pos_of_pos_sph {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.rotTwo z).im ∧ 0 < σ.sphChartSideZero (σ.rotTwo z) ∧
      0 < σ.sphChartSideOne (σ.rotTwo z) := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 := one_add_vertexTwo_ne_sph hs hz
  have ht := one_add_tOneTwo_ne_of_re_sph hs (re_rotTwo_nonneg_sph hs hz)
  refine ⟨(sector_rotTwo_pos_sph hs hz hpos).1, ?_, ?_⟩
  · have e := wallSide_zero_chart_sph hs z
    have : 0 < σ.sphChartSideZero (σ.rotTwo z) * Complex.normSq (1 + σ.vertexTwo * z) := by
      rw [← e]; exact mul_pos (hpos 0) (by positivity)
    exact (mul_pos_iff_of_pos_right (Complex.normSq_pos.2 hv2)).1 this
  · have e := wallSide_one_chart_sph hs hv1 hv2 ht
    have : 0 < σ.sphChartSideOne (σ.rotTwo z) * Complex.normSq (1 + conj σ.vertexOne * z) := by
      rw [← e]; exact mul_pos (mul_pos (hpos 1) (by positivity)) (Complex.normSq_pos.2 ht)
    exact (mul_pos_iff_of_pos_right (Complex.normSq_pos.2 hv1)).1 this

theorem mem_triangle_sphChartTwo {ζ : ℂ} (h : ζ ∈ σ.sphChartRegion) :
    σ.sphChartTwo ζ ∈ σ.triangle ∧
      1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0 := by
  have hre := re_nonneg_of_chartRegion_sph h
  have hd := sphChartTwo_dom_of_re hs hre h.1
  refine ⟨?_, hd⟩
  set z := σ.sphChartTwo ζ with hzdef
  have hv2 := one_add_vertexTwo_sphChartTwo hd
  have hr : σ.rotTwo z = ζ := rotTwo_sphChartTwo hs hd
  have ht : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0 := by
    rw [hr]; exact one_add_tOneTwo_ne_of_re_sph hs hre
  have hv1 := one_add_conj_vertexOne_ne_of_chart_sph hs hv2 ht
  refine (mem_triangle_iff_sph hs).2 ⟨?_, ?_, ?_⟩
  · have e := wallSide_zero_chart_sph hs z
    rw [hr] at e
    have : 0 ≤ σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) := by
      rw [e]; exact mul_nonneg h.2.1 (Complex.normSq_nonneg _)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  · have e := wallSide_one_chart_sph hs hv1 hv2 ht
    rw [hr] at e
    have : 0 ≤ σ.wallSide 1 z * ((1 + σ.sphTOneThree ^ 2) *
        Complex.normSq (1 + σ.sphTOneTwo * ζ)) := by
      rw [← mul_assoc, e]; exact mul_nonneg h.2.2 (Complex.normSq_nonneg _)
    refine nonneg_of_mul_nonneg_left this (mul_pos (by positivity) ?_)
    rw [← hr]
    exact Complex.normSq_pos.2 ht
  · rw [wallSide_two_eq_sph hs, hr]
    exact mul_nonneg h.1 (Complex.normSq_nonneg _)

theorem wallSide_pos_sphChartTwo {ζ : ℂ} (h2 : 0 < ζ.im) (h0 : 0 < σ.sphChartSideZero ζ)
    (h1 : 0 < σ.sphChartSideOne ζ) : ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ) := by
  have hreg : ζ ∈ σ.sphChartRegion := ⟨h2.le, h0.le, h1.le⟩
  have hre := re_nonneg_of_chartRegion_sph hreg
  have hd := sphChartTwo_dom_of_re hs hre h2.le
  set z := σ.sphChartTwo ζ with hzdef
  have hv2 := one_add_vertexTwo_sphChartTwo hd
  have hr : σ.rotTwo z = ζ := rotTwo_sphChartTwo hs hd
  have ht : 1 + (σ.sphTOneTwo : ℂ) * σ.rotTwo z ≠ 0 := by
    rw [hr]; exact one_add_tOneTwo_ne_of_re_sph hs hre
  have hv1 := one_add_conj_vertexOne_ne_of_chart_sph hs hv2 ht
  intro i
  fin_cases i
  · have e := wallSide_zero_chart_sph hs z
    rw [hr] at e
    have : 0 < σ.wallSide 0 z * (1 + σ.sphTTwoThree ^ 2) := by
      rw [e]; exact mul_pos h0 (Complex.normSq_pos.2 hv2)
    exact (mul_pos_iff_of_pos_right (by positivity)).1 this
  · have e := wallSide_one_chart_sph hs hv1 hv2 ht
    have : 0 < σ.wallSide 1 z * ((1 + σ.sphTOneThree ^ 2) *
        Complex.normSq (1 + σ.sphTOneTwo * σ.rotTwo z)) := by
      rw [← mul_assoc, e, hr]; exact mul_pos h1 (Complex.normSq_pos.2 hv1)
    exact (mul_pos_iff_of_pos_right (mul_pos (by positivity) (Complex.normSq_pos.2 ht))).1 this
  · change 0 < σ.wallSide 2 z
    rw [wallSide_two_eq_sph hs, hr]
    exact mul_pos h2 (Complex.normSq_pos.2 hv2)

theorem norm_rotTwo_eq_div_sph (z : ℂ) :
    ‖σ.rotTwo z‖ = ‖z - σ.vertexTwo‖ / ‖1 + σ.vertexTwo * z‖ := by
  rw [norm_rotTwo_sph hs, sphMoeb, norm_div, conj_vertexTwo_sph]

theorem isOpen_rotTwo_far_sph (c : ℂ) (r : ℝ) : IsOpen {z | r < ‖σ.rotTwo z - c‖} := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  by_cases hp : 1 + σ.vertexTwo * z = 0
  · have hz0 : σ.rotTwo z = 0 := rotTwo_of_pole_sph hs hp
    change r < ‖σ.rotTwo z - c‖ at hz
    rw [hz0, zero_sub, norm_neg] at hz
    have hzv : z ≠ σ.vertexTwo := by
      rintro rfl
      exact one_add_vertexTwo_mul_self_ne_sph hp
    have hA : 0 < ‖z - σ.vertexTwo‖ - (r + ‖c‖) * ‖1 + σ.vertexTwo * z‖ := by
      rw [hp, norm_zero, mul_zero, sub_zero]
      exact norm_pos_iff.2 (sub_ne_zero.2 hzv)
    have hcont : ContinuousAt (fun u : ℂ => ‖u - σ.vertexTwo‖ -
        (r + ‖c‖) * ‖1 + σ.vertexTwo * u‖) z := by fun_prop
    filter_upwards [hcont.eventually (lt_mem_nhds hA)] with u hu
    by_cases hu0 : 1 + σ.vertexTwo * u = 0
    · rw [rotTwo_of_pole_sph hs hu0, zero_sub, norm_neg]
      exact hz
    · have hN := norm_pos_iff.2 hu0
      have h1 : r + ‖c‖ < ‖σ.rotTwo u‖ := by
        rw [norm_rotTwo_eq_div_sph hs, lt_div_iff₀ hN]
        linarith
      have h2 := norm_sub_norm_le (σ.rotTwo u) c
      linarith
  · exact ((contDiffAt_rotTwo_sph hs hp).continuousAt.sub continuousAt_const).norm.eventually
      (lt_mem_nhds hz)

theorem exists_sphFoldCore_of {c : ℂ} {r δ : ℝ} (hδ : 0 < δ) (hδr : δ < r) {G : Set ℂ}
    (hGo : IsOpen G) (hGsm : ∀ z ∈ G, ContDiffAt ℝ ∞ σ.sphPreFold z)
    (hGdet : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ σ.sphPreFold z).det)
    (hcover : ∀ z ∈ σ.triangle, z ≠ 0 → r - δ ≤ ‖σ.rotTwo z - c‖ → z ∈ G)
    (hin : ∀ ζ : ℂ, ‖ζ - c‖ < r + δ → ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ))
    (hinj : InjOn σ.sphPreFold (σ.triangle \ {0})) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ σ.triangle \ {0} ⊆ U ∧
      (∀ z, z ≠ 0 → z ∈ G → r < ‖σ.rotTwo z - c‖ → z ∈ U) ∧ ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, r ≤ ‖σ.rotTwo z - c‖ → F z = σ.sphPreFold z) ∧
      InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven := by
  have hr0 : 0 < r := by linarith
  have hdisc : ∀ ζ, ‖ζ - c‖ < r + δ → σ.sphChartTwo ζ ∈ σ.triangle ∧
      (∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ)) ∧ σ.sphChartTwo ζ ≠ 0 ∧
      σ.sphChartTwo ζ ≠ σ.vertexOne ∧ σ.sphChartTwo ζ ≠ σ.vertexTwo ∧
      1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0 ∧
      σ.rotTwo (σ.sphChartTwo ζ) = ζ := by
    intro ζ hζ
    have hp := hin ζ hζ
    have hT : σ.sphChartTwo ζ ∈ σ.triangle :=
      (mem_triangle_iff_sph hs).2 ⟨(hp 0).le, (hp 1).le, (hp 2).le⟩
    obtain ⟨h0, h1, h2⟩ := ne_vertices_of_pos_sph hs hp
    have hd := sphChartTwo_dom_of_ne_zero h0
    exact ⟨hT, hp, h0, h1, h2, hd, rotTwo_sphChartTwo hs hd⟩
  have hann : ∀ ζ, r - δ < ‖ζ - c‖ → ‖ζ - c‖ < r + δ → σ.sphChartTwo ζ ∈ G := by
    intro ζ h1 h2
    obtain ⟨hT, -, h0, -, -, -, hr⟩ := hdisc ζ h2
    exact hcover _ hT h0 (by rw [hr]; exact h1.le)
  set E' : ℂ → ℂ := fun ζ => σ.sphPreFold (σ.sphChartTwo ζ) with hE'def
  have hE'sm : ∀ ζ, r - δ < ‖ζ - c‖ → ‖ζ - c‖ < r + δ → ContDiffAt ℝ ∞ E' ζ := by
    intro ζ h1 h2
    obtain ⟨-, -, -, -, -, hd, -⟩ := hdisc ζ h2
    exact (hGsm _ (hann ζ h1 h2)).comp ζ (contDiffAt_sphChartTwo hd)
  have hE'det : ∀ ζ, r - δ < ‖ζ - c‖ → ‖ζ - c‖ < r + δ → 0 < (fderiv ℝ E' ζ).det := by
    intro ζ h1 h2
    obtain ⟨-, -, -, a1, a2, hd, -⟩ := hdisc ζ h2
    have hg := hann ζ h1 h2
    rw [show E' = σ.sphPreFold ∘ σ.sphChartTwo from rfl,
      det_fderiv_comp_sph ((hGsm _ hg).differentiableAt (by simp))
        ((contDiffAt_sphChartTwo hd).differentiableAt (by simp))]
    exact mul_pos (hGdet _ hg a1 a2) (det_fderiv_sphChartTwo_pos hd)
  have hE' : ContDiffOn ℝ ∞ E' {ζ | r - δ < ‖ζ - c‖ ∧ ‖ζ - c‖ < r + δ} := fun ζ hζ =>
    (hE'sm ζ hζ.1 hζ.2).contDiffWithinAt
  have hdet : ∀ ζ, r - δ < ‖ζ - c‖ → ‖ζ - c‖ < r + δ → (fderiv ℝ E' ζ).det ≠ 0 :=
    fun ζ h1 h2 => (hE'det ζ h1 h2).ne'
  have hinjA : InjOn E' {ζ | r - δ < ‖ζ - c‖ ∧ ‖ζ - c‖ < r + δ} := by
    intro ζ hζ ζ' hζ' h
    obtain ⟨hT, -, h0, -, -, -, hr⟩ := hdisc ζ hζ.2
    obtain ⟨hT', -, h0', -, -, -, hr'⟩ := hdisc ζ' hζ'.2
    have := hinj ⟨hT, h0⟩ ⟨hT', h0'⟩ h
    rw [← hr, ← hr', this]
  have hsph : ∀ q ∈ sphere c r, ‖q - c‖ = r ∧ ContinuousAt E' q ∧ E' q ∈ openHalfSeven := by
    intro q hq
    have hq' : ‖q - c‖ = r := by rwa [mem_sphere_iff_norm] at hq
    obtain ⟨hT, hp, h0, -⟩ := hdisc q (by linarith)
    exact ⟨hq', (hE'sm q (by linarith) (by linarith)).continuousAt,
      norm_sphPreFold_lt hs hT h0, im_sphPreFold_pos hs hT hp⟩
  have ht0 : 0 ≤ σ.sphTOneTwo := (tOneTwo_pos_sph hs).le
  set ζ₃ := σ.rotTwo 0 with hζ₃
  have hv0 : 1 + σ.vertexTwo * 0 ≠ 0 := by simp
  have hψ3 : σ.sphChartTwo ζ₃ = 0 := sphChartTwo_rotTwo hs hv0
  set O : Set ℂ := {ζ | ζ ∈ σ.sphChartRegion ∧ ζ ≠ ζ₃ ∧ r < ‖ζ - c‖} with hOdef
  have hOmem : ∀ ζ ∈ O, σ.sphChartTwo ζ ∈ σ.triangle ∧ σ.sphChartTwo ζ ≠ 0 ∧
      σ.rotTwo (σ.sphChartTwo ζ) = ζ ∧ σ.sphChartTwo ζ ∈ G ∧
      1 - conj σ.vertexTwo * (-exp (-((σ.θ₂ : ℂ) * I)) * ζ) ≠ 0 := by
    intro ζ hζ
    obtain ⟨hT, hd⟩ := mem_triangle_sphChartTwo hs hζ.1
    have hr := rotTwo_sphChartTwo hs hd
    have h0 : σ.sphChartTwo ζ ≠ 0 := fun h => hζ.2.1 (by rw [← hr, h])
    exact ⟨hT, h0, hr, hcover _ hT h0 (by rw [hr]; linarith [hζ.2.2]), hd⟩
  have hE'O : ContinuousOn E' O := fun ζ hζ => by
    obtain ⟨-, -, -, hg, hd⟩ := hOmem ζ hζ
    exact ((hGsm _ hg).continuousAt.comp
      (contDiffAt_sphChartTwo hd).continuousAt).continuousWithinAt
  obtain ⟨hcT, hcp, -, -, -, -, hcr⟩ := hdisc c (by rw [sub_self, norm_zero]; linarith)
  have hcR : c ∈ σ.sphChartRegion := by
    rw [← hcr]
    exact chartRegion_of_mem_triangle_sph hs hcT
  have hc0 : 0 < σ.sphChartSideZero c := by
    have := (chartSide_pos_of_pos_sph hs hcT hcp).2.1
    rwa [hcr] at this
  have hζ₃0 : σ.sphChartSideZero ζ₃ = 0 := by
    have e := wallSide_zero_chart_sph hs 0
    rw [wallSide_zero_zero_sph, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (Complex.normSq_pos.2 hv0).ne'
  have hζ₃far : r + δ ≤ ‖ζ₃ - c‖ := by
    by_contra h
    push Not at h
    have := (hdisc ζ₃ h).2.1 0
    rw [hψ3, wallSide_zero_zero_sph] at this
    exact lt_irrefl 0 this
  have hζ₃R : ζ₃ ∈ σ.sphChartRegion := chartRegion_of_mem_triangle_sph hs (zero_mem_triangle_sph hs)
  set ρ₂ := r + δ / 2 with hρ₂
  have hnear : ∀ ζ : ℂ, ‖ζ - c‖ ≤ ρ₂ → r < ‖ζ - c‖ → ζ ∈ O := by
    intro ζ h1 h2
    obtain ⟨hT, -, h0, -, -, -, hr⟩ := hdisc ζ (by linarith)
    refine ⟨by rw [← hr]; exact chartRegion_of_mem_triangle_sph hs hT, fun h => h0 ?_, h2⟩
    rw [h]
    exact hψ3
  have hOc : IsPreconnected O := by
    have hρ₂r : r < ρ₂ := by linarith
    have hCsub : sphere c ρ₂ ⊆ O := fun w hw => by
      have : ‖w - c‖ = ρ₂ := by rwa [mem_sphere_iff_norm] at hw
      exact hnear w this.le (by rw [this]; exact hρ₂r)
    have hCc : IsPreconnected (sphere c ρ₂) :=
      isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c ρ₂
    have hρ₂0 : 0 < ρ₂ := by linarith
    have hx₀ : c + (ρ₂ : ℂ) ∈ sphere c ρ₂ := by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ₂0]
    refine isPreconnected_of_forall (c + (ρ₂ : ℂ)) fun ζ hζ => ?_
    obtain ⟨hζR, hζ3, hζr⟩ := hζ
    set d := ‖ζ - c‖ with hd
    have hd0 : 0 < d := by linarith
    set g : ℝ → ℂ := fun s => c + (s : ℂ) * (ζ - c) with hg
    have hk : ρ₂ / d * d = ρ₂ := div_mul_cancel₀ _ hd0.ne'
    have hsr : ∀ s ∈ uIcc 1 (ρ₂ / d), 0 ≤ s ∧ r < s * d ∧ (1 < s → s * d ≤ ρ₂) := by
      intro s hs'
      rcases mem_uIcc.1 hs' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨by linarith, by nlinarith, fun _ => ?_⟩
        nlinarith
      · have h0 : 0 ≤ ρ₂ / d := div_nonneg hρ₂0.le hd0.le
        refine ⟨by linarith, ?_, fun h => absurd h (not_lt.2 h2)⟩
        have := mul_le_mul_of_nonneg_right h1 hd0.le
        rw [hk] at this
        linarith
    have hsegsub : g '' uIcc 1 (ρ₂ / d) ⊆ O := by
      rintro _ ⟨s, hs', rfl⟩
      obtain ⟨hs0, hlo, hhi⟩ := hsr s hs'
      have hn := EuclidShape.norm_lineMap_sub c ζ hs0
      rcases le_or_gt s 1 with hs1 | hs1
      · refine ⟨segment_mem_sphChartRegion ht0 hcR hζR hs0 hs1, ?_, by rw [hn]; exact hlo⟩
        rcases hs1.lt_or_eq with hs1 | hs1
        · intro h3
          have e := sphChartSideZero_segment (σ := σ) c ζ s
          change σ.sphChartSideZero (c + (s : ℂ) * (ζ - c)) = _ at e
          rw [show c + (s : ℂ) * (ζ - c) = ζ₃ from h3, hζ₃0] at e
          have := mul_pos (sub_pos.2 hs1) hc0
          have := mul_nonneg hs0 hζR.2.1
          linarith
        · change c + (s : ℂ) * (ζ - c) ≠ ζ₃
          rw [hs1, ofReal_one, one_mul, add_sub_cancel]
          exact hζ3
      · exact hnear _ (by rw [hn]; exact hhi hs1) (by rw [hn]; exact hlo)
    have hsegc : IsPreconnected (g '' uIcc 1 (ρ₂ / d)) :=
      isPreconnected_uIcc.image _ (by fun_prop)
    have hzseg : ζ ∈ g '' uIcc 1 (ρ₂ / d) := ⟨1, left_mem_uIcc, by simp [hg]⟩
    have hcseg : g (ρ₂ / d) ∈ g '' uIcc 1 (ρ₂ / d) := ⟨ρ₂ / d, right_mem_uIcc, rfl⟩
    have hcC : g (ρ₂ / d) ∈ sphere c ρ₂ := by
      rw [mem_sphere_iff_norm, hg]
      dsimp only
      rw [EuclidShape.norm_lineMap_sub c ζ (div_nonneg hρ₂0.le hd0.le), ← hd, hk]
    exact ⟨_ ∪ sphere c ρ₂, union_subset hsegsub hCsub, Or.inr hx₀, Or.inl hzseg,
      hsegc.union _ hcseg hcC hCc⟩
  obtain ⟨qmax, hqmax, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr0.le)
    (fun q hq => (hsph q hq).2.1.norm.continuousWithinAt)
  set M := ‖E' qmax‖ with hM
  have hM7 : M < 7 / 2 := (hsph qmax hqmax).2.2.1
  have hog := (sphParams hs).2.2.2.2.2.2.2.1
  set s₀ := min (min 1 (7 / 2 - M)) σ.sphOuterGermRadius with hs₀
  have hs₀0 : 0 < s₀ := lt_min (lt_min one_pos (by linarith)) hog
  have hs₀1 : s₀ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hs₀M : s₀ ≤ 7 / 2 - M := (min_le_left _ _).trans (min_le_right _ _)
  have hs₀g : s₀ ≤ σ.sphOuterGermRadius := min_le_right _ _
  have hd3 := (mem_triangle_sphChartTwo hs hζ₃R).2
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 (contDiffAt_sphChartTwo hd3).continuousAt
    s₀ hs₀0
  set L := ‖c - ζ₃‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  set k := min (1 / 2) (min (η / (2 * L)) (δ / (2 * (r + δ)))) with hkdef
  have hk0 : 0 < k := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hk1 : k ≤ 1 / 2 := min_le_left _ _
  have hkη : k ≤ η / (2 * L) := (min_le_right _ _).trans (min_le_left _ _)
  have hkδ : k ≤ δ / (2 * (r + δ)) := (min_le_right _ _).trans (min_le_right _ _)
  set ζt := ζ₃ + (k : ℂ) * (c - ζ₃) with hζt
  have hζtR : ζt ∈ σ.sphChartRegion := segment_mem_sphChartRegion ht0 hζ₃R hcR hk0.le (by linarith)
  have hζt3 : ζt ≠ ζ₃ := by
    intro h
    have e := sphChartSideZero_segment (σ := σ) ζ₃ c k
    rw [← hζt, h, hζ₃0] at e
    have := mul_pos hk0 hc0
    linarith
  have hζtc : r < ‖ζt - c‖ := by
    have e : ζt - c = ((1 - k : ℝ) : ℂ) * (ζ₃ - c) := by
      rw [hζt]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hrδ : 0 < r + δ := by linarith
    have hk' : k * (2 * (r + δ)) ≤ δ := by
      rw [le_div_iff₀ (by positivity)] at hkδ
      exact hkδ
    nlinarith
  have hζtO : ζt ∈ O := ⟨hζtR, hζt3, hζtc⟩
  obtain ⟨hztT, hzt0, -, -, -⟩ := hOmem ζt hζtO
  have hztn : ‖σ.sphChartTwo ζt‖ < s₀ := by
    have hdist : dist ζt ζ₃ < η := by
      rw [dist_eq_norm, hζt, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk0]
      have hcz : ‖c - ζ₃‖ < L := by rw [hL]; linarith
      have h1 : k * ‖c - ζ₃‖ ≤ k * L := mul_le_mul_of_nonneg_left hcz.le hk0.le
      have h2 : k * L ≤ η / 2 := by
        rw [le_div_iff₀ (by positivity)] at hkη
        nlinarith
      linarith
    have := hηb hdist
    rwa [dist_eq_norm, hψ3, sub_zero] at this
  have hztpow : ‖σ.sphChartTwo ζt‖ ^ σ.p₃ ≤ ‖σ.sphChartTwo ζt‖ :=
    pow_le_of_le_one (norm_nonneg _) (by linarith) (by have := σ.two_le_p₃; omega)
  have hEzt : E' ζt = compactOuterGerm σ.p₃ (σ.sphChartTwo ζt) :=
    sphPreFold_eq_outerGerm_of_mem hs hztT hzt0 (by linarith)
  have hnE : M < ‖E' ζt‖ := by
    rw [hEzt, norm_compactOuterGerm hzt0 (by linarith)]
    linarith
  set u₀ := E' ζt with hu₀
  have hu0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnE
    linarith [norm_nonneg (E' qmax)]
  set S := E' '' O ∪ (fun t : ℝ => (t : ℂ) * u₀) '' Ici 1 with hSdef
  have hSc : IsPreconnected S :=
    (hOc.image E' hE'O).union u₀ ⟨ζt, hζtO, rfl⟩ ⟨1, mem_Ici.2 le_rfl, by simp⟩
      (isPreconnected_ray u₀)
  have hSb : ¬ Bornology.IsBounded S := fun hb =>
    not_isBounded_ray hu0 (hb.subset subset_union_right)
  have hSd : Disjoint S (E' '' sphere c r) := by
    rw [disjoint_left]
    rintro v (⟨x, hx, hxv⟩ | hv) ⟨q, hq, hqv⟩
    · obtain ⟨hxT, hx0, hxr, -⟩ := hOmem x hx
      have hq' : ‖q - c‖ = r := (hsph q hq).1
      obtain ⟨hqT, -, hq0, -, -, -, hqr⟩ := hdisc q (by linarith)
      have := hinj ⟨hxT, hx0⟩ ⟨hqT, hq0⟩ (hxv.trans hqv.symm)
      have hxq : x = q := by rw [← hxr, ← hqr, this]
      have h2 := hx.2.2
      rw [hxq, hq'] at h2
      exact lt_irrefl _ h2
    · have h1 := norm_ray_ge hv
      have h2 : ‖E' q‖ ≤ M := hmax hq
      rw [hqv] at h2
      linarith
  set z₀ : ℂ := c + ((r + δ / 2 : ℝ) : ℂ) with hz₀
  have hz₀n : ‖z₀ - c‖ = r + δ / 2 := by
    rw [hz₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hout : ∃ z₀, r < ‖z₀ - c‖ ∧ ‖z₀ - c‖ < r + δ ∧ ∃ S : Set ℂ, IsPreconnected S ∧
      E' z₀ ∈ S ∧ Disjoint S (E' '' sphere c r) ∧ ¬ Bornology.IsBounded S :=
    ⟨z₀, by rw [hz₀n]; linarith, by rw [hz₀n]; linarith, S, hSc,
      Or.inl ⟨z₀, hnear z₀ (by rw [hz₀n]) (by rw [hz₀n]; linarith), rfl⟩, hSd, hSb⟩
  obtain ⟨Q, hQs, hQi, hQd, ⟨V, hVo, hsV, hQV⟩, hQc⟩ :=
    exists_core_replacement hδ hδr hE' hdet hinjA hout
  have hQE : Q =ᶠ[𝓝 qmax] E' := Filter.eventually_of_mem (hVo.mem_nhds (hsV hqmax)) hQV
  have hQpos : ∀ u, 0 < (fderiv ℝ Q u).det := by
    have hq := (hsph qmax hqmax).1
    refine det_pos_of_ne_zero hQs hQd (u₀ := qmax) ?_
    rw [hQE.fderiv_eq]
    exact hE'det qmax (by linarith) (by linarith)
  have hQball : Q '' ball c r ⊆ openHalfSeven := by
    rintro _ ⟨w, hw, rfl⟩
    by_contra hcon
    obtain ⟨S₀, hS₀, huS, hS₀d, hS₀b⟩ := outside_halfSeven hcon
    have hΓ : Disjoint S₀ (E' '' sphere c r) := by
      refine disjoint_left.2 fun v hv ⟨q, hq, hqv⟩ => disjoint_left.1 hS₀d hv ?_
      rw [← hqv]
      exact (hsph q hq).2.2
    exact disjoint_left.1 (hQc S₀ hS₀ hS₀b hΓ) huS ⟨w, hw, rfl⟩
  have hpole : ∀ z : ℂ, ‖σ.rotTwo z - c‖ < r + δ → 1 + σ.vertexTwo * z ≠ 0 := by
    intro z hz hp
    rw [rotTwo_of_pole_sph hs hp] at hz
    have := (hdisc 0 hz).2.1 2
    rw [sphChartTwo_zero, wallSide_two_vertexTwo_sph hs] at this
    exact lt_irrefl 0 this
  classical
  set F : ℂ → ℂ := fun z => if ‖σ.rotTwo z - c‖ < r then Q (σ.rotTwo z) else σ.sphPreFold z
    with hFdef
  have hF1 : ∀ z, r ≤ ‖σ.rotTwo z - c‖ → F z = σ.sphPreFold z := fun z hz => by
    simp only [hFdef, not_lt.2 hz, ↓reduceIte]
  set W := {z : ℂ | 1 + σ.vertexTwo * z ≠ 0} ∩ σ.rotTwo ⁻¹' (V ∪ ball c r) with hW
  have hDo : IsOpen {z : ℂ | 1 + σ.vertexTwo * z ≠ 0} := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hWo : IsOpen W := ContinuousOn.isOpen_inter_preimage
    (fun z hz => (contDiffAt_rotTwo_sph hs hz).continuousAt.continuousWithinAt) hDo
    (hVo.union isOpen_ball)
  have hFW : ∀ z ∈ W, F z = Q (σ.rotTwo z) := by
    intro z hz
    by_cases hb : ‖σ.rotTwo z - c‖ < r
    · simp only [hFdef, hb, ↓reduceIte]
    · rw [hF1 z (not_lt.1 hb)]
      rcases hz.2 with hV | hb'
      · rw [hQV hV]
        change σ.sphPreFold z = σ.sphPreFold (σ.sphChartTwo (σ.rotTwo z))
        rw [sphChartTwo_rotTwo hs hz.1]
      · exact absurd (by rwa [mem_ball, dist_eq_norm] at hb') hb
  set G' := G ∩ {z | r < ‖σ.rotTwo z - c‖} with hG'
  have hG'o : IsOpen G' := hGo.inter (isOpen_rotTwo_far_sph hs c r)
  have hFG : ∀ z ∈ G', F z = σ.sphPreFold z := fun z hz => hF1 z hz.2.le
  have hevW : ∀ z ∈ W, F =ᶠ[𝓝 z] fun u => Q (σ.rotTwo u) := fun z hz =>
    Filter.eventually_of_mem (hWo.mem_nhds hz) hFW
  have hevG : ∀ z ∈ G', F =ᶠ[𝓝 z] σ.sphPreFold := fun z hz =>
    Filter.eventually_of_mem (hG'o.mem_nhds hz) hFG
  set U := (W ∪ G') ∩ {z | z ≠ 0} with hU
  have hUo : IsOpen U := (hWo.union hG'o).inter isOpen_ne
  refine ⟨F, U, hUo, fun h => h.2 rfl, ?_, ?_, ?_, ?_, hF1, ?_, ?_⟩
  · rintro z ⟨hzT, hz0⟩
    have hv2 := one_add_vertexTwo_ne_sph hs hzT
    refine ⟨?_, hz0⟩
    rcases lt_trichotomy ‖σ.rotTwo z - c‖ r with h | h | h
    · exact Or.inl ⟨hv2, Or.inr (by rwa [mem_ball, dist_eq_norm])⟩
    · exact Or.inl ⟨hv2, Or.inl (hsV (by rwa [mem_sphere_iff_norm]))⟩
    · exact Or.inr ⟨hcover z hzT hz0 (by linarith), h⟩
  · intro z h0 hg h
    exact ⟨Or.inr ⟨hg, h⟩, h0⟩
  · intro z hz
    rcases hz.1 with h | h
    · exact ((hQs.contDiffAt.comp z (contDiffAt_rotTwo_sph hs h.1)).congr_of_eventuallyEq
        (hevW z h)).contDiffWithinAt
    · exact ((hGsm z h.1).congr_of_eventuallyEq (hevG z h)).contDiffWithinAt
  · intro z hz h1 h2
    rcases hz.1 with h | h
    · rw [(hevW z h).fderiv_eq]
      rw [show (fun u => Q (σ.rotTwo u)) = Q ∘ σ.rotTwo from rfl,
        det_fderiv_comp_sph ((hQs.contDiffAt).differentiableAt (by simp))
          ((contDiffAt_rotTwo_sph hs h.1).differentiableAt (by simp))]
      exact mul_pos (hQpos _) (det_fderiv_rotTwo_pos_sph hs h.1)
    · rw [(hevG z h).fderiv_eq]
      exact hGdet z h.1 h1 h2
  · have hFQ : ∀ z, ‖σ.rotTwo z - c‖ < r → F z = Q (σ.rotTwo z) := fun z hz => by
      simp only [hFdef, hz, ↓reduceIte]
    have hback : ∀ z ∈ σ.triangle, σ.sphChartTwo (σ.rotTwo z) = z := fun z hz =>
      sphChartTwo_rotTwo hs (one_add_vertexTwo_ne_sph hs hz)
    have key : ∀ a b : ℂ, a ∈ σ.triangle \ {0} → b ∈ σ.triangle \ {0} →
        ‖σ.rotTwo a - c‖ < r → r ≤ ‖σ.rotTwo b - c‖ → F a = F b → False := by
      intro a b ha hb hna hnb hab
      rw [hFQ a hna, hF1 b hnb] at hab
      rcases hnb.lt_or_eq with hlt | heq
      · have hbO : σ.rotTwo b ∈ O := by
          refine ⟨chartRegion_of_mem_triangle_sph hs hb.1, fun h => hb.2 ?_, hlt⟩
          rw [← hback b hb.1, h, hψ3]
          rfl
        have hbS : σ.sphPreFold b ∈ S := by
          refine Or.inl ⟨σ.rotTwo b, hbO, ?_⟩
          change σ.sphPreFold (σ.sphChartTwo (σ.rotTwo b)) = _
          rw [hback b hb.1]
        rw [← hab] at hbS
        exact disjoint_left.1 (hQc S hSc hSb hSd) hbS
          ⟨σ.rotTwo a, by rwa [mem_ball, dist_eq_norm], rfl⟩
      · have hbV : σ.rotTwo b ∈ V := hsV (by rw [mem_sphere_iff_norm]; exact heq.symm)
        have hEb : σ.sphPreFold b = Q (σ.rotTwo b) := by
          rw [hQV hbV]
          change σ.sphPreFold b = σ.sphPreFold (σ.sphChartTwo (σ.rotTwo b))
          rw [hback b hb.1]
        rw [hEb] at hab
        have := hQi hab
        rw [this] at hna
        linarith
    intro z hz z' hz' heq
    by_cases h1 : ‖σ.rotTwo z - c‖ < r <;> by_cases h2 : ‖σ.rotTwo z' - c‖ < r
    · rw [hFQ z h1, hFQ z' h2] at heq
      have := hQi heq
      rw [← hback z hz.1, ← hback z' hz'.1, this]
    · exact (key z z' hz hz' h1 (not_lt.1 h2) heq).elim
    · exact (key z' z hz' hz h2 (not_lt.1 h1) heq.symm).elim
    · rw [hF1 z (not_lt.1 h1), hF1 z' (not_lt.1 h2)] at heq
      exact hinj hz hz' heq
  · rintro z ⟨hzT, hz0⟩
    by_cases h : ‖σ.rotTwo z - c‖ < r
    · have e : F z = Q (σ.rotTwo z) := by simp only [hFdef, h, ↓reduceIte]
      rw [e]
      have := hQball ⟨σ.rotTwo z, by rwa [mem_ball, dist_eq_norm], rfl⟩
      exact ⟨this.1, this.2.le⟩
    · rw [hF1 z (not_lt.1 h)]
      exact ⟨norm_sphPreFold_lt hs hzT hz0, im_sphPreFold_nonneg hs hzT hz0⟩

theorem sphCore_consts : 0 < σ.sphCoreMargin ∧ σ.sphCoreMargin < σ.sphCoreRadius := by
  have := sphScale_pos hs
  unfold sphCoreMargin sphCoreRadius sphLensWidth
  constructor <;> linarith

theorem exists_sphFoldCore {G : Set ℂ} (hGo : IsOpen G)
    (hGsm : ∀ z ∈ G, ContDiffAt ℝ ∞ σ.sphPreFold z)
    (hGdet : ∀ z ∈ G, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ σ.sphPreFold z).det)
    (hcover : ∀ z ∈ σ.triangle, z ≠ 0 →
      σ.sphCoreRadius - σ.sphCoreMargin ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → z ∈ G)
    (hin : ∀ ζ : ℂ, ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin →
      ∀ i, 0 < σ.wallSide i (σ.sphChartTwo ζ))
    (hinj : InjOn σ.sphPreFold (σ.triangle \ {0})) :
    ∃ F : ℂ → ℂ, ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∉ U ∧ σ.triangle \ {0} ⊆ U ∧
      (∀ z, z ≠ 0 → z ∈ G → σ.sphCoreRadius < ‖σ.rotTwo z - σ.sphCoreCenter‖ → z ∈ U) ∧
      ContDiffOn ℝ ∞ F U ∧
      (∀ z ∈ U, z ≠ σ.vertexOne → z ≠ σ.vertexTwo → 0 < (fderiv ℝ F z).det) ∧
      (∀ z, σ.sphCoreRadius ≤ ‖σ.rotTwo z - σ.sphCoreCenter‖ → F z = σ.sphPreFold z) ∧
      InjOn F (σ.triangle \ {0}) ∧ MapsTo F (σ.triangle \ {0}) basePlusSeven :=
  exists_sphFoldCore_of hs (sphCore_consts hs).1 (sphCore_consts hs).2 hGo hGsm hGdet hcover hin
    hinj

end Spherical

end CompactShape

end GC.Seifert
