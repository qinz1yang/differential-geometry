import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphLayout
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphWalls

/-!
# The vertex discs of a spherical closed triangle fold

Lane B3d2 (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §5, with
review 32 §6.1; the spherical analogue of B3c's `ClosedTriangleGeometryHypDiscs`). For a
spherical datum `K` (triangle `σ` in the stereographic chart, `v₃ = 0`, `v₂ = t₂ > 0`,
`v₁ = t₁ e^{iθ₃}`, `0 < tⱼ ≤ 1`) the margin `μ = min (t₁ sin θ₃, t₂ sin θ₃, t₂ sin θ₂)` bounds
the side functions of the walls opposite the vertices from below at the vertices, and the radii
`radOne`, `radTwo`, `radThree` are at most `ρ₀ = μ/16`, the apex radii of `D` and `1/2`.
The vertex discs are CF's apex discs with their denominator condition (`discOneR`, `discTwoR`
of the interface `SphLayout`). With `w = discV v z` one has `(z - v)(1 - v̄ w) = w (1 + |v|²)`,
so for `‖v‖ ≤ 1`, `‖w‖ ≤ 1/2` the point lies within `4 ‖w‖` of `v` (`norm_sub_le_four`): the
inner discs lie in Euclidean discs of radius `μ/4`. This gives the margins `3μ/4 < Im z` on the
disc of `v₁`, `3μ/4 < w₁` on the disc of `v₂`, `3μ/4 < w₂` on the disc of `0`, the positivity of
`Re (1 + v̄ⱼ z)` on the inner discs (slit plane), the nonvanishing of the recentring
denominators, the pairwise disjointness of the discs and of the mirror disc of `v₁`. Finally a
point of a vertex disc whose rotated coordinate lies in the closed sector `[0, θⱼ]` is in the
triangle (`discOne_sector`, …), and conversely triangle points of a disc lie in the closed
sector (`triangle_sector_one`, …).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

namespace Lay

section Constants

variable (K : SphDatum)

def sphMu : ℝ := min (K.σ.sphTOneThree * Real.sin K.σ.θ₃)
  (min (K.σ.sphTTwoThree * Real.sin K.σ.θ₃) (K.σ.sphTTwoThree * Real.sin K.σ.θ₂))

def rhoZero : ℝ := sphMu K / 16

def radOne : ℝ := min (min (rhoZero K) (K.D.apexRadius 0)) (1 / 2)

def radTwo : ℝ := min (min (rhoZero K) (K.D.apexRadius 1)) (1 / 2)

def radThree : ℝ := min (min (rhoZero K) (K.D.apexRadius 2)) (1 / 2)

theorem tOne_pos : 0 < K.σ.sphTOneThree := CompactShape.tOneThree_pos_sph K.hσ

theorem tTwo_pos : 0 < K.σ.sphTTwoThree := CompactShape.tTwoThree_pos_sph K.hσ

theorem tOne_le : K.σ.sphTOneThree ≤ 1 := CompactShape.tOneThree_le_one_sph K.hσ

theorem tTwo_le : K.σ.sphTTwoThree ≤ 1 := CompactShape.tTwoThree_le_one_sph K.hσ

theorem sphMu_pos : 0 < sphMu K := by
  have := tOne_pos K
  have := tTwo_pos K
  have := K.σ.sin_θ₂_pos
  have := K.σ.sin_θ₃_pos
  unfold sphMu
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

theorem sphMu_le_one : sphMu K ≤ K.σ.sphTOneThree * Real.sin K.σ.θ₃ := min_le_left _ _

theorem sphMu_le_two : sphMu K ≤ K.σ.sphTTwoThree * Real.sin K.σ.θ₃ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem sphMu_le_three : sphMu K ≤ K.σ.sphTTwoThree * Real.sin K.σ.θ₂ :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem sphMu_le : sphMu K ≤ 1 := by
  have := sphMu_le_three K
  have := mul_le_mul_of_nonneg_right (tTwo_le K) K.σ.sin_θ₂_pos.le
  have := Real.sin_le_one K.σ.θ₂
  linarith

theorem rhoZero_pos : 0 < rhoZero K := by unfold rhoZero; linarith [sphMu_pos K]

theorem radOne_pos : 0 < radOne K :=
  lt_min (lt_min (rhoZero_pos K) (K.D.apexRadius_pos 0)) (by norm_num)

theorem radTwo_pos : 0 < radTwo K :=
  lt_min (lt_min (rhoZero_pos K) (K.D.apexRadius_pos 1)) (by norm_num)

theorem radThree_pos : 0 < radThree K :=
  lt_min (lt_min (rhoZero_pos K) (K.D.apexRadius_pos 2)) (by norm_num)

theorem radOne_le_rho : radOne K ≤ rhoZero K := (min_le_left _ _).trans (min_le_left _ _)

theorem radTwo_le_rho : radTwo K ≤ rhoZero K := (min_le_left _ _).trans (min_le_left _ _)

theorem radThree_le_rho : radThree K ≤ rhoZero K := (min_le_left _ _).trans (min_le_left _ _)

theorem radOne_le_apex : radOne K ≤ K.D.apexRadius 0 := (min_le_left _ _).trans (min_le_right _ _)

theorem radTwo_le_apex : radTwo K ≤ K.D.apexRadius 1 := (min_le_left _ _).trans (min_le_right _ _)

theorem radThree_le_apex : radThree K ≤ K.D.apexRadius 2 :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem radOne_le_half : radOne K ≤ 1 / 2 := min_le_right _ _

theorem radTwo_le_half : radTwo K ≤ 1 / 2 := min_le_right _ _

theorem radThree_le_half : radThree K ≤ 1 / 2 := min_le_right _ _

end Constants

section Generic

theorem norm_sub_le_four {v z : ℂ} (hv : ‖v‖ ≤ 1) (hz : 1 + conj v * z ≠ 0)
    (hw : ‖discV v z‖ ≤ 1 / 2) : ‖z - v‖ ≤ 4 * ‖discV v z‖ := by
  set w := discV v z with hwdef
  have h : w * (1 + conj v * z) = z - v := by
    rw [hwdef, discV, div_mul_cancel₀ _ hz]
  have e : (z - v) * (1 - conj v * w) = w * (1 + conj v * v) := by
    linear_combination (-1 : ℂ) * h
  have h1 : ‖1 + conj v * v‖ ≤ 2 := by
    calc ‖1 + conj v * v‖ ≤ ‖(1 : ℂ)‖ + ‖conj v * v‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg v]
  have h2 : 1 / 2 ≤ ‖1 - conj v * w‖ := by
    have := norm_sub_norm_le (1 : ℂ) (conj v * w)
    rw [norm_one, norm_mul, Complex.norm_conj] at this
    nlinarith [norm_nonneg v, norm_nonneg w]
  have h3 := congrArg norm e
  rw [norm_mul, norm_mul] at h3
  have := mul_le_mul_of_nonneg_left h2 (norm_nonneg (z - v))
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
  linarith

theorem re_mul_ge (c z u : ℂ) : (c * u).re - ‖c‖ * ‖z - u‖ ≤ (c * z).re := by
  have h : (c * z).re = (c * u).re + (c * (z - u)).re := by
    rw [← add_re]
    congr 1
    ring
  have h2 := abs_re_le_norm (c * (z - u))
  rw [norm_mul] at h2
  have := (abs_le.mp h2).1
  linarith

theorem one_sub_ne_of_norm_lt {a : ℂ} (h : ‖a‖ < 1) : 1 - a ≠ 0 := by
  intro h0
  have ha : a = 1 := by linear_combination -h0
  rw [ha, norm_one] at h
  exact lt_irrefl _ h

theorem abs_wallSide_one_sub_le (σ : CompactShape) (z w : ℂ) :
    |σ.wallSide 1 z - σ.wallSide 1 w| ≤ ‖z - w‖ := by
  change |(exp ((σ.θ₃ : ℂ) * I) * conj z).im - (exp ((σ.θ₃ : ℂ) * I) * conj w).im| ≤ _
  rw [← sub_im, ← mul_sub, ← map_sub]
  refine (abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]

theorem sides_of_arg {w : ℂ} {θ : ℝ} (hθ : θ ≤ Real.pi) (h0 : 0 ≤ arg w) (h1 : arg w ≤ θ) :
    0 ≤ w.im ∧ 0 ≤ (exp ((θ : ℂ) * I) * conj w).im := by
  refine ⟨arg_nonneg_iff.mp h0, ?_⟩
  rw [CompactShape.im_exp_mul_conj_sph, ← Complex.norm_mul_cos_arg w,
    ← Complex.norm_mul_sin_arg w]
  have e : Real.sin θ * (‖w‖ * Real.cos (arg w)) - Real.cos θ * (‖w‖ * Real.sin (arg w)) =
      ‖w‖ * Real.sin (θ - arg w) := by
    rw [Real.sin_sub]
    ring
  rw [e]
  exact mul_nonneg (norm_nonneg _)
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))

theorem im_exp_neg_mul (θ : ℝ) (w : ℂ) :
    (exp (-((θ : ℂ) * I)) * w).im = -(exp ((θ : ℂ) * I) * conj w).im := by
  have h : exp (-((θ : ℂ) * I)) * w = conj (exp ((θ : ℂ) * I) * conj w) := by
    rw [map_mul, conj_conj, CompactShape.conj_exp_ofReal_mul_I_sph]
  rw [h, conj_im]

theorem arg_mem_Icc_of_sides' {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hw : w ≠ 0)
    (h1 : 0 ≤ w.im) (h2 : 0 ≤ (exp ((θ : ℂ) * I) * conj w).im) : 0 ≤ arg w ∧ arg w ≤ θ := by
  refine ⟨arg_nonneg_iff.mpr h1, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hπ := arg_le_pi w
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [CompactShape.im_exp_mul_conj_sph, ← Complex.norm_mul_cos_arg w,
    ← Complex.norm_mul_sin_arg w] at h2
  have e : Real.sin θ * (‖w‖ * Real.cos (arg w)) - Real.cos θ * (‖w‖ * Real.sin (arg w)) =
      -(‖w‖ * Real.sin (arg w - θ)) := by
    rw [Real.sin_sub]
    ring
  rw [e] at h2
  have hs : 0 < Real.sin (arg w - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  nlinarith [mul_pos hr hs]

end Generic

variable (K : SphDatum)

section Norms

theorem norm_rotOne_eq (z : ℂ) : ‖K.σ.rotOne z‖ = ‖discV K.σ.vertexOne z‖ := by
  have h : ‖exp (-((K.σ.θ₃ : ℂ) * I))‖ = 1 := by
    rw [← neg_mul, ← ofReal_neg, norm_exp_ofReal_mul_I]
  rw [rotOne_eq_of_sph K.hσ, norm_mul, norm_neg, h, one_mul]

theorem norm_rotTwo_eq (z : ℂ) : ‖K.σ.rotTwo z‖ = ‖discV K.σ.vertexTwo z‖ := by
  rw [rotTwo_eq_of_sph K.hσ, norm_mul, norm_neg, norm_exp_ofReal_mul_I, one_mul]

theorem norm_vertexOne : ‖K.σ.vertexOne‖ = K.σ.sphTOneThree :=
  CompactShape.norm_vertexOne_sph K.hσ

theorem norm_vertexTwo : ‖K.σ.vertexTwo‖ = K.σ.sphTTwoThree :=
  CompactShape.norm_vertexTwo_sph K.hσ

theorem vertexOne_im : K.σ.vertexOne.im = K.σ.sphTOneThree * Real.sin K.σ.θ₃ := by
  rw [K.σ.vertexOne_eq_ray, K.σ.ray_im]
  rfl

theorem norm_sub_vertexOne_lt {z : ℂ} (hz : z ∈ discOneR K (radOne K)) :
    ‖z - K.σ.vertexOne‖ < sphMu K / 4 := by
  have hn : ‖discV K.σ.vertexOne z‖ < radOne K := by rw [← norm_rotOne_eq]; exact hz.2
  have h := norm_sub_le_four (by rw [norm_vertexOne]; exact tOne_le K) hz.1
    (hn.le.trans (radOne_le_half K))
  have := radOne_le_rho K
  unfold rhoZero at this
  linarith

theorem norm_sub_vertexTwo_lt {z : ℂ} (hz : z ∈ discTwoR K (radTwo K)) :
    ‖z - K.σ.vertexTwo‖ < sphMu K / 4 := by
  have hn : ‖discV K.σ.vertexTwo z‖ < radTwo K := by rw [← norm_rotTwo_eq]; exact hz.2
  have h := norm_sub_le_four (by rw [norm_vertexTwo]; exact tTwo_le K) hz.1
    (hn.le.trans (radTwo_le_half K))
  have := radTwo_le_rho K
  unfold rhoZero at this
  linarith

theorem norm_lt_of_discThree {z : ℂ} (hz : z ∈ discThreeR (radThree K)) :
    ‖z‖ < sphMu K / 16 :=
  lt_of_lt_of_le hz (radThree_le_rho K)

end Norms

section Margins

theorem im_gt_of_mem_discOne {z : ℂ} (hz : z ∈ discOneR K (radOne K)) :
    3 * sphMu K / 4 < z.im := by
  have h := abs_im_le_norm (z - K.σ.vertexOne)
  rw [sub_im, vertexOne_im] at h
  have h2 := norm_sub_vertexOne_lt K hz
  have := sphMu_le_one K
  have := (abs_lt.mp (h.trans_lt h2)).1
  linarith

theorem wallSide_one_gt_of_mem_discTwo {z : ℂ} (hz : z ∈ discTwoR K (radTwo K)) :
    3 * sphMu K / 4 < K.σ.wallSide 1 z := by
  have h := abs_wallSide_one_sub_le K.σ z K.σ.vertexTwo
  have hv : K.σ.wallSide 1 K.σ.vertexTwo = K.σ.sphTTwoThree * Real.sin K.σ.θ₃ := by
    rw [K.σ.wallSide_one_eq, K.σ.vertexTwo_eq_real, ofReal_re, ofReal_im]
    change Real.sin K.σ.θ₃ * K.σ.sphTTwoThree - Real.cos K.σ.θ₃ * 0 = _
    ring
  rw [hv] at h
  have h2 := norm_sub_vertexTwo_lt K hz
  have := sphMu_le_two K
  have := (abs_lt.mp (h.trans_lt h2)).1
  linarith

theorem wallSide_two_ge (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    K.σ.sphTTwoThree * Real.sin K.σ.θ₂ - 4 * ‖z‖ ≤ K.σ.wallSide 2 z := by
  rw [CompactShape.wallSide_two_apply_sph K.hσ]
  have ht0 := tTwo_pos K
  have ht1 := tTwo_le K
  have hs0 : 0 ≤ Real.sin K.σ.θ₂ := K.σ.sin_θ₂_pos.le
  have hs1 : Real.sin K.σ.θ₂ ≤ 1 := Real.sin_le_one _
  have hc0 : 0 ≤ Real.cos K.σ.θ₂ := K.σ.cos_θ₂_nonneg
  have hc1 : Real.cos K.σ.θ₂ ≤ 1 := Real.cos_le_one _
  set t := K.σ.sphTTwoThree
  set s := Real.sin K.σ.θ₂
  set c := Real.cos K.σ.θ₂
  have hre := abs_le.mp (abs_re_le_norm z)
  have him := abs_le.mp (abs_im_le_norm z)
  have hn := norm_nonneg z
  have st : s * t ≤ 1 := by nlinarith
  have a1 : s * t * ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by
    have := mul_le_mul_of_nonneg_right st (sq_nonneg ‖z‖)
    have := mul_le_mul_of_nonneg_left hz hn
    nlinarith
  have hk0 : 0 ≤ s * (1 - t ^ 2) := mul_nonneg hs0 (by nlinarith)
  have hk1 : s * (1 - t ^ 2) ≤ 1 := by nlinarith
  have a2 : s * (1 - t ^ 2) * z.re ≤ ‖z‖ := by
    have := mul_le_mul_of_nonneg_left hre.2 hk0
    have := mul_le_of_le_one_left hn hk1
    linarith
  have hk0' : 0 ≤ c * (1 + t ^ 2) := mul_nonneg hc0 (by positivity)
  have hk1' : c * (1 + t ^ 2) ≤ 2 := by nlinarith
  have a3 : c * (1 + t ^ 2) * z.im ≤ 2 * ‖z‖ := by
    have := mul_le_mul_of_nonneg_left him.2 hk0'
    have := mul_le_mul_of_nonneg_right hk1' hn
    linarith
  nlinarith

theorem wallSide_two_gt_of_mem_discThree {z : ℂ} (hz : z ∈ discThreeR (radThree K)) :
    3 * sphMu K / 4 < K.σ.wallSide 2 z := by
  have h1 := norm_lt_of_discThree K hz
  have h := wallSide_two_ge K z ((le_of_lt hz).trans (radThree_le_half K))
  have := sphMu_le_three K
  have := sphMu_pos K
  linarith

theorem re_one_add_conj_vertexOne_of_discOne {z : ℂ} (hz : z ∈ discOneR K (radOne K)) :
    0 < (1 + conj K.σ.vertexOne * z).re := by
  have h := re_mul_ge (conj K.σ.vertexOne) z K.σ.vertexOne
  have h0 := CompactShape.conj_vertexOne_mul_re_nonneg_sph K.hσ
    (CompactShape.vertexOne_mem_triangle_sph K.hσ)
  rw [Complex.norm_conj, norm_vertexOne] at h
  have h2 := norm_sub_vertexOne_lt K hz
  have := sphMu_le K
  have := tOne_le K
  have := tOne_pos K
  have : K.σ.sphTOneThree * ‖z - K.σ.vertexOne‖ ≤ ‖z - K.σ.vertexOne‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (tOne_le K)
  rw [add_re, one_re]
  linarith

theorem re_one_add_vertexTwo_of_discOne {z : ℂ} (hz : z ∈ discOneR K (radOne K)) :
    0 < (1 + conj K.σ.vertexTwo * z).re := by
  have h := re_mul_ge (conj K.σ.vertexTwo) z K.σ.vertexOne
  have h0 := CompactShape.vertexTwo_mul_re_nonneg_sph K.hσ
    (CompactShape.vertexOne_mem_triangle_sph K.hσ)
  rw [Complex.norm_conj, norm_vertexTwo] at h
  have h2 := norm_sub_vertexOne_lt K hz
  have := sphMu_le K
  have : K.σ.sphTTwoThree * ‖z - K.σ.vertexOne‖ ≤ ‖z - K.σ.vertexOne‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (tTwo_le K)
  rw [add_re, one_re]
  linarith

theorem re_one_add_vertexTwo_of_discTwo {z : ℂ} (hz : z ∈ discTwoR K (radTwo K)) :
    0 < (1 + conj K.σ.vertexTwo * z).re := by
  have h := re_mul_ge (conj K.σ.vertexTwo) z K.σ.vertexTwo
  have h0 := CompactShape.vertexTwo_mul_re_nonneg_sph K.hσ
    (CompactShape.vertexTwo_mem_triangle_sph K.hσ)
  rw [Complex.norm_conj, norm_vertexTwo] at h
  have h2 := norm_sub_vertexTwo_lt K hz
  have := sphMu_le K
  have : K.σ.sphTTwoThree * ‖z - K.σ.vertexTwo‖ ≤ ‖z - K.σ.vertexTwo‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (tTwo_le K)
  rw [add_re, one_re]
  linarith

end Margins

section Fields

theorem discOne_slit : ∀ z ∈ discOneR K (radOne K), 1 + conj K.σ.vertexOne * z ∈ slitPlane :=
  fun _ hz => mem_slitPlane_iff.mpr (Or.inl (re_one_add_conj_vertexOne_of_discOne K hz))

theorem discTwo_slit : ∀ z ∈ discTwoR K (radTwo K), 1 + conj K.σ.vertexTwo * z ∈ slitPlane :=
  fun _ hz => mem_slitPlane_iff.mpr (Or.inl (re_one_add_vertexTwo_of_discTwo K hz))

theorem den_ne {v z : ℂ} {r : ℝ} (hv : ‖v‖ ≤ 1) (hr : r ≤ 1 / 2) (hz : ‖discV v z‖ < r)
    (θ : ℝ) : 1 - conj v * (exp (θ * I) * discV v z) ≠ 0 := by
  refine one_sub_ne_of_norm_lt ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_exp_ofReal_mul_I, one_mul]
  have := mul_le_of_le_one_left (norm_nonneg (discV v z)) hv
  linarith

theorem discOne_den : ∀ z ∈ discOneR K (radOne K), ∀ θ : ℝ,
    1 - conj K.σ.vertexOne * (exp (θ * I) * discV K.σ.vertexOne z) ≠ 0 :=
  fun _ hz θ => den_ne (by rw [norm_vertexOne]; exact tOne_le K) (radOne_le_half K)
    (by rw [← norm_rotOne_eq]; exact hz.2) θ

theorem discTwo_den : ∀ z ∈ discTwoR K (radTwo K), ∀ θ : ℝ,
    1 - conj K.σ.vertexTwo * (exp (θ * I) * discV K.σ.vertexTwo z) ≠ 0 :=
  fun _ hz θ => den_ne (by rw [norm_vertexTwo]; exact tTwo_le K) (radTwo_le_half K)
    (by rw [← norm_rotTwo_eq]; exact hz.2) θ

theorem discOne_im_pos : ∀ z ∈ discOneR K (radOne K), 0 < z.im := fun _ hz => by
  have := im_gt_of_mem_discOne K hz
  have := sphMu_pos K
  linarith

theorem norm_sub_lt_of_disc {a b : ℂ} {r s d : ℝ} {z : ℂ} (hz : ‖z - a‖ < r) (hw : ‖z - b‖ < s)
    (hd : d ≤ ‖a - b‖) (hrs : r + s ≤ d) : False := by
  have := norm_sub_le_norm_sub_add_norm_sub a z b
  rw [norm_sub_rev a z] at this
  linarith

theorem disjoint_one_two : Disjoint (discOneR K (radOne K)) (discTwoR K (radTwo K)) := by
  rw [Set.disjoint_left]
  intro z h1 h2
  have hd : K.σ.sphTOneThree * Real.sin K.σ.θ₃ ≤ ‖K.σ.vertexOne - K.σ.vertexTwo‖ := by
    have := abs_im_le_norm (K.σ.vertexOne - K.σ.vertexTwo)
    rw [sub_im, vertexOne_im, K.σ.vertexTwo_eq_real, ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have := sphMu_le_one K
  have := sphMu_pos K
  exact norm_sub_lt_of_disc (norm_sub_vertexOne_lt K h1) (norm_sub_vertexTwo_lt K h2) hd
    (by linarith)

theorem disjoint_one_three : Disjoint (discOneR K (radOne K)) (discThreeR (radThree K)) := by
  rw [Set.disjoint_left]
  intro z h1 h3
  have h3' : ‖z - 0‖ < sphMu K / 16 := by rw [sub_zero]; exact norm_lt_of_discThree K h3
  have hd : K.σ.sphTOneThree * Real.sin K.σ.θ₃ ≤ ‖K.σ.vertexOne - 0‖ := by
    rw [sub_zero, ← vertexOne_im]
    exact (le_abs_self _).trans (abs_im_le_norm _)
  have := sphMu_le_one K
  have := sphMu_pos K
  exact norm_sub_lt_of_disc (norm_sub_vertexOne_lt K h1) h3' hd (by linarith)

theorem disjoint_two_three : Disjoint (discTwoR K (radTwo K)) (discThreeR (radThree K)) := by
  rw [Set.disjoint_left]
  intro z h2 h3
  have h3' : ‖z - 0‖ < sphMu K / 16 := by rw [sub_zero]; exact norm_lt_of_discThree K h3
  have hd : K.σ.sphTTwoThree * Real.sin K.σ.θ₃ ≤ ‖K.σ.vertexTwo - 0‖ := by
    rw [sub_zero, norm_vertexTwo]
    exact mul_le_of_le_one_right (tTwo_pos K).le (Real.sin_le_one _)
  have := sphMu_le_two K
  have := sphMu_pos K
  exact norm_sub_lt_of_disc (norm_sub_vertexTwo_lt K h2) h3' hd (by linarith)

theorem conj_mem_discTwoR {r : ℝ} {z : ℂ} (hz : z ∈ discTwoR K r) : conj z ∈ discTwoR K r := by
  have hv := conj_vertexTwo_sph K.σ
  refine ⟨?_, ?_⟩
  · have h : 1 + conj K.σ.vertexTwo * conj z = conj (1 + conj K.σ.vertexTwo * z) := by
      rw [map_add, map_one, map_mul, conj_conj, hv]
    rw [h]
    exact (map_ne_zero _).2 hz.1
  · rw [rotTwo_conj_sph K.hσ, norm_mul, norm_conj]
    have : ‖exp (2 * (K.σ.θ₂ : ℂ) * I)‖ = 1 := by
      rw [show 2 * (K.σ.θ₂ : ℂ) * I = ((2 * K.σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_ofReal_mul_I]
    rw [this, one_mul]
    exact hz.2

theorem conj_mem_discThreeR {r : ℝ} {z : ℂ} (hz : z ∈ discThreeR r) : conj z ∈ discThreeR r := by
  change ‖conj z‖ < r
  rw [norm_conj]
  exact hz

theorem disjoint_two_mirror :
    ∀ z ∈ discTwoR K (radTwo K), conj z ∉ discOneR K (radOne K) := fun _ hz h1 =>
  Set.disjoint_left.mp (disjoint_one_two K) h1 (conj_mem_discTwoR K hz)

theorem disjoint_three_mirror :
    ∀ z ∈ discThreeR (radThree K), conj z ∉ discOneR K (radOne K) := fun _ hz h1 =>
  Set.disjoint_left.mp (disjoint_one_three K) h1 (conj_mem_discThreeR hz)

end Fields

section Sectors

theorem normSq_pos_of_re {w : ℂ} (h : 0 < w.re) : 0 < normSq w :=
  normSq_pos.mpr fun h0 => by rw [h0, zero_re] at h; exact lt_irrefl _ h

theorem discOne_sector : ∀ z ∈ discOneR K (radOne K), 0 ≤ arg (K.σ.rotOne z) →
    arg (K.σ.rotOne z) ≤ K.σ.θ₁ → z ∈ K.σ.triangle := by
  intro z hz h0 h1
  obtain ⟨a, b⟩ := sides_of_arg (by linarith [K.σ.θ₁_le, Real.pi_pos]) h0 h1
  have hp1 := normSq_pos_of_re (re_one_add_conj_vertexOne_of_discOne K hz)
  have hr2 := re_one_add_vertexTwo_of_discOne K hz
  refine (CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨?_, ?_, ?_⟩
  · exact (discOne_im_pos K z hz).le
  · have e := CompactShape.wallSide_one_eq_rotOne_sph K.hσ z
    have ht : 0 < 1 + K.σ.sphTOneThree ^ 2 := by positivity
    by_contra hn
    rw [not_le] at hn
    nlinarith [mul_nonneg a hp1.le]
  · have e := CompactShape.wallSide_two_eq_rotOne_sph K.hσ hz.1
      (fun h => by rw [h, zero_re] at hr2; exact lt_irrefl _ hr2)
    have ht : 0 < 1 + K.σ.sphTOneTwo ^ 2 := by positivity
    have him : 0 ≤ (K.σ.rotTwo z).im := by
      by_contra hn
      rw [not_le] at hn
      nlinarith [mul_nonneg b (normSq_nonneg (1 + (K.σ.sphTOneTwo : ℂ) * K.σ.rotTwo z))]
    rw [CompactShape.wallSide_two_eq_sph K.hσ]
    exact mul_nonneg him (normSq_nonneg _)

theorem discTwo_sector : ∀ z ∈ discTwoR K (radTwo K), 0 ≤ arg (K.σ.rotTwo z) →
    arg (K.σ.rotTwo z) ≤ K.σ.θ₂ → z ∈ K.σ.triangle := by
  intro z hz h0 h1
  obtain ⟨a, b⟩ := sides_of_arg (by linarith [K.σ.θ₂_le, Real.pi_pos]) h0 h1
  refine (CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨?_, ?_, ?_⟩
  · have e := CompactShape.wallSide_zero_eq_rotTwo_sph K.hσ z
    have ht : 0 < 1 + K.σ.sphTTwoThree ^ 2 := by positivity
    by_contra hn
    rw [not_le] at hn
    nlinarith [mul_nonneg b (normSq_nonneg (1 + K.σ.vertexTwo * z))]
  · have := wallSide_one_gt_of_mem_discTwo K hz
    have := sphMu_pos K
    linarith
  · rw [CompactShape.wallSide_two_eq_sph K.hσ]
    exact mul_nonneg a (normSq_nonneg _)

theorem discThree_sector : ∀ z ∈ discThreeR (radThree K), 0 ≤ arg z → arg z ≤ K.σ.θ₃ →
    z ∈ K.σ.triangle := by
  intro z hz h0 h1
  obtain ⟨a, b⟩ := sides_of_arg (by linarith [K.σ.θ₃_le, Real.pi_pos]) h0 h1
  refine (CompactShape.mem_triangle_iff_sph K.hσ).2 ⟨a, b, ?_⟩
  have := wallSide_two_gt_of_mem_discThree K hz
  have := sphMu_pos K
  linarith

theorem rotOne_ne_zero {z : ℂ} (hd : 1 + conj K.σ.vertexOne * z ≠ 0) (h1 : z ≠ K.σ.vertexOne) :
    K.σ.rotOne z ≠ 0 := by
  intro h
  apply h1
  rw [rotOne_eq_of_sph K.hσ, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (neg_ne_zero.2 (Complex.exp_ne_zero _))
  · rw [discV, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hd

theorem rotTwo_ne_zero {z : ℂ} (hd : 1 + conj K.σ.vertexTwo * z ≠ 0) (h2 : z ≠ K.σ.vertexTwo) :
    K.σ.rotTwo z ≠ 0 := by
  intro h
  apply h2
  rw [rotTwo_eq_of_sph K.hσ, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (neg_ne_zero.2 (Complex.exp_ne_zero _))
  · rw [discV, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hd

theorem triangle_sector_one : ∀ z ∈ K.σ.triangle, z ∈ discOneR K (radOne K) →
    z ≠ K.σ.vertexOne → 0 ≤ arg (K.σ.rotOne z) ∧ arg (K.σ.rotOne z) ≤ K.σ.θ₁ := by
  intro z hT hz h1
  obtain ⟨a, b⟩ := CompactShape.sector_one_sph K.hσ hT
  exact arg_mem_Icc_of_sides' K.σ.θ₁_pos (rotOne_ne_zero K hz.1 h1) a b

theorem triangle_sector_two : ∀ z ∈ K.σ.triangle, z ∈ discTwoR K (radTwo K) →
    z ≠ K.σ.vertexTwo → 0 ≤ arg (K.σ.rotTwo z) ∧ arg (K.σ.rotTwo z) ≤ K.σ.θ₂ := by
  intro z hT hz h2
  obtain ⟨a, b⟩ := CompactShape.sector_two_sph K.hσ hT
  exact arg_mem_Icc_of_sides' K.σ.θ₂_pos (rotTwo_ne_zero K hz.1 h2) a b

theorem triangle_sector_three : ∀ z ∈ K.σ.triangle, z ∈ discThreeR (radThree K) → z ≠ 0 →
    0 ≤ arg z ∧ arg z ≤ K.σ.θ₃ := by
  intro z hT _ h0
  exact arg_mem_Icc_of_sides' K.σ.θ₃_pos h0 (hT.2 0) (hT.2 1)

end Sectors

end Lay

end Sph

end ClosedTriangle

end GC.Seifert
