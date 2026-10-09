import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersChart
import DifferentialGeometry.Topology.Manifold.CornerRounding.Regular

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the common rounding

Part B of the circle kind of the S³ inhabitant: the controlled rounding of `C₁ = [1, 4]²`. On each
axis `a` the band function `circBand a = roundedMin 1 (16 slack_{a,1}) (16 slack_{a,4})` smooths
the minimum of the two slacks of that axis (their sum is `≥ 19`, so the smoothing only acts where
both are `≥ 9`); the rounding is

  `circRounding = −(1/16) · roundedMin (1/4) (circBand ψ) (circBand r)`.

On every corner chart the two bands are exactly `x` and `y`, so the rounding is
`−(1/16) ψ_std` (`circRounding_chart`); it is smooth, regular at its zeros
(`circRounding_regular`, by `mfderiv_roundedMin_ne_zero` twice), agrees with `C₁` outside the
unit-box images (`circRounding_agree`) and `{rounding ≤ 0} ⊆ C₁` is compact.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open DifferentialGeometry.Topology.Manifold.CornerRounding
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## One axis -/

/-- The band function of the axis `a` at the coordinate value `t`. -/
def circBand1 (a : Bool) (t : ℝ) : ℝ :=
  roundedMin 1 (16 * circSlack a false t) (16 * circSlack a true t)

theorem circSlack_sum (a : Bool) {t : ℝ} (ht : 0 < t) :
    19 ≤ 16 * circSlack a false t + 16 * circSlack a true t := by
  cases a <;> simp only [circSlack]
  · have ht2 : 0 < t ^ 2 := by positivity
    have key : 16 * (t ^ 2 - 1) + 16 * (16 / t ^ 2 - 1) - 19 =
        (16 * t ^ 4 - 51 * t ^ 2 + 256) / t ^ 2 := by
      field_simp
      ring
    have hnum : 0 ≤ (16 * t ^ 4 - 51 * t ^ 2 + 256) / t ^ 2 :=
      div_nonneg (by nlinarith [sq_nonneg (t ^ 2 - 4)]) ht2.le
    linarith
  · linarith

/-- Below `8` the band function has a gap `≥ 1` between its two arguments. -/
theorem circBand1_gap (a : Bool) {t : ℝ} (ht : 0 < t) (h : circBand1 a t < 8) :
    1 ≤ |16 * circSlack a false t - 16 * circSlack a true t| := by
  by_contra hlt
  rw [not_le] at hlt
  have hsum := circSlack_sum a ht
  have hm := min_sub_le_roundedMin one_pos (16 * circSlack a false t) (16 * circSlack a true t)
  have hab := abs_lt.1 hlt
  rw [circBand1] at h
  rcases le_total (16 * circSlack a false t) (16 * circSlack a true t) with hle | hle
  · rw [min_eq_left hle] at hm
    linarith [hab.1, hab.2]
  · rw [min_eq_right hle] at hm
    linarith [hab.1, hab.2]

theorem circBand1_eq_min (a : Bool) {t : ℝ} (ht : 0 < t) (h : circBand1 a t < 8) :
    circBand1 a t = min (16 * circSlack a false t) (16 * circSlack a true t) :=
  roundedMin_eq_min one_pos (circBand1_gap a ht h)

theorem circBand1_nonneg_iff (a : Bool) {t : ℝ} (ht : 0 < t) :
    0 ≤ circBand1 a t ↔ 1 ≤ t ∧ t ≤ 4 := by
  rw [← circSlack_false_nonneg_iff a ht, ← circSlack_true_nonneg_iff a ht]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := nonneg_of_roundedMin_nonneg one_pos h
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    by_cases hs : circBand1 a t < 8
    · rw [circBand1_eq_min a ht hs]
      exact le_min (by linarith) (by linarith)
    · linarith [not_lt.1 hs]

/-- A small band value is sixteen times one of the two slacks. -/
theorem circBand1_eq_slack (a : Bool) {t : ℝ} (ht : 0 < t) (h : circBand1 a t < 8) :
    ∃ σ, circBand1 a t = 16 * circSlack a σ t := by
  rw [circBand1_eq_min a ht h]
  rcases min_choice (16 * circSlack a false t) (16 * circSlack a true t) with hm | hm
  · exact ⟨false, hm⟩
  · exact ⟨true, hm⟩

/-- On a corner chart the band of the axis `a` is the chart coordinate. -/
theorem circBand1_circCornerInv (a σ : Bool) {s : ℝ} (hs : |s| < 2) :
    circBand1 a (circCornerInv a σ s) = s := by
  have hpos := circCornerInv_pos a σ hs
  have hsl := circSlack_circCornerInv a σ hs
  have hsmall : |circSlack a σ (circCornerInv a σ s)| < 1 / 8 := by
    rw [hsl, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
    linarith
  have hother := circSlack_other_gt a σ hpos hsmall
  have hl := (abs_lt.1 hs).1
  have hu := (abs_lt.1 hs).2
  rw [circBand1]
  cases σ
  · simp only [Bool.not_false] at hother
    rw [hsl, sixteen_mul_one_div, roundedMin_eq_min one_pos, min_eq_left (by linarith)]
    rw [abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · simp only [Bool.not_true] at hother
    rw [hsl, sixteen_mul_one_div, roundedMin_eq_min one_pos, min_eq_right (by linarith)]
    rw [abs_of_pos (by linarith)]
    linarith

/-! ## The bands on the base -/

/-- The band function of the axis `a` on the base. -/
def circBand (a : Bool) (c : sphereCircleBaseOpens) : ℝ :=
  circBand1 a (circCoordL a c.val)

theorem contMDiff_circBand (a : Bool) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (circBand a) := by
  have h1 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun c : sphereCircleBaseOpens => 16 * circSlack a false (circCoordL a c.val)) :=
    fun c => contMDiffAt_circAxis _ a c
      (contDiffAt_const.mul (contDiffAt_circSlack a false (circCoordL_pos a c)))
  have h2 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun c : sphereCircleBaseOpens => 16 * circSlack a true (circCoordL a c.val)) :=
    fun c => contMDiffAt_circAxis _ a c
      (contDiffAt_const.mul (contDiffAt_circSlack a true (circCoordL_pos a c)))
  exact contMDiff_roundedMin h1 h2 1

/-- **Where the band is small, its differential is a nonzero multiple of `dψ` resp. `dr`.** -/
theorem hasMFDerivAt_circBand (a : Bool) (c : sphereCircleBaseOpens) (h : circBand a c < 8) :
    ∃ α : ℝ, α ≠ 0 ∧ HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (circBand a) c (α • circCoordL a) := by
  have ht := circCoordL_pos a c
  have h1 := hasMFDerivAt_circAxis (fun t => 16 * circSlack a false t) a c
    ((hasDerivAt_circSlack a false ht).const_mul 16)
  have h2 := hasMFDerivAt_circAxis (fun t => 16 * circSlack a true t) a c
    ((hasDerivAt_circSlack a true ht).const_mul 16)
  have hD := hasMFDerivAt_roundedMin h1 h2 1
  have hgap := circBand1_gap a ht h
  rcases le_or_gt (16 * circSlack a true (circCoordL a c.val))
    (16 * circSlack a false (circCoordL a c.val)) with hle | hlt
  · have hw : 1 ≤ 16 * circSlack a false (circCoordL a c.val) -
        16 * circSlack a true (circCoordL a c.val) := by
      rwa [abs_of_nonneg (by linarith)] at hgap
    rw [roundedMinWeight_eq_one one_pos hw] at hD
    refine ⟨16 * circSlackDeriv a true (circCoordL a c.val),
      mul_ne_zero (by norm_num) (circSlackDeriv_ne_zero a true ht), hD.congr_mfderiv ?_⟩
    change ((1 - 1 : ℝ) • _ + (1 : ℝ) • _ : E2 →L[ℝ] ℝ) = _
    rw [sub_self, zero_smul, zero_add, one_smul]
  · have hw : 1 ≤ 16 * circSlack a true (circCoordL a c.val) -
        16 * circSlack a false (circCoordL a c.val) := by
      rwa [abs_sub_comm, abs_of_nonneg (by linarith)] at hgap
    rw [roundedMinWeight_eq_zero one_pos hw] at hD
    refine ⟨16 * circSlackDeriv a false (circCoordL a c.val),
      mul_ne_zero (by norm_num) (circSlackDeriv_ne_zero a false ht), hD.congr_mfderiv ?_⟩
    change ((1 - 0 : ℝ) • _ + (0 : ℝ) • _ : E2 →L[ℝ] ℝ) = _
    rw [sub_zero, zero_smul, add_zero, one_smul]

/-- `C₁` in terms of the bands. -/
theorem mem_sphereCircleCbase_iff_band {c : sphereCircleBaseOpens} :
    c ∈ sphereCircleCbase ↔ 0 ≤ circBand false c ∧ 0 ≤ circBand true c := by
  rw [circBand, circBand, circBand1_nonneg_iff false (circCoordL_pos false c),
    circBand1_nonneg_iff true (circCoordL_pos true c)]
  exact Iff.rfl

/-! ## The rounding -/

/-- **The common rounding** `−(1/16) · roundedMin (1/4) (band ψ) (band r)`. -/
def circRounding (c : sphereCircleBaseOpens) : ℝ :=
  -(1 / 16 * roundedMin rimRoundingWidth (circBand false c) (circBand true c))

theorem rimRoundingWidth_pos_CIRCB : 0 < rimRoundingWidth := by
  norm_num [rimRoundingWidth]

theorem contMDiff_circRounding : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ circRounding :=
  (contMDiff_const.mul (contMDiff_roundedMin (contMDiff_circBand false) (contMDiff_circBand true)
    rimRoundingWidth)).neg

theorem circRounding_nonpos_iff {c : sphereCircleBaseOpens} :
    circRounding c ≤ 0 ↔ 0 ≤ roundedMin rimRoundingWidth (circBand false c) (circBand true c) := by
  rw [circRounding, neg_nonpos]
  constructor <;> intro h <;> linarith

/-- **The rounding on a corner chart** is `−(1/16) ψ_std`. -/
theorem circRounding_chart (k : Fin 4) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    circRounding (circCorner k v) = -(1 / 16 * standardRimRounding v) := by
  have hc := circCoordL_circCornerChart (circCornerEquiv.symm k).1 (circCornerEquiv.symm k).2 hv
  rw [circRounding, circBand, circBand, circCorner, hc.1, hc.2, circBand1_circCornerInv _ _ hv.1,
    circBand1_circCornerInv _ _ hv.2]
  rfl

/-- **The rounding is regular at its zeros.** -/
theorem circRounding_regular (c : sphereCircleBaseOpens) (h0 : circRounding c = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) circRounding c ≠ 0 := by
  set g : sphereCircleBaseOpens → ℝ :=
    fun y => roundedMin rimRoundingWidth (circBand false y) (circBand true y) with hg
  have hzero : g c = 0 := by
    have : -(1 / 16 * g c) = 0 := h0
    linarith
  have hdf : ∀ a, MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) (circBand a) c := fun a =>
    (contMDiff_circBand a c).mdifferentiableAt (by simp)
  have hreg : ∀ a, circBand a c < 8 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (circBand a) c ≠ 0 := by
    intro a ha
    obtain ⟨α, hα, hD⟩ := hasMFDerivAt_circBand a c ha
    rw [hD.mfderiv]
    exact circCoordL_smul_ne_zero a hα
  have hgne : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g c ≠ 0 := by
    refine mfderiv_roundedMin_ne_zero (hdf false) (hdf true) rimRoundingWidth_pos_CIRCB
      (δ := 3 / 4) (by norm_num [rimRoundingWidth]) (fun h _ => hreg false (by linarith))
      (fun h _ => hreg true (by linarith)) ?_ hzero
    intro hφ hψ hs t ht
    obtain ⟨α, hα, hDα⟩ := hasMFDerivAt_circBand false c (by linarith)
    obtain ⟨β, hβ, hDβ⟩ := hasMFDerivAt_circBand true c (by linarith)
    have hD := (hDα.const_smul (1 - t)).add (hDβ.const_smul t)
    have hfun : (fun y => (1 - t) * circBand false y + t * circBand true y) =
        (1 - t) • circBand false + t • circBand true := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun, hD.mfderiv]
    intro hz
    change ((1 - t) • α • circCoordL false + t • β • circCoordL true : E2 →L[ℝ] ℝ) = 0 at hz
    rw [smul_smul, smul_smul] at hz
    obtain ⟨h1, h2⟩ := circCoordL_combination_eq_zero hz
    have h1' : 1 - t = 0 := (mul_eq_zero.1 h1).resolve_right hα
    have h2' : t = 0 := (mul_eq_zero.1 h2).resolve_right hβ
    linarith
  have hgd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) g c :=
    (contMDiff_roundedMin (contMDiff_circBand false) (contMDiff_circBand true)
      rimRoundingWidth c).mdifferentiableAt (by simp)
  have hR := hgd.hasMFDerivAt.const_smul (-(1 / 16 : ℝ))
  have hfun : circRounding = (-(1 / 16 : ℝ)) • g := by
    funext y
    simp only [circRounding, hg, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, hR.mfderiv]
  exact smul_ne_zero (by norm_num) hgne

/-- `{rounding ≤ 0} ⊆ C₁`. -/
theorem circRounding_nonpos_subset : {c | circRounding c ≤ 0} ⊆ sphereCircleCbase := by
  intro c hc
  have h := circRounding_nonpos_iff.1 hc
  exact mem_sphereCircleCbase_iff_band.2 (nonneg_of_roundedMin_nonneg
    rimRoundingWidth_pos_CIRCB h)

/-- **The rounding agrees with `C₁` outside the unit-box images of the corner charts.** -/
theorem circRounding_agree :
    {c | circRounding c ≤ 0} \ (⋃ k, circCorner k '' rimBox 1) =
      sphereCircleCbase \ ⋃ k, circCorner k '' rimBox 1 := by
  ext c
  constructor
  · rintro ⟨hc, hU⟩
    exact ⟨circRounding_nonpos_subset hc, hU⟩
  · rintro ⟨hc, hU⟩
    refine ⟨?_, hU⟩
    obtain ⟨hφ, hψ⟩ := mem_sphereCircleCbase_iff_band.1 hc
    change circRounding c ≤ 0
    rw [circRounding_nonpos_iff]
    by_contra hneg
    obtain ⟨-, hs⟩ := band_of_roundedMin_neg rimRoundingWidth_pos_CIRCB hφ hψ (not_le.1 hneg)
    rw [rimRoundingWidth] at hs
    obtain ⟨σ, hσ⟩ := circBand1_eq_slack false (circCoordL_pos false c)
      (show circBand false c < 8 by linarith)
    obtain ⟨τ, hτ⟩ := circBand1_eq_slack true (circCoordL_pos true c)
      (show circBand true c < 8 by linarith)
    have hbox1 : (circBand false c, circBand true c) ∈ rimBox 1 := by
      refine ⟨?_, ?_⟩
      · rw [abs_of_nonneg hφ]
        linarith
      · rw [abs_of_nonneg hψ]
        linarith
    have hbox2 : (circBand false c, circBand true c) ∈ rimBox 2 :=
      ⟨by linarith [hbox1.1], by linarith [hbox1.2]⟩
    apply hU
    refine mem_iUnion.2 ⟨circCornerEquiv (σ, σ ^^ τ), (circBand false c, circBand true c),
      hbox1, Subtype.ext ?_⟩
    have hx : (σ ^^ (σ ^^ τ)) = τ := by cases σ <;> cases τ <;> rfl
    rw [circCorner, Equiv.symm_apply_apply, circCornerChart_val _ _ hbox2, circPlaneMap]
    dsimp only
    rw [hx]
    change sphereCircleEquiv.symm (circCornerInv false σ (circBand1 false (circCoordL false c.val)),
      circCornerInv true τ (circBand1 true (circCoordL true c.val))) = c.val
    rw [hσ, hτ, circCornerInv_circSlack false σ (circCoordL_pos false c),
      circCornerInv_circSlack true τ (circCoordL_pos true c)]
    exact sphereCircleEquiv.symm_apply_apply c.val

/-- **The rounded base is compact.** -/
theorem isCompact_circRounding : IsCompact {c | circRounding c ≤ 0} :=
  isCompact_sphereCircleCbase.of_isClosed_subset
    (isClosed_le contMDiff_circRounding.continuous continuous_const) circRounding_nonpos_subset

end GC.GraphManifold.Assembly.FC39P0
