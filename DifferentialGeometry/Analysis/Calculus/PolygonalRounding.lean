import DifferentialGeometry.Analysis.Calculus.SmoothCorner
import DifferentialGeometry.Analysis.Calculus.CurveSubdivision
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ZMod.Basic

open Set Filter
open scoped ContDiff Topology NNReal

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def roundedPolygonalCurve (h ε : ℝ) (p : ℤ → E) (t : ℝ) : E :=
  let k : ℤ := ⌊t / h + 1 / 2⌋
  smoothCorner ε (p k) (h⁻¹ • (p k - p (k - 1)))
    (h⁻¹ • (p (k + 1) - p k)) (t - k * h)

namespace roundedPolygonalCurve

theorem eq_corner_of_mem_Ico {h : ℝ} (hh : 0 < h)
    (ε : ℝ) (p : ℤ → E) (k : ℤ) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) * h - h / 2) ((k : ℝ) * h + h / 2)) :
    roundedPolygonalCurve h ε p t =
      smoothCorner ε (p k) (h⁻¹ • (p k - p (k - 1)))
        (h⁻¹ • (p (k + 1) - p k)) (t - k * h) := by
  have hfloor : ⌊t / h + 1 / 2⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor
    · rw [← sub_le_iff_le_add, le_div_iff₀ hh]
      nlinarith [ht.1]
    · rw [← lt_sub_iff_add_lt, div_lt_iff₀ hh]
      nlinarith [ht.2]
  simp only [roundedPolygonalCurve, hfloor]

theorem eq_affine {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (p : ℤ → E) (k : ℤ) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) * h + ε) (((k : ℝ) + 1) * h - ε)) :
    roundedPolygonalCurve h ε p t =
      p k + ((t - k * h) / h) • (p (k + 1) - p k) := by
  let j : ℤ := ⌊t / h + 1 / 2⌋
  have hlow : k ≤ j := by
    apply Int.le_floor.mpr
    rw [← sub_le_iff_le_add, le_div_iff₀ hh]
    nlinarith [ht.1]
  have hhigh : j < k + 2 := by
    apply Int.floor_lt.mpr
    push_cast
    rw [← lt_sub_iff_add_lt, div_lt_iff₀ hh]
    nlinarith [ht.2]
  have hj : j = k ∨ j = k + 1 := by omega
  rcases hj with hj | hj
  · change smoothCorner ε (p j) (h⁻¹ • (p j - p (j - 1)))
      (h⁻¹ • (p (j + 1) - p j)) (t - j * h) = _
    rw [hj, smoothCorner.eq_right hε (by linarith [ht.1]), smul_smul, div_eq_mul_inv]
  · change smoothCorner ε (p j) (h⁻¹ • (p j - p (j - 1)))
      (h⁻¹ • (p (j + 1) - p j)) (t - j * h) = _
    rw [hj, smoothCorner.eq_left hε (by push_cast; linarith [ht.2])]
    simp only [add_sub_cancel_right, Int.cast_add, Int.cast_one, smul_smul]
    rw [show (t - ((k : ℝ) + 1) * h) * h⁻¹ = (t - k * h) / h - 1 by
      field_simp
      ring]
    simp only [sub_smul, one_smul, smul_sub]
    abel

theorem eq_corner_of_mem_Icc {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεh : ε ≤ h / 2) (p : ℤ → E) (k : ℤ) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) * h - h / 2) ((k : ℝ) * h + h / 2)) :
    roundedPolygonalCurve h ε p t =
      smoothCorner ε (p k) (h⁻¹ • (p k - p (k - 1)))
        (h⁻¹ • (p (k + 1) - p k)) (t - k * h) := by
  rcases ht.2.lt_or_eq with ht' | ht'
  · exact eq_corner_of_mem_Ico hh ε p k ⟨ht.1, ht'⟩
  · rw [eq_affine hh hε p k ⟨by linarith, by nlinarith⟩,
      smoothCorner.eq_right hε (by linarith), smul_smul, div_eq_mul_inv]

theorem image_Icc {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεh : ε ≤ h / 2) (p : ℤ → E) (k : ℤ) :
    roundedPolygonalCurve h ε p '' Icc ((k : ℝ) * h - h / 2) ((k : ℝ) * h + h / 2) =
      smoothCorner ε (p k) (h⁻¹ • (p k - p (k - 1)))
        (h⁻¹ • (p (k + 1) - p k)) '' Icc (-h / 2) (h / 2) := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t - k * h, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      (eq_corner_of_mem_Icc hh hε hεh p k ht).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t + k * h, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [eq_corner_of_mem_Icc hh hε hεh p k ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      add_sub_cancel_right]

theorem range_eq_iUnion_image_Icc {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεh : ε ≤ h / 2) (p : ℤ → E) :
    range (roundedPolygonalCurve h ε p) =
      ⋃ k : ℤ, smoothCorner ε (p k) (h⁻¹ • (p k - p (k - 1)))
        (h⁻¹ • (p (k + 1) - p k)) '' Icc (-h / 2) (h / 2) := by
  ext q
  constructor
  · rintro ⟨t, rfl⟩
    let k : ℤ := ⌊t / h + 1 / 2⌋
    have hlow : (k : ℝ) * h - h / 2 ≤ t := by
      have hf := Int.floor_le (t / h + 1 / 2)
      have hhf := (le_div_iff₀ hh).mp (show (k : ℝ) - 1 / 2 ≤ t / h by linarith)
      nlinarith
    have hhigh : t < (k : ℝ) * h + h / 2 := by
      have hf := Int.lt_floor_add_one (t / h + 1 / 2)
      have hhf := (div_lt_iff₀ hh).mp (show t / h < (k : ℝ) + 1 / 2 by linarith)
      nlinarith
    exact mem_iUnion.mpr ⟨k, image_Icc hh hε hεh p k ▸
      mem_image_of_mem (roundedPolygonalCurve h ε p) ⟨hlow, hhigh.le⟩⟩
  · intro hq
    obtain ⟨k, hk⟩ := mem_iUnion.mp hq
    rw [← image_Icc hh hε hεh p k] at hk
    exact image_subset_range _ _ hk

theorem range_eq_iUnion_image_Icc_zmod {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεh : ε ≤ h / 2) {n : ℕ} (p : ZMod n → E) :
    range (roundedPolygonalCurve h ε (fun k : ℤ => p k)) =
      ⋃ i : ZMod n, smoothCorner ε (p i) (h⁻¹ • (p i - p (i - 1)))
        (h⁻¹ • (p (i + 1) - p i)) '' Icc (-h / 2) (h / 2) := by
  rw [range_eq_iUnion_image_Icc hh hε hεh]
  simp only [Int.cast_sub, Int.cast_one, Int.cast_add]
  exact (ZMod.intCast_surjective (n := n)).iUnion_comp
    (fun i : ZMod n => smoothCorner ε (p i) (h⁻¹ • (p i - p (i - 1)))
      (h⁻¹ • (p (i + 1) - p i)) '' Icc (-h / 2) (h / 2))

private theorem eventually_eq_corner {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεh : ε < h / 2) (p : ℤ → E) (t : ℝ) :
    let j : ℤ := ⌊t / h + 1 / 2⌋
    roundedPolygonalCurve h ε p =ᶠ[𝓝 t]
      fun u => smoothCorner ε (p j) (h⁻¹ • (p j - p (j - 1)))
        (h⁻¹ • (p (j + 1) - p j)) (u - j * h) := by
  let j : ℤ := ⌊t / h + 1 / 2⌋
  have hlow : (j : ℝ) * h - h / 2 ≤ t := by
    have hf := Int.floor_le (t / h + 1 / 2)
    have hhf := (le_div_iff₀ hh).mp (show (j : ℝ) - 1 / 2 ≤ t / h by linarith)
    nlinarith
  have hhigh : t < (j : ℝ) * h + h / 2 := by
    have hf := Int.lt_floor_add_one (t / h + 1 / 2)
    have hhf := (div_lt_iff₀ hh).mp (show t / h < (j : ℝ) + 1 / 2 by linarith)
    nlinarith
  by_cases ht : (j : ℝ) * h - h / 2 < t
  · filter_upwards [Ioo_mem_nhds ht hhigh] with u hu
    exact eq_corner_of_mem_Ico hh ε p j ⟨hu.1.le, hu.2⟩
  · have hteq : t = (j : ℝ) * h - h / 2 := le_antisymm (le_of_not_gt ht) hlow
    have htleft : (((j - 1 : ℤ) : ℝ)) * h + ε < t := by
      rw [hteq, Int.cast_sub, Int.cast_one]
      nlinarith
    have htright : t < (j : ℝ) * h - ε := by rw [hteq]; linarith
    filter_upwards [Ioo_mem_nhds htleft htright] with u hu
    rw [eq_affine hh hε p (j - 1) ⟨hu.1.le, by
      simpa only [Int.cast_sub, Int.cast_one, sub_add_cancel] using hu.2.le⟩]
    rw [smoothCorner.eq_left hε (by linarith [hu.2])]
    simp only [sub_add_cancel, Int.cast_sub, Int.cast_one, smul_smul]
    rw [show (u - ((j : ℝ) - 1) * h) / h = (u - j * h) * h⁻¹ + 1 by
      field_simp
      ring]
    simp only [add_smul, one_smul, smul_sub]
    abel

theorem contDiff {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hεh : ε < h / 2)
    (p : ℤ → E) : ContDiff ℝ ∞ (roundedPolygonalCurve h ε p) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let j : ℤ := ⌊t / h + 1 / 2⌋
  have hs : ContDiff ℝ ∞ (fun u : ℝ =>
      smoothCorner ε (p j) (h⁻¹ • (p j - p (j - 1)))
        (h⁻¹ • (p (j + 1) - p j)) (u - j * h)) :=
    (smoothCorner.contDiff ε (p j) (h⁻¹ • (p j - p (j - 1)))
      (h⁻¹ • (p (j + 1) - p j))).comp (contDiff_id.sub contDiff_const)
  exact hs.contDiffAt.congr_of_eventuallyEq (eventually_eq_corner hh hε hεh p t)

theorem deriv_mem_segment {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hεh : ε < h / 2)
    (p : ℤ → E) (t : ℝ) :
    let j : ℤ := ⌊t / h + 1 / 2⌋
    deriv (roundedPolygonalCurve h ε p) t ∈
      segment ℝ (h⁻¹ • (p j - p (j - 1))) (h⁻¹ • (p (j + 1) - p j)) := by
  let j : ℤ := ⌊t / h + 1 / 2⌋
  rw [(eventually_eq_corner hh hε hεh p t).deriv_eq]
  have hd := (smoothCorner.hasDerivAt ε (p j) (h⁻¹ • (p j - p (j - 1)))
    (h⁻¹ • (p (j + 1) - p j)) (t - j * h)).scomp t
    ((hasDerivAt_id t).sub_const (j * h))
  change deriv (smoothCorner ε (p j) (h⁻¹ • (p j - p (j - 1)))
    (h⁻¹ • (p (j + 1) - p j)) ∘ fun x : ℝ => id x - j * h) t ∈ _
  rw [hd.deriv, one_smul]
  rw [segment_eq_image_lineMap]
  exact ⟨_, Real.smoothMax.deriv_left_mem_Icc ε (t - j * h) 0,
    AffineMap.lineMap_apply_module _ _ _⟩

theorem norm_deriv_sub_le {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (hεh : ε < h / 2)
    (p : ℤ → E) (t : ℝ) (q : E) {r : ℝ} :
    let j : ℤ := ⌊t / h + 1 / 2⌋
    ‖h⁻¹ • (p j - p (j - 1)) - q‖ ≤ r →
    ‖h⁻¹ • (p (j + 1) - p j) - q‖ ≤ r →
    ‖deriv (roundedPolygonalCurve h ε p) t - q‖ ≤ r := by
  intro j hv hw
  rw [← dist_eq_norm]
  apply Metric.mem_closedBall.mp
  exact (convex_closedBall q r).segment_subset
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw)
    (deriv_mem_segment hh hε hεh p t)

theorem norm_sub_vertex_le {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (p : ℤ → E) (t : ℝ) {M : ℝ} :
    let j : ℤ := ⌊t / h + 1 / 2⌋
    ‖h⁻¹ • (p j - p (j - 1))‖ ≤ M →
    ‖h⁻¹ • (p (j + 1) - p j)‖ ≤ M →
    ‖roundedPolygonalCurve h ε p t - p j‖ ≤ (h / 2 + 2 * ε) * M := by
  intro j hv hw
  have hM : 0 ≤ M := (norm_nonneg _).trans hv
  have hlow : (j : ℝ) * h - h / 2 ≤ t := by
    have hf := Int.floor_le (t / h + 1 / 2)
    have hhf := (le_div_iff₀ hh).mp (show (j : ℝ) - 1 / 2 ≤ t / h by linarith)
    nlinarith
  have hhigh : t < (j : ℝ) * h + h / 2 := by
    have hf := Int.lt_floor_add_one (t / h + 1 / 2)
    have hhf := (div_lt_iff₀ hh).mp (show t / h < (j : ℝ) + 1 / 2 by linarith)
    nlinarith
  have habs : |t - j * h| ≤ h / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  let v := h⁻¹ • (p j - p (j - 1))
  let w := h⁻¹ • (p (j + 1) - p j)
  let a := if t - j * h ≤ 0 then p j + (t - j * h) • v else p j + (t - j * h) • w
  have ha : ‖a - p j‖ ≤ h / 2 * M := by
    dsimp only [a]
    split_ifs
    · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul habs hv (norm_nonneg _) (half_pos hh).le
    · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul habs hw (norm_nonneg _) (half_pos hh).le
  have hbound := smoothCorner.norm_sub_le hε (p j) v w (t - j * h)
  have hwv : ‖w - v‖ ≤ 2 * M := (norm_sub_le w v).trans (by linarith)
  calc
    ‖roundedPolygonalCurve h ε p t - p j‖ ≤ ‖roundedPolygonalCurve h ε p t - a‖ + ‖a - p j‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε * (2 * M) + h / 2 * M := add_le_add
      (hbound.trans (mul_le_mul_of_nonneg_left hwv hε.le)) ha
    _ = (h / 2 + 2 * ε) * M := by ring

theorem norm_sub_le_of_lipschitz {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    {γ : ℝ → E} {C : ℝ≥0} (hγ : LipschitzWith C γ) (t : ℝ) :
    ‖roundedPolygonalCurve h ε (fun k : ℤ => γ (k * h)) t - γ t‖ ≤
      (h + 2 * ε) * C := by
  let j : ℤ := ⌊t / h + 1 / 2⌋
  have hslopes (k : ℤ) : ‖h⁻¹ • (γ ((k + 1 : ℤ) * h) - γ (k * h))‖ ≤ C := by
    have hb := hγ.dist_le_mul (((k + 1 : ℤ) : ℝ) * h) ((k : ℝ) * h)
    rw [dist_eq_norm, Real.dist_eq, Int.cast_add, Int.cast_one,
      show ((k : ℝ) + 1) * h - k * h = h by ring, abs_of_pos hh] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    calc
      h⁻¹ * ‖γ ((k + 1 : ℤ) * h) - γ (k * h)‖ ≤ h⁻¹ * ((C : ℝ) * h) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Int.cast_add, Int.cast_one] using hb) (inv_pos.mpr hh).le
      _ = C := by field_simp
  have hv : ‖h⁻¹ • (γ (j * h) - γ ((j - 1 : ℤ) * h))‖ ≤ C := by
    simpa only [sub_add_cancel] using hslopes (j - 1)
  have hw := hslopes j
  have hnear := norm_sub_vertex_le hh hε (fun k : ℤ => γ (k * h)) t hv hw
  have hlow : (j : ℝ) * h - h / 2 ≤ t := by
    have hf := Int.floor_le (t / h + 1 / 2)
    have hhf := (le_div_iff₀ hh).mp (show (j : ℝ) - 1 / 2 ≤ t / h by linarith)
    nlinarith
  have hhigh : t < (j : ℝ) * h + h / 2 := by
    have hf := Int.lt_floor_add_one (t / h + 1 / 2)
    have hhf := (div_lt_iff₀ hh).mp (show t / h < (j : ℝ) + 1 / 2 by linarith)
    nlinarith
  have hvertex : ‖γ (j * h) - γ t‖ ≤ C * (h / 2) := by
    have hb := hγ.dist_le_mul ((j : ℝ) * h) t
    rw [dist_eq_norm, Real.dist_eq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith, by linarith⟩) C.coe_nonneg)
  calc
    ‖roundedPolygonalCurve h ε (fun k : ℤ => γ (k * h)) t - γ t‖ ≤
        ‖roundedPolygonalCurve h ε (fun k : ℤ => γ (k * h)) t - γ (j * h)‖ +
          ‖γ (j * h) - γ t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (h / 2 + 2 * ε) * C + C * (h / 2) := add_le_add hnear hvertex
    _ = (h + 2 * ε) * C := by ring

theorem exists_uniform_deriv_approximation {γ v : ℝ → E}
    (hd : ∀ t, HasDerivAt γ (v t) t) (hv : UniformContinuous v)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, ∀ ε ∈ Ioo (0 : ℝ) (h / 2), ∀ t : ℝ,
      ‖deriv (roundedPolygonalCurve h ε (fun k : ℤ => γ (k * h))) t - v t‖ ≤ r := by
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuous_iff.mp hv r hr
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro h hh ε hε t
  let j : ℤ := ⌊t / h + 1 / 2⌋
  have hlow : (j : ℝ) * h - h / 2 ≤ t := by
    have hf := Int.floor_le (t / h + 1 / 2)
    have hhf := (le_div_iff₀ hh.1).mp (show (j : ℝ) - 1 / 2 ≤ t / h by linarith)
    nlinarith
  have hhigh : t < (j : ℝ) * h + h / 2 := by
    have hf := Int.lt_floor_add_one (t / h + 1 / 2)
    have hhf := (div_lt_iff₀ hh.1).mp (show t / h < (j : ℝ) + 1 / 2 by linarith)
    nlinarith
  have hvar (x : ℝ) (hx : x ∈ Icc (((j : ℝ) - 1) * h) (((j : ℝ) + 1) * h)) :
      ‖v x - v t‖ ≤ r := by
    rw [← dist_eq_norm]
    apply (show dist (v x) (v t) < r from hunif ?_).le
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> nlinarith [hx.1, hx.2, hh.2]
  apply norm_deriv_sub_le hh.1 hε.1 hε.2 (fun k : ℤ => γ (k * h)) t (v t)
  · have hb := norm_slope_sub_le_of_hasDerivWithinAt
      (γ := γ) (v := v) (w := v t) (ε := r)
      (show ((j : ℝ) - 1) * h < (j : ℝ) * h by nlinarith [hh.1])
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hvar x ⟨hx.1, by nlinarith [hx.2, hh.1]⟩)
    simpa only [slope_def_module, Int.cast_sub, Int.cast_one,
      show (j : ℝ) * h - (j - 1) * h = h by ring] using hb
  · have hb := norm_slope_sub_le_of_hasDerivWithinAt
      (γ := γ) (v := v) (w := v t) (ε := r)
      (show (j : ℝ) * h < ((j : ℝ) + 1) * h by nlinarith [hh.1])
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => hvar x ⟨by nlinarith [hx.1, hh.1], hx.2⟩)
    simpa only [slope_def_module, Int.cast_add, Int.cast_one,
      show ((j : ℝ) + 1) * h - j * h = h by ring] using hb

theorem periodic {h : ℝ} (hh : h ≠ 0) (ε : ℝ) {p : ℤ → E} {n : ℤ}
    (hp : Function.Periodic p n) :
    Function.Periodic (roundedPolygonalCurve h ε p) ((n : ℝ) * h) := by
  intro t
  have hshift : (t + (n : ℝ) * h) / h + 1 / 2 = (t / h + 1 / 2) + n := by
    field_simp
    ring
  have hp' : ∀ k : ℤ, p (k + n) = p k := hp
  dsimp only [roundedPolygonalCurve]
  rw [hshift, Int.floor_add_intCast]
  simp only [show ∀ k : ℤ, k + n - 1 = (k - 1) + n by omega,
    show ∀ k : ℤ, k + n + 1 = (k + 1) + n by omega, hp', Int.cast_add]
  congr 1
  ring

end roundedPolygonalCurve
end DifferentialGeometry.Analysis
