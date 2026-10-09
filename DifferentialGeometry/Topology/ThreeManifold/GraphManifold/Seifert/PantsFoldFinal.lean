import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsFoldCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCoreDescent
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCollars

/-!
# `PantsQuotientDiffeo` holds

Packet K16f, tier 3. Let `F` be the fold with its core replaced (`exists_foldCore`). The three
hypotheses of `pantsQuotientDiffeo_of_core` left are proved here. Wall identities
(`fold_hwall`): on `{|x| < 1/100, |holeX| < 1/100}` both a point and its mirror in wall 0 use
`cornerZero` or `cornerInf` with the odd angle (`foldMap_neg_conj`); wall 1 follows by the
mirror `foldMirror`; on the reflection-stable neighbourhood of wall 2 defined by
`|wallTwo| < 1/250`, `|1 + 2 holeX| < 1/5` at the point and at its reflection, every branch equals
`bridgeTwo` (`foldMap_eq_bridgeTwo_of`), whose reflection identity is `bridgeTwo_wallReflection`.
Surjectivity onto `pantsPlus` (`fold_surjOn`): `F` of the open triangle is open (inverse function
theorem), nonempty, and closed in the connected open upper half `foldPantsUpper`, because a point
deep in a cusp is mapped close to the corresponding boundary circle (`foldMap_of_im_gt_one`,
`norm_cornerZero_sub`, `norm_cornerHalf_add`), so preimages of a compact part lie in the compact
`hexagonSet`, and boundary points of the triangle have real image (`im_eq_zero_of_boundary`);
the real segments are the images of the walls (`foldMap_wall_zero`, `foldMap_wall_one`,
`foldMap_wall_two`). Hence `pantsQuotientDiffeo : PantsQuotientDiffeo`.
-/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem heightOne_neg (x y : ℝ) : heightOne (-x) y = heightOne x y := by
  unfold heightOne
  ring

theorem holeX_neg (x y : ℝ) : holeX (-x) y = -holeX x y := by
  unfold holeX
  ring

theorem heightHalf_lt_of_abs_lt {x y : ℝ} (hy : 0 < y) (hx : |x| < 1 / 100) :
    heightOne (1 / 2 - x) y < 3 / 5 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  unfold heightOne
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [sq_nonneg (y - 1 / 2)]

theorem foldMap_neg_conj {w : ℂ} (hw : 0 < w.im) (hx : |w.re| < 1 / 100)
    (hX : |holeX w.re w.im| < 1 / 100) : foldMap (-conj w) = conj (foldMap w) := by
  have hre : (-conj w).re = -w.re := by simp
  have him : (-conj w).im = w.im := by simp
  have hw' : 0 < (-conj w).im := by rw [him]; exact hw
  have hh : ¬ 3 / 5 < heightOne (1 / 2 - w.re) w.im :=
    not_lt.2 (heightHalf_lt_of_abs_lt hw hx).le
  have hh' : ¬ 3 / 5 < heightOne (1 / 2 - (-conj w).re) (-conj w).im := by
    rw [hre, him]
    exact not_lt.2 (heightHalf_lt_of_abs_lt hw (by rwa [abs_neg])).le
  by_cases h0 : 3 / 5 < heightOne w.re w.im
  · have h0' : 3 / 5 < heightOne (-conj w).re (-conj w).im := by
      rw [hre, him, heightOne_neg]; exact h0
    rw [foldMap_of_heightOne h0, foldMap_of_heightOne h0']
    exact cornerZero_neg_conj hw (by linarith) (by linarith)
  · have h0' : ¬ 3 / 5 < heightOne (-conj w).re (-conj w).im := by
      rw [hre, him, heightOne_neg]; exact h0
    have hl : ¬ foldLens w := fun h =>
      absurd ((normSq_sub_half_lt_iff hw).1 h.2.2) (by linarith [(abs_lt.1 hX).1])
    have hl' : ¬ foldLens (-conj w) := fun h => by
      have := (normSq_sub_half_lt_iff hw').1 h.2.2
      rw [hre, him, holeX_neg] at this
      linarith [(abs_lt.1 hX).2]
    rw [foldMap_of_not_lens h0 hh hl, foldMap_of_not_lens h0' hh' hl']
    exact cornerInf_neg_conj (by linarith)

theorem foldMap_eq_bridgeTwo_of {w : ℂ} (hw : 0 < w.im) (h1 : wallTwo w.re w.im < 1 / 25)
    (h2 : holeX w.re w.im ≤ -(35 / 100)) (h3 : holeX (1 / 2 - w.re) w.im ≤ -(35 / 100)) :
    foldMap w = bridgeTwo w := by
  by_cases h0 : 3 / 5 < heightOne w.re w.im
  · rw [foldMap_of_heightOne h0, cornerZero_eq_bridgeTwo hw h2]
  by_cases hh : 3 / 5 < heightOne (1 / 2 - w.re) w.im
  · have hM : 0 < (foldMirror w).im := by rw [foldMirror_im]; exact hw
    rw [foldMap_of_heightHalf h0 hh, cornerHalf,
      cornerZero_eq_bridgeTwo hM (by rw [foldMirror_re, foldMirror_im]; exact h3), foldMirror,
      bridgeTwo_mirror]
    simp
  have hl : foldLens w := ⟨h1, (normSq_lt_iff_holeX_half hw).2 (by linarith),
    (normSq_sub_half_lt_iff hw).2 (by linarith)⟩
  exact foldMap_of_lens h0 hh hl

theorem norm_sub_foldCenter_ge_of_re {z : ℂ} (h : z.re < 3 / 20 ∨ 7 / 20 < z.re) :
    1 / 10 ≤ ‖z - foldCenter‖ := by
  have hsq := norm_sub_foldCenter_sq z
  have : (1 / 10) ^ 2 ≤ ‖z - foldCenter‖ ^ 2 := by
    rw [hsq]
    rcases h with h | h <;> nlinarith [sq_nonneg (z.im - 37 / 100)]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) (by norm_num)).1 this

theorem norm_sub_foldCenter_ge_of_wallTwo {z : ℂ} (h : wallTwo z.re z.im < 1 / 100) :
    1 / 10 ≤ ‖z - foldCenter‖ := by
  by_contra hc
  push Not at hc
  have := wallTwo_ge_of_norm_le hc.le
  linarith

theorem continuous_holeX_coe : Continuous fun z : ℍ => holeX (z : ℂ).re (z : ℂ).im :=
  continuous_iff_continuousAt.2 fun z =>
    (continuousAt_holeX z.im_pos).comp UpperHalfPlane.continuous_coe.continuousAt

theorem continuous_holeX_half_coe :
    Continuous fun z : ℍ => holeX (1 / 2 - (z : ℂ).re) (z : ℂ).im := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  have hz := z.im_pos
  have h : ContinuousAt (fun w : ℂ => holeX (1 / 2 - w.re) w.im) (z : ℂ) := by
    unfold holeX
    have hre : Continuous fun w : ℂ => w.re := Complex.continuous_re
    have him : Continuous fun w : ℂ => w.im := Complex.continuous_im
    have h : 4 * ((1 / 2 - (z : ℂ).re) ^ 2 + (z : ℂ).im ^ 2) ≠ 0 := by
      have : 0 < (z : ℂ).im := hz
      positivity
    fun_prop (disch := exact h)
  exact h.comp UpperHalfPlane.continuous_coe.continuousAt

theorem continuous_wallTwo_coe : Continuous fun z : ℍ => wallTwo (z : ℂ).re (z : ℂ).im :=
  continuous_wallTwo.comp UpperHalfPlane.continuous_coe

theorem holeX_of_wallTwo_eq_zero {x y : ℝ} (hy : 0 < y) (hw : wallTwo x y = 0) :
    holeX x y = -(1 / 2) ∧ holeX (1 / 2 - x) y = -(1 / 2) := by
  unfold wallTwo at hw
  have hx : 0 < x := by nlinarith
  have hx' : x < 1 / 2 := by nlinarith
  unfold holeX
  constructor
  · rw [div_eq_iff (by positivity)]
    nlinarith
  · rw [div_eq_iff (by positivity)]
    nlinarith

theorem wallTwo_eq_zero_of_mem_wall {z : ℍ} (hz : z ∈ wall 2) :
    wallTwo (z : ℂ).re (z : ℂ).im = 0 := by
  rw [mem_wall_iff, wallSide_two] at hz
  exact hz

theorem fold_hwall {F : ℂ → ℂ} (hF1 : ∀ z, 1 / 10 ≤ ‖z - foldCenter‖ → F z = foldMap z) :
    ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z) := by
  intro i
  fin_cases i
  · refine ⟨{z : ℍ | |(z : ℂ).re| < 1 / 100 ∧ |holeX (z : ℂ).re (z : ℂ).im| < 1 / 100},
      (isOpen_lt (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe))
        continuous_const).inter (isOpen_lt (continuous_abs.comp continuous_holeX_coe)
          continuous_const), ?_, ?_⟩
    · intro z hz
      have h0 : (z : ℂ).re = 0 := hz
      refine ⟨by rw [h0]; norm_num, ?_⟩
      unfold holeX
      rw [h0]
      norm_num
    · rintro z ⟨hx, hX⟩
      simp only [Fin.zero_eta]
      rw [coe_wallReflection_zero_smul]
      have hre : (-conj (z : ℂ)).re = -(z : ℂ).re := by simp
      rw [hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inl (by rw [hre]; linarith [(abs_lt.1 hx).1]))),
        hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inl (by linarith [(abs_lt.1 hx).2])))]
      exact foldMap_neg_conj z.im_pos hx hX
  · refine ⟨{z : ℍ | |1 / 2 - (z : ℂ).re| < 1 / 100 ∧
        |holeX (1 / 2 - (z : ℂ).re) (z : ℂ).im| < 1 / 100},
      (isOpen_lt (continuous_abs.comp (continuous_const.sub
        (Complex.continuous_re.comp UpperHalfPlane.continuous_coe))) continuous_const).inter
        (isOpen_lt (continuous_abs.comp continuous_holeX_half_coe) continuous_const), ?_, ?_⟩
    · intro z hz
      have h0 : (z : ℂ).re = 1 / 2 := hz
      refine ⟨by rw [h0]; norm_num, ?_⟩
      unfold holeX
      rw [h0]
      norm_num
    · rintro z ⟨hx, hX⟩
      simp only [Fin.mk_one]
      rw [coe_wallReflection_one_smul]
      set w := foldMirror (z : ℂ)
      have hwre : w.re = 1 / 2 - (z : ℂ).re := foldMirror_re _
      have hwim : w.im = (z : ℂ).im := foldMirror_im _
      have hw0 : 0 < w.im := by rw [hwim]; exact z.im_pos
      have key : (1 : ℂ) - conj (z : ℂ) = foldMirror (-conj w) := by
        apply Complex.ext
        · rw [foldMirror_re]
          simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.neg_re, hwre]
          ring
        · rw [foldMirror_im]
          simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, Complex.neg_im, hwim]
          ring
      have hre1 : ((1 : ℂ) - conj (z : ℂ)).re = 1 - (z : ℂ).re := by simp
      have hlt1 : 7 / 20 < ((1 : ℂ) - conj (z : ℂ)).re := by
        rw [hre1]; linarith [(abs_lt.1 hx).1]
      rw [hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inr hlt1)),
        hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inr (by linarith [(abs_lt.1 hx).2]))), key,
        foldMap_foldMirror (by simp [hw0]),
        foldMap_neg_conj hw0 (by rw [hwre]; exact hx) (by rw [hwre, hwim]; exact hX)]
      have := foldMap_foldMirror (z := (z : ℂ)) z.im_pos
      rw [this]
      simp
  · refine ⟨{z : ℍ | (|wallTwo (z : ℂ).re (z : ℂ).im| < 1 / 250 ∧
        |1 + 2 * holeX (z : ℂ).re (z : ℂ).im| < 1 / 5 ∧
        |1 + 2 * holeX (1 / 2 - (z : ℂ).re) (z : ℂ).im| < 1 / 5) ∧
      (|wallTwo ((wallReflection 2 • z : ℍ) : ℂ).re ((wallReflection 2 • z : ℍ) : ℂ).im| < 1 / 250 ∧
        |1 + 2 * holeX ((wallReflection 2 • z : ℍ) : ℂ).re ((wallReflection 2 • z : ℍ) : ℂ).im| <
          1 / 5 ∧
        |1 + 2 * holeX (1 / 2 - ((wallReflection 2 • z : ℍ) : ℂ).re)
          ((wallReflection 2 • z : ℍ) : ℂ).im| < 1 / 5)}, ?_, ?_, ?_⟩
    · have hσ : Continuous fun z : ℍ => wallReflection 2 • z :=
        (isometry_wallReflection_smul 2).continuous
      have hA : IsOpen {z : ℍ | |wallTwo (z : ℂ).re (z : ℂ).im| < 1 / 250 ∧
          |1 + 2 * holeX (z : ℂ).re (z : ℂ).im| < 1 / 5 ∧
          |1 + 2 * holeX (1 / 2 - (z : ℂ).re) (z : ℂ).im| < 1 / 5} :=
        (isOpen_lt (continuous_abs.comp continuous_wallTwo_coe) continuous_const).inter
          ((isOpen_lt (continuous_abs.comp (continuous_const.add
            (continuous_const.mul continuous_holeX_coe))) continuous_const).inter
          (isOpen_lt (continuous_abs.comp (continuous_const.add
            (continuous_const.mul continuous_holeX_half_coe))) continuous_const))
      exact hA.inter (hA.preimage hσ)
    · intro z hz
      have hfix := wallReflection_smul_of_mem_wall hz
      have hw0 := wallTwo_eq_zero_of_mem_wall hz
      obtain ⟨e1, e2⟩ := holeX_of_wallTwo_eq_zero (x := (z : ℂ).re) (y := (z : ℂ).im) z.im_pos hw0
      have hA : |wallTwo (z : ℂ).re (z : ℂ).im| < 1 / 250 ∧
          |1 + 2 * holeX (z : ℂ).re (z : ℂ).im| < 1 / 5 ∧
          |1 + 2 * holeX (1 / 2 - (z : ℂ).re) (z : ℂ).im| < 1 / 5 := by
        rw [hw0, e1, e2]
        norm_num
      refine ⟨hA, ?_⟩
      simp only [Fin.reduceFinMk] at hfix ⊢
      rw [hfix]
      exact hA
    · rintro z ⟨⟨a1, a2, a3⟩, b1, b2, b3⟩
      simp only [Fin.reduceFinMk] at b1 b2 b3 ⊢
      set z' := wallReflection 2 • z
      have hcond : ∀ w : ℂ, 0 < w.im → |wallTwo w.re w.im| < 1 / 250 →
          |1 + 2 * holeX w.re w.im| < 1 / 5 → |1 + 2 * holeX (1 / 2 - w.re) w.im| < 1 / 5 →
          F w = bridgeTwo w := by
        intro w hw h1 h2 h3
        have h1' := (abs_lt.1 h1).2
        rw [hF1 w (norm_sub_foldCenter_ge_of_wallTwo (by linarith))]
        exact foldMap_eq_bridgeTwo_of hw (by linarith) (by linarith [(abs_lt.1 h2).2])
          (by linarith [(abs_lt.1 h3).2])
      rw [hcond _ z'.im_pos b1 b2 b3, hcond _ z.im_pos a1 a2 a3]
      exact bridgeTwo_wallReflection z

theorem exists_bridgeSigma_lt {s : ℝ} (hs : 1 / 2 < s) :
    ∃ H : ℝ, 0 < H ∧ ∀ t, H ≤ t → bridgeSigma t < s := by
  refine ⟨max 1 (1 / (s - 1 / 2)), by positivity, fun t ht => ?_⟩
  have h1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have h2 : 1 / (s - 1 / 2) ≤ t := le_trans (le_max_right _ _) ht
  have hs' : 0 < s - 1 / 2 := by linarith
  rw [div_le_iff₀ hs'] at h2
  unfold bridgeSigma
  have h3 : 2 / (1 + 4 * t ^ 2) ≤ 1 / (2 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (2 * t - 1)]
  have h4 : 1 / (2 * t) < s - 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

theorem isOpen_triangleInterior : IsOpen triangleInterior :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const continuous_wallTwo)))

theorem im_eq_zero_of_boundary {F : ℂ → ℂ}
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    {z : ℂ} (hz : z ∈ triangleSet) (hnot : z ∉ triangleInterior) : (F z).im = 0 := by
  obtain ⟨hy, h0, h1, hw⟩ := hz
  set p : ℍ := ⟨z, hy⟩
  have hp : (p : ℂ) = z := rfl
  have hreal : ∃ i, p ∈ wall i := by
    by_contra hc
    push Not at hc
    apply hnot
    refine ⟨hy, lt_of_le_of_ne h0 fun h => hc 0 h.symm, lt_of_le_of_ne h1 fun h => hc 1 h,
      lt_of_le_of_ne hw fun h => hc 2 ?_⟩
    change ‖(p : ℂ) - 1 / 4‖ = 1 / 4
    rw [norm_eq_quarter_iff, wallSide_two]
    exact h.symm
  obtain ⟨i, hi⟩ := hreal
  have := core_conj_of_mem_wall hwall i p hi
  rw [hp] at this
  exact Complex.conj_eq_iff_im.1 this

theorem mem_hexagonSet {z : ℂ} {H : ℝ} (hH : 1 / 2 ≤ H) (hz : z ∈ triangleSet) (hy : z.im ≤ H)
    (h0 : heightOne z.re z.im ≤ H) (hh : heightOne (1 / 2 - z.re) z.im ≤ H) :
    z ∈ hexagonSet H := by
  rw [← coe_image_pantsHexagon hH]
  refine ⟨⟨z, hz.1⟩, ⟨(coe_mem_triangleSet_iff _).1 hz, fun j => ?_⟩, rfl⟩
  fin_cases j
  · change cuspHeight 0 z ≤ H
    rw [cuspHeight_zero_eq]
    unfold heightOne at hh
    rwa [show (z.re - 1 / 2) ^ 2 = (1 / 2 - z.re) ^ 2 by ring]
  · change cuspHeight 1 z ≤ H
    rw [cuspHeight_one_eq]
    exact h0
  · change cuspHeight 2 z ≤ H
    rw [cuspHeight_two_eq]
    exact hy

theorem hexagonSet_subset {H : ℝ} (hH : 1 / 2 ≤ H) : hexagonSet H ⊆ triangleSet := by
  rw [← coe_image_pantsHexagon hH]
  rintro _ ⟨p, hp, rfl⟩
  exact (coe_mem_triangleSet_iff p).2 hp.1

theorem heightOne_le_quarter_inv {x y : ℝ} (hy : 0 < y) : heightOne x y ≤ 1 / (4 * y) := by
  unfold heightOne
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg x]

theorem foldMap_of_im_gt_one {z : ℂ} (hz : z ∈ triangleSet) (hy : 1 < z.im) :
    foldMap z = cornerInf z := by
  have hy0 := hz.1
  have hq : 1 / (4 * z.im) < 3 / 5 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  refine foldMap_of_not_lens (not_lt.2 (le_trans (heightOne_le_quarter_inv hy0) hq.le))
    (not_lt.2 (le_trans (heightOne_le_quarter_inv hy0) hq.le)) fun hl => ?_
  have := hl.1
  have hx0 := hz.2.1
  have hx1 := hz.2.2.1
  unfold wallTwo at this
  nlinarith

theorem im_lt_quarter_of_heightOne_gt_one {x y : ℝ} (hy : 0 < y) (h : 1 < heightOne x y) :
    y < 1 / 4 := by
  unfold heightOne at h
  rw [lt_div_iff₀ (by positivity)] at h
  nlinarith [sq_nonneg x]

theorem norm_sub_foldCenter_ge_of_im {z : ℂ} (h : z.im < 1 / 4 ∨ 1 < z.im) :
    1 / 10 ≤ ‖z - foldCenter‖ := by
  have hsq := norm_sub_foldCenter_sq z
  have : (1 / 10) ^ 2 ≤ ‖z - foldCenter‖ ^ 2 := by
    rw [hsq]
    rcases h with h | h <;> nlinarith [sq_nonneg (z.re - 1 / 4)]
  exact (pow_le_pow_iff_left₀ (by norm_num) (norm_nonneg _) (by norm_num)).1 this

theorem foldMap_wall_zero {y : ℝ} (hy : 0 < y) : foldMap ⟨0, y⟩ = (foldRho y : ℂ) := by
  have hre : (⟨0, y⟩ : ℂ).re = 0 := rfl
  have him : (⟨0, y⟩ : ℂ).im = y := rfl
  have hh : ¬ 3 / 5 < heightOne (1 / 2 - (⟨0, y⟩ : ℂ).re) (⟨0, y⟩ : ℂ).im := by
    rw [hre, him]
    unfold heightOne
    rw [not_lt, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (y - 1 / 2)]
  by_cases h0 : 3 / 5 < heightOne (⟨0, y⟩ : ℂ).re (⟨0, y⟩ : ℂ).im
  · rw [foldMap_of_heightOne h0, cornerZero_wall_zero hy (by rw [hre, him] at h0; linarith)]
    have hy' : y ≤ 12 / 25 := by
      rw [hre, him] at h0
      unfold heightOne at h0
      rw [lt_div_iff₀ (by positivity)] at h0
      nlinarith
    rw [foldRho_eq_bridgeRho hy']
  · have hl : ¬ foldLens ⟨0, y⟩ := fun hl => by
      have := hl.2.2
      rw [Complex.normSq_apply] at this
      simp at this
      nlinarith
    rw [foldMap_of_not_lens h0 hh hl, cornerInf_wall_zero hy]

theorem foldMap_wall_one {y : ℝ} (hy : 0 < y) : foldMap ⟨1 / 2, y⟩ = -(foldRho y : ℂ) := by
  have h : (⟨1 / 2, y⟩ : ℂ) = foldMirror ⟨0, y⟩ := by
    apply Complex.ext <;> simp [foldMirror_re, foldMirror_im]
  rw [h, foldMap_foldMirror (by simpa using hy), foldMap_wall_zero hy, Complex.conj_ofReal]

theorem wallTwo_wall_two_point {t : ℝ} (ht : 0 < t) :
    wallTwo (⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩ : ℂ).re
      (⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩ : ℂ).im = 0 := by
  set w : ℂ := ⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩
  have hw0 : 0 < w.im := holeInvIm_pos ht
  have hX : holeX w.re w.im = -(1 / 2) := holeX_holeInv ht
  have hs : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  unfold holeX at hX
  rw [div_eq_iff (by positivity)] at hX
  unfold wallTwo
  linarith

theorem foldMap_wall_two {t : ℝ} (ht : 0 < t) :
    foldMap ⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩ =
      ((3 / 2 - bridgeSigma t : ℝ) : ℂ) := by
  set w : ℂ := ⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩
  have hw0 : 0 < w.im := holeInvIm_pos ht
  have hh : heightOne w.re w.im = t := heightOne_holeInv ht
  have hX : holeX w.re w.im = -(1 / 2) := holeX_holeInv ht
  have hwall : wallTwo w.re w.im = 0 := wallTwo_wall_two_point ht
  obtain ⟨-, e2⟩ := holeX_of_wallTwo_eq_zero hw0 hwall
  rw [foldMap_eq_bridgeTwo_of hw0 (by rw [hwall]; norm_num) (by rw [hX]; norm_num)
    (by rw [e2]; norm_num), bridgeTwo_of_wallTwo_eq_zero hw0 hwall, hh]

theorem mem_triangleSet_wall_two {t : ℝ} (ht : 0 < t) :
    (⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩ : ℂ) ∈ triangleSet := by
  set w : ℂ := ⟨holeInvRe (-(1 / 2)) t, holeInvIm (-(1 / 2)) t⟩
  have hw0 : 0 < w.im := holeInvIm_pos ht
  have hX : holeX w.re w.im = -(1 / 2) := holeX_holeInv ht
  have hs : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  unfold holeX at hX
  rw [div_eq_iff (by positivity)] at hX
  refine ⟨hw0, by nlinarith, by nlinarith, ?_⟩
  unfold wallTwo
  linarith

theorem exists_holeInv_wall_two {a : ℝ} (h1 : -1 < a) (h2 : a < 1) :
    ∃ t : ℝ, 0 < t ∧ bridgeSigma t = 3 / 2 - a := by
  have hpos : 0 < (2 / (1 - a) - 1) / 4 := by
    have : 1 < 2 / (1 - a) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    linarith
  refine ⟨Real.sqrt ((2 / (1 - a) - 1) / 4), Real.sqrt_pos.2 hpos, ?_⟩
  unfold bridgeSigma
  rw [Real.sq_sqrt hpos.le]
  have : 1 + 4 * ((2 / (1 - a) - 1) / 4) = 2 / (1 - a) := by ring
  rw [this]
  field_simp
  ring

theorem fold_surjOn {F : ℂ → ℂ} (hF1 : ∀ z, 1 / 10 ≤ ‖z - foldCenter‖ → F z = foldMap z)
    (hF2 : ∀ z, 0 < z.im → ContDiffAt ℝ ∞ F z) (hF3 : ∀ z, 0 < z.im → (fderiv ℝ F z).det ≠ 0)
    (hF6 : Set.MapsTo F triangleInterior foldPantsUpper)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z)) :
    ∀ u ∈ pantsPlus, ∃ z : ℂ, z ∈ triangleSet ∧ F z = u := by
  intro u hu
  by_cases him : 0 < u.im
  · have hopen : IsOpen (F '' triangleInterior) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨z, hz, rfl⟩
      exact image_mem_nhds_of_det_ne_zero (isOpen_triangleInterior.mem_nhds hz) (hF2 z hz.1)
        (hF3 z hz.1)
    have hz₁ : ((1 / 4 : ℝ) + (1 : ℂ) * Complex.I) ∈ triangleInterior := by
      refine ⟨by simp, by simp, by simp; norm_num, ?_⟩
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.one_re,
        Complex.I_re, Complex.one_im, Complex.I_im, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im]
      unfold wallTwo
      norm_num
    have hne : (foldPantsUpper ∩ F '' triangleInterior).Nonempty :=
      ⟨_, hF6 hz₁, _, hz₁, rfl⟩
    have hclos : closure (F '' triangleInterior) ∩ foldPantsUpper ⊆ F '' triangleInterior := by
      rintro v ⟨hvc, hvp⟩
      obtain ⟨hpl, hvim⟩ := hvp
      obtain ⟨hn3, hn1, hn2⟩ := (planarFunction_three_neg_iff v).1 hpl
      obtain ⟨H₁, -, hH₁⟩ := exists_lt_foldRho (show (‖v‖ + 3) / 2 < 3 by linarith)
      set s := (min ‖v - 3 / 2‖ ‖v + 3 / 2‖ + 1 / 2) / 2
      have hs1 : 1 / 2 < s := by
        have := lt_min hn1 hn2
        simp only [s]
        linarith
      have hs2 : s < ‖v - 3 / 2‖ := by
        have := min_le_left ‖v - 3 / 2‖ ‖v + 3 / 2‖
        simp only [s]
        linarith
      have hs3 : s < ‖v + 3 / 2‖ := by
        have := min_le_right ‖v - 3 / 2‖ ‖v + 3 / 2‖
        simp only [s]
        linarith
      obtain ⟨H₂, -, hH₂⟩ := exists_bridgeSigma_lt hs1
      set H := max (max H₁ H₂) 1
      have hH1 : 1 ≤ H := le_max_right _ _
      have hHa : H₁ ≤ H := le_trans (le_max_left _ _) (le_max_left _ _)
      have hHb : H₂ ≤ H := le_trans (le_max_right _ _) (le_max_left _ _)
      set N := {w : ℂ | ‖w‖ < (‖v‖ + 3) / 2 ∧ s < ‖w - 3 / 2‖ ∧ s < ‖w + 3 / 2‖}
      have hNo : IsOpen N := by
        refine (isOpen_lt continuous_norm continuous_const).inter
          ((isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
            (isOpen_lt continuous_const (continuous_id.add continuous_const).norm))
      have hvN : v ∈ N := ⟨by linarith, hs2, hs3⟩
      have hK : ∀ z ∈ triangleSet, F z ∈ N → z ∈ hexagonSet H := by
        intro z hz hFz
        have hy0 := hz.1
        obtain ⟨k1, k2, k3⟩ := hFz
        refine mem_hexagonSet (by linarith) hz ?_ ?_ ?_
        · by_contra hc
          push Not at hc
          rw [hF1 z (norm_sub_foldCenter_ge_of_im (Or.inr (by linarith))),
            foldMap_of_im_gt_one hz (by linarith), norm_cornerInf hy0] at k1
          linarith [hH₁ z.im (by linarith)]
        · by_contra hc
          push Not at hc
          have hq := im_lt_quarter_of_heightOne_gt_one hy0 (by linarith)
          rw [hF1 z (norm_sub_foldCenter_ge_of_im (Or.inl hq)),
            foldMap_of_heightOne (by linarith), norm_cornerZero_sub] at k2
          linarith [hH₂ _ (by linarith : H₂ ≤ heightOne z.re z.im)]
        · by_contra hc
          push Not at hc
          have hq := im_lt_quarter_of_heightOne_gt_one hy0 (by linarith)
          have h0 : ¬ 3 / 5 < heightOne z.re z.im := fun h0 => by
            have := heightHalf_lt_of_heightOne (x := z.re) hy0 (by linarith)
            linarith
          rw [hF1 z (norm_sub_foldCenter_ge_of_im (Or.inl hq)),
            foldMap_of_heightHalf h0 (by linarith), norm_cornerHalf_add] at k3
          linarith [hH₂ _ (by linarith : H₂ ≤ heightOne (1 / 2 - z.re) z.im)]
      have hcomp : IsCompact (F '' hexagonSet H) := by
        refine (isCompact_hexagonSet H).image_of_continuousOn fun z hz => ?_
        exact (hF2 z (hexagonSet_subset (by linarith) hz).1).continuousAt.continuousWithinAt
      have hv1 : v ∈ closure (N ∩ F '' triangleInterior) := hNo.inter_closure ⟨hvN, hvc⟩
      have hv2 : v ∈ F '' hexagonSet H := by
        refine hcomp.isClosed.closure_subset (closure_mono ?_ hv1)
        rintro _ ⟨hN, z, hz, rfl⟩
        exact ⟨z, hK z (triangleInterior_subset hz) hN, rfl⟩
      obtain ⟨z, hzK, rfl⟩ := hv2
      have hzΔ := hexagonSet_subset (by linarith) hzK
      by_cases hzI : z ∈ triangleInterior
      · exact ⟨z, hzI, rfl⟩
      · have := im_eq_zero_of_boundary hwall hzΔ hzI
        linarith
    obtain ⟨z, hz, hzu⟩ := isPreconnected_foldPantsUpper.subset_of_closure_inter_subset hopen hne
      hclos ⟨hu.1, him⟩
    exact ⟨z, triangleInterior_subset hz, hzu⟩
  · have him0 : u.im = 0 := le_antisymm (not_lt.1 him) hu.2
    set a := u.re
    have hua : u = (a : ℂ) := Complex.ext (by simp [a]) (by simp [him0])
    obtain ⟨hn3, hn1, hn2⟩ := (planarFunction_three_neg_iff u).1 hu.1
    rw [hua] at hn3 hn1 hn2
    have e1 : ‖(a : ℂ)‖ = |a| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(a : ℂ) - 3 / 2‖ = |a - 3 / 2| := by
      rw [show (a : ℂ) - 3 / 2 = ((a - 3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    have e3 : ‖(a : ℂ) + 3 / 2‖ = |a + 3 / 2| := by
      rw [show (a : ℂ) + 3 / 2 = ((a + 3 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    rw [e1] at hn3
    rw [e2] at hn1
    rw [e3] at hn2
    obtain ⟨a1, a2⟩ := abs_lt.1 hn3
    rcases lt_or_ge 2 a with ha | ha
    · obtain ⟨y, hy, hya⟩ := exists_foldRho_eq ha a2
      have hw0 : 0 ≤ wallTwo (⟨0, y⟩ : ℂ).re (⟨0, y⟩ : ℂ).im := by
        unfold wallTwo
        change 0 ≤ (0 : ℝ) ^ 2 + y ^ 2 - 0 / 2
        nlinarith [sq_nonneg y]
      refine ⟨⟨0, y⟩, ⟨hy, le_rfl, by norm_num, hw0⟩, ?_⟩
      rw [hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inl (by simp))), foldMap_wall_zero hy, hya,
        hua]
    rcases lt_or_ge a (-2) with hb | hb
    · obtain ⟨y, hy, hya⟩ := exists_foldRho_eq (by linarith : 2 < -a) (by linarith)
      refine ⟨⟨1 / 2, y⟩, ⟨hy, by norm_num, le_rfl, by unfold wallTwo; simp; nlinarith⟩, ?_⟩
      rw [hF1 _ (norm_sub_foldCenter_ge_of_re (Or.inr (by simp; norm_num))),
        foldMap_wall_one hy, hya, hua]
      push_cast
      ring
    have hc1 : -1 < a := by
      by_contra hc
      push Not at hc
      have : |a + 3 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    have hc2 : a < 1 := by
      by_contra hc
      push Not at hc
      have : |a - 3 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    obtain ⟨t, ht, hta⟩ := exists_holeInv_wall_two hc1 hc2
    refine ⟨_, mem_triangleSet_wall_two ht, ?_⟩
    rw [hF1 _ (norm_sub_foldCenter_ge_of_wallTwo (by rw [wallTwo_wall_two_point ht]; norm_num)),
      foldMap_wall_two ht, hta, hua]
    push_cast
    ring

theorem pantsQuotientDiffeo : PantsQuotientDiffeo := by
  obtain ⟨F, hF1, hF2, hF3, hF4, hF5, hF6⟩ := exists_foldCore
  have hwall := fold_hwall hF1
  refine pantsQuotientDiffeo_of_core (U := {z : ℂ | 0 < z.im})
    (isOpen_lt continuous_const Complex.continuous_im) (fun z _ => z.im_pos)
    (fun z hz => (hF2 z hz).contDiffWithinAt) hwall (fun z _ => hF3 z z.im_pos) ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hF5 ((coe_mem_triangleSet_iff z).2 hz)
  · intro z hz z' hz' h
    exact UpperHalfPlane.ext (hF4 ((coe_mem_triangleSet_iff z).2 hz)
      ((coe_mem_triangleSet_iff z').2 hz') h)
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := fold_surjOn hF1 hF2 hF3 hF6 hwall u hu
    exact ⟨⟨z, hz.1⟩, (coe_mem_triangleSet_iff _).1 hz, rfl⟩

end GC.Seifert
