import DifferentialGeometry.Topology.LoopSpace.AnnulusSectors
import DifferentialGeometry.Analysis.Integration.Measure.ComplexNullLines
import Mathlib.MeasureTheory.Constructions.Polish.Basic



noncomputable section

open Set MeasureTheory Metric
open DifferentialGeometry.Analysis
open scoped Topology

namespace DifferentialGeometry.Topology



theorem unitSquare_ae_eq_sectors :
    unitSquare =ᵐ[volume] (annulusSector 0 ∪ annulusSector (1 / 2) : Set ℂ) := by
  filter_upwards [ae_complex_re_ne 0, ae_complex_re_ne 1, ae_complex_im_ne 0,
    ae_complex_im_ne (1 / 2), ae_complex_im_ne 1] with z hr₀ hr₁ hi₀ hiₘ hi₁
  apply propext
  constructor
  · rintro ⟨hr, hi⟩
    have hro : z.re ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hr.1 hr₀.symm, lt_of_le_of_ne hr.2 hr₁⟩
    by_cases hθ : z.im < 1 / 2
    · exact Or.inl ⟨hro, lt_of_le_of_ne hi.1 hi₀.symm, by simpa using hθ⟩
    · exact Or.inr ⟨hro, lt_of_le_of_ne (le_of_not_gt hθ) hiₘ.symm,
        by have h := lt_of_le_of_ne hi.2 hi₁; linarith⟩
  · rintro (h | h)
    · exact annulusSector_subset_square le_rfl (by norm_num) h
    · exact annulusSector_subset_square (by norm_num) (by norm_num) h

theorem disjoint_annulusSectors : Disjoint (annulusSector 0) (annulusSector (1 / 2)) := by
  apply disjoint_left.mpr
  intro z hz hw
  linarith [hz.2.2, hw.2.1]


theorem annulusPolarMap_injOn_sector (a : ℝ) : InjOn annulusPolarMap (annulusSector a) := by
  intro z hz w hw heq
  apply dist_eq_zero.mp
  have h := annulusPolarMap_inverse_dist_le (Ioo_subset_Icc_self hz.1)
    (Ioo_subset_Icc_self hw.1) (Ioo_subset_Icc_self hz.2) (Ioo_subset_Icc_self hw.2)
  rw [heq, dist_self, mul_zero] at h
  exact le_antisymm h dist_nonneg

theorem measurableSet_annulusSector_image (a : ℝ) :
    MeasurableSet (annulusPolarMap '' annulusSector a) :=
  (isOpen_annulusSector a).measurableSet.image_of_continuousOn_injOn
    contDiff_annulusPolarMap.continuous.continuousOn (annulusPolarMap_injOn_sector a)

theorem annulusSector_image_norm {a : ℝ} {z : ℂ}
    (hz : z ∈ annulusPolarMap '' annulusSector a) : 1 / 2 < ‖z‖ ∧ ‖z‖ < 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [norm_annulusPolarMap (Ioo_subset_Icc_self hw.1)]
  constructor <;> linarith [hw.1.1, hw.1.2]

theorem disjoint_annulusSector_images :
    Disjoint (annulusPolarMap '' annulusSector 0) (annulusPolarMap '' annulusSector (1 / 2)) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx' : x ∈ {z : ℂ | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Ico (0 : ℝ) 1} :=
    ⟨Ioo_subset_Icc_self hx.1, hx.2.1.le, by linarith [hx.2.2]⟩
  have hy' : y ∈ {z : ℂ | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Ico (0 : ℝ) 1} :=
    ⟨Ioo_subset_Icc_self hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  have hxy := annulusPolarMap_injective_on_period hx' hy' heq.symm
  exact disjoint_annulusSectors.le_bot ⟨hx, hxy ▸ hy⟩



theorem mem_annulusSector_images_of_im_ne_zero {z : ℂ}
    (hz : 1 / 2 < ‖z‖ ∧ ‖z‖ < 1) (hzi : z.im ≠ 0) :
    z ∈ annulusPolarMap '' annulusSector 0 ∪ annulusPolarMap '' annulusSector (1 / 2) := by
  let θ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z)
  obtain ⟨t, ht, htθ⟩ := AddCircle.eq_coe_Ico θ
  have hcircle : AddCircle.toCircle (t : loopCircle) = radialDirection z := by
    rw [htθ, ← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply _
  let w : ℂ := ⟨2 * ‖z‖ - 1, t⟩
  have hφ : annulusPolarMap w = z := by
    change ((2 * ‖z‖ - 1 + 1) / 2 : ℝ) • (AddCircle.toCircle (t : loopCircle) : ℂ) = z
    rw [hcircle, show (2 * ‖z‖ - 1 + 1) / 2 = ‖z‖ by ring]
    exact radialDirection_reconstruct z
  have ht₀ : t ≠ 0 := by
    intro heq
    apply hzi
    rw [← hφ]
    simp [annulusPolarMap, w, heq]
  have htₘ : t ≠ 1 / 2 := by
    intro heq
    apply hzi
    have hc : (AddCircle.toCircle (t : loopCircle) : ℂ) = -1 := by
      rw [heq, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one,
        show 2 * Real.pi * (1 / 2) = Real.pi by ring, Complex.exp_pi_mul_I]
    rw [← hφ]
    change (((2 * ‖z‖ - 1 + 1) / 2 : ℝ) • (AddCircle.toCircle (t : loopCircle) : ℂ)).im = 0
    rw [hc]
    simp
  have hwr : w.re ∈ Ioo (0 : ℝ) 1 := by
    change 0 < 2 * ‖z‖ - 1 ∧ 2 * ‖z‖ - 1 < 1
    constructor <;> linarith [hz.1, hz.2]
  by_cases htlt : t < 1 / 2
  · exact Or.inl ⟨w, ⟨hwr, lt_of_le_of_ne ht.1 ht₀.symm, by simpa [w] using htlt⟩, hφ⟩
  · exact Or.inr ⟨w, ⟨hwr, lt_of_le_of_ne (le_of_not_gt htlt) htₘ.symm,
      by dsimp [w]; linarith [ht.2]⟩, hφ⟩



theorem closedDisk_ae_eq_annulusPieces :
    closedBall (0 : ℂ) 1 =ᵐ[volume]
      (closedBall (0 : ℂ) (1 / 2) ∪
        (annulusPolarMap '' annulusSector 0 ∪ annulusPolarMap '' annulusSector (1 / 2)) : Set ℂ) := by
  have hcircle : ∀ᵐ z : ℂ ∂volume, ‖z‖ ≠ 1 := by
    rw [ae_iff]
    convert MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) 1 using 1
    congr 1
    ext z
    simp
  filter_upwards [hcircle, ae_complex_im_ne 0] with z hz₁ hzi
  apply propext
  constructor
  · intro hz
    change dist z 0 ≤ 1 at hz
    have hzn : ‖z‖ ≤ 1 := by simpa only [dist_zero_right] using hz
    by_cases hhalf : ‖z‖ ≤ 1 / 2
    · exact Or.inl (by simpa only [mem_closedBall, dist_zero_right] using hhalf)
    · exact Or.inr (mem_annulusSector_images_of_im_ne_zero
        ⟨lt_of_not_ge hhalf, lt_of_le_of_ne hzn hz₁⟩ hzi)
  · rintro (hz | hz | hz)
    · exact closedBall_subset_closedBall (by norm_num : (1 / 2 : ℝ) ≤ 1) hz
    · change dist z 0 ≤ 1
      rw [dist_zero_right]
      exact (annulusSector_image_norm hz).2.le
    · change dist z 0 ≤ 1
      rw [dist_zero_right]
      exact (annulusSector_image_norm hz).2.le

theorem disjoint_halfDisk_annulusSector (a : ℝ) :
    Disjoint (closedBall (0 : ℂ) (1 / 2)) (annulusPolarMap '' annulusSector a) := by
  apply disjoint_left.mpr
  intro z hz hzi
  have hzn : ‖z‖ ≤ 1 / 2 := by simpa only [mem_closedBall, dist_zero_right] using hz
  exact (not_lt_of_ge hzn) (annulusSector_image_norm hzi).1

end DifferentialGeometry.Topology
