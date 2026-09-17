import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric
open scoped ContDiff Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def halfBallInversionMap (r : ℝ) (p : E × ℝ) : E × ℝ :=
  ((2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) • p.1,
    (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) * (p.2 + r) - r)

omit [InnerProductSpace ℝ E] in
private theorem halfBallInversion_denominator {r : ℝ} {p : E × ℝ}
    (hp : p ≠ (0, -r)) : 0 < ‖p.1‖ ^ 2 + (p.2 + r) ^ 2 := by
  have hnonneg := sq_nonneg ‖p.1‖
  have hnonneg' := sq_nonneg (p.2 + r)
  by_contra hh
  have hsum : ‖p.1‖ ^ 2 + (p.2 + r) ^ 2 = 0 := by linarith
  have hx : ‖p.1‖ = 0 := by nlinarith
  have ht : p.2 = -r := by nlinarith
  exact hp (Prod.ext (norm_eq_zero.mp hx) ht)

private theorem halfBallInversion_denominator_apply (r : ℝ) {p : E × ℝ}
    (hp : p ≠ (0, -r)) :
    ‖(halfBallInversionMap r p).1‖ ^ 2 + ((halfBallInversionMap r p).2 + r) ^ 2 =
      4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  simp only [halfBallInversionMap, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

private theorem halfBallInversionMap_mem {r : ℝ} (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ≠ (0, -r)) : halfBallInversionMap r p ≠ (0, -r) := by
  have heq := halfBallInversion_denominator_apply r hp
  intro hh
  rw [hh] at heq
  have hpos : 0 < 4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) :=
    div_pos (mul_pos (by norm_num) (by
      simpa only [← pow_mul] using (pow_pos (sq_pos_of_ne_zero hr) 2)))
      (halfBallInversion_denominator hp)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), neg_add_cancel, add_zero] at heq
  linarith

private theorem halfBallInversionMap_involutive {r : ℝ} (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ≠ (0, -r)) : halfBallInversionMap r (halfBallInversionMap r p) = p := by
  have hd := (halfBallInversion_denominator hp).ne'
  have heq := halfBallInversion_denominator_apply r hp
  apply Prod.ext
  · change (2 * r ^ 2 / _) • ((2 * r ^ 2 / _) • p.1) = p.1
    rw [heq, smul_smul]
    have hc : (2 * r ^ 2 / (4 * r ^ 4 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2))) *
        (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) = 1 := by
      field_simp
      ring
    rw [hc, one_smul]
  · change (2 * r ^ 2 / _) * ((2 * r ^ 2 / _) * (p.2 + r) - r + r) - r = p.2
    rw [heq]
    field_simp
    ring

private theorem contDiffOn_halfBallInversionMap (r : ℝ) :
    ContDiffOn ℝ ∞ (halfBallInversionMap (E := E) r) {(0, -r)}ᶜ := by
  have hd : ContDiff ℝ ∞ (fun p : E × ℝ => ‖p.1‖ ^ 2 + (p.2 + r) ^ 2) :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).add ((contDiff_snd.add contDiff_const).pow 2)
  have hq : ContDiffOn ℝ ∞ (fun p : E × ℝ => 2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2))
      {(0, -r)}ᶜ := contDiffOn_const.div hd.contDiffOn
        (fun _ hp => (halfBallInversion_denominator hp).ne')
  exact (hq.smul contDiffOn_fst).prodMk
    ((hq.mul (contDiffOn_snd.add contDiffOn_const)).sub contDiffOn_const)

noncomputable def halfBallInversion (r : ℝ) (hr : r ≠ 0) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ where
  toFun := halfBallInversionMap r
  invFun := halfBallInversionMap r
  source := {(0, -r)}ᶜ
  target := {(0, -r)}ᶜ
  map_source' _ hp := halfBallInversionMap_mem hr hp
  map_target' _ hp := halfBallInversionMap_mem hr hp
  left_inv' _ hp := halfBallInversionMap_involutive hr hp
  right_inv' _ hp := halfBallInversionMap_involutive hr hp
  open_source := isOpen_compl_singleton
  open_target := isOpen_compl_singleton
  contMDiffOn_toFun := (contDiffOn_halfBallInversionMap r).contMDiffOn
  contMDiffOn_invFun := (contDiffOn_halfBallInversionMap r).contMDiffOn

theorem halfBallInversion_apply (r : ℝ) (hr : r ≠ 0) (p : E × ℝ) :
    halfBallInversion r hr p =
      ((2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) • p.1,
        (2 * r ^ 2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2)) * (p.2 + r) - r) := rfl

@[simp] theorem halfBallInversion_symm (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).symm = halfBallInversion r hr := rfl

@[simp] theorem halfBallInversion_source (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).source = {(0, -r)}ᶜ := rfl

@[simp] theorem halfBallInversion_target (r : ℝ) (hr : r ≠ 0) :
    (halfBallInversion (E := E) r hr).target = {(0, -r)}ᶜ := rfl

theorem halfBallInversion_snd (r : ℝ) (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr).source) :
    (halfBallInversion r hr p).2 =
      r * (r ^ 2 - (‖p.1‖ ^ 2 + p.2 ^ 2)) / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  rw [halfBallInversion_apply]
  dsimp only
  field_simp
  ring

theorem norm_sq_halfBallInversion (r : ℝ) (hr : r ≠ 0) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr).source) :
    ‖(halfBallInversion r hr p).1‖ ^ 2 + (halfBallInversion r hr p).2 ^ 2 - r ^ 2 =
      -4 * r ^ 3 * p.2 / (‖p.1‖ ^ 2 + (p.2 + r) ^ 2) := by
  have hd := (halfBallInversion_denominator hp).ne'
  simp only [halfBallInversion_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem halfBallInversion_snd_nonneg_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    0 ≤ (halfBallInversion r hr.ne' p).2 ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 := by
  rw [halfBallInversion_snd r hr.ne' hp, le_div_iff₀ (halfBallInversion_denominator hp)]
  simp only [zero_mul, mul_nonneg_iff_of_pos_left hr, sub_nonneg]

theorem norm_sq_halfBallInversion_le_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 ≤ r ^ 2 ↔
      0 ≤ p.2 := by
  rw [← sub_nonpos, norm_sq_halfBallInversion r hr.ne' hp,
    div_le_iff₀ (halfBallInversion_denominator hp), zero_mul]
  have hc : 0 < 4 * r ^ 3 := by positivity
  constructor <;> intro hh <;> nlinarith

theorem halfBallInversion_snd_nonpos_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    (halfBallInversion r hr.ne' p).2 ≤ 0 ↔ r ^ 2 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  rw [halfBallInversion_snd r hr.ne' hp, div_le_iff₀ (halfBallInversion_denominator hp)]
  simp only [zero_mul]
  constructor <;> intro hh <;> nlinarith

theorem norm_sq_halfBallInversion_ge_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    r ^ 2 ≤ ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 ↔
      p.2 ≤ 0 := by
  rw [← sub_nonneg, norm_sq_halfBallInversion r hr.ne' hp,
    le_div_iff₀ (halfBallInversion_denominator hp), zero_mul]
  have hc : 0 < 4 * r ^ 3 := by positivity
  constructor <;> intro hh <;> nlinarith

theorem mem_halfBallInversion_source_of_snd_nonneg {r : ℝ} (hr : 0 < r)
    {p : E × ℝ} (hp : 0 ≤ p.2) : p ∈ (halfBallInversion r hr.ne').source := by
  intro heq
  change p = (0, -r) at heq
  rw [heq] at hp
  exact (not_le_of_gt hr) (by simpa using hp)

theorem halfBall_subset_halfBallInversion_source {r : ℝ} (hr : 0 < r) :
    {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} ⊆
      (halfBallInversion r hr.ne').source := by
  exact fun _ hp => mem_halfBallInversion_source_of_snd_nonneg hr hp.2

theorem halfBallInversion_isImage_halfBall {r : ℝ} (hr : 0 < r) :
    (halfBallInversion (E := E) r hr.ne').toOpenPartialHomeomorph.IsImage
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} := by
  intro p hp
  exact ((norm_sq_halfBallInversion_le_iff hr hp).and
    (halfBallInversion_snd_nonneg_iff hr hp)).trans and_comm

theorem halfBallInversion_image_halfBall {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' ''
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} =
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} := by
  have h := (halfBallInversion_isImage_halfBall (E := E) hr).image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').source ∩
    {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}) =
    (halfBallInversion r hr.ne').source ∩ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} at h
  rw [inter_eq_right.mpr (halfBall_subset_halfBallInversion_source hr)] at h
  exact h

theorem norm_sq_halfBallInversion_eq_iff {r : ℝ} (hr : 0 < r) {p : E × ℝ}
    (hp : p ∈ (halfBallInversion r hr.ne').source) :
    ‖(halfBallInversion r hr.ne' p).1‖ ^ 2 + (halfBallInversion r hr.ne' p).2 ^ 2 = r ^ 2 ↔
      p.2 = 0 := by
  rw [← sub_eq_zero, norm_sq_halfBallInversion r hr.ne' hp, div_eq_zero_iff,
    mul_eq_zero]
  have hc : -4 * r ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hr.ne')
  simp only [hc, false_or, (halfBallInversion_denominator hp).ne', or_false]

theorem halfBallInversion_isImage_disk {r : ℝ} (hr : 0 < r) :
    (halfBallInversion (E := E) r hr.ne').toOpenPartialHomeomorph.IsImage
      (closedBall 0 r ×ˢ {(0 : ℝ)})
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} := by
  intro p hp
  change (‖(halfBallInversion r hr.ne' p).1‖ ^ 2 +
    (halfBallInversion r hr.ne' p).2 ^ 2 = r ^ 2 ∧
    0 ≤ (halfBallInversion r hr.ne' p).2) ↔ _
  rw [norm_sq_halfBallInversion_eq_iff hr hp, halfBallInversion_snd_nonneg_iff hr hp]
  simp only [mem_prod, mem_closedBall_zero_iff, mem_singleton_iff]
  constructor
  · rintro ⟨ht, hx⟩
    rw [ht] at hx
    exact ⟨by nlinarith [norm_nonneg p.1], ht⟩
  · rintro ⟨hx, ht⟩
    refine ⟨ht, ?_⟩
    rw [ht]
    nlinarith [norm_nonneg p.1]

theorem halfBallInversion_image_disk {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' '' (closedBall 0 r ×ˢ {(0 : ℝ)}) =
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} := by
  have h := (halfBallInversion_isImage_disk (E := E) hr).image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').source ∩
    closedBall (0 : E) r ×ˢ {(0 : ℝ)}) =
    (halfBallInversion r hr.ne').target ∩ {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} at h
  rw [inter_eq_right.mpr (show closedBall (0 : E) r ×ˢ {(0 : ℝ)} ⊆
    (halfBallInversion r hr.ne').source from fun p hp =>
      mem_halfBallInversion_source_of_snd_nonneg hr (le_of_eq hp.2.symm)),
    inter_eq_right.mpr (show {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} ⊆
      (halfBallInversion r hr.ne').target from fun _ hp =>
        mem_halfBallInversion_source_of_snd_nonneg hr hp.2)] at h
  exact h

theorem halfBallInversion_image_hemisphere {r : ℝ} (hr : 0 < r) :
    halfBallInversion (E := E) r hr.ne' ''
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} =
      closedBall 0 r ×ˢ {(0 : ℝ)} := by
  have h := (halfBallInversion_isImage_disk (E := E) hr).symm.image_eq
  change halfBallInversion r hr.ne' '' ((halfBallInversion r hr.ne').target ∩
    {p | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2}) =
    (halfBallInversion r hr.ne').source ∩ closedBall (0 : E) r ×ˢ {(0 : ℝ)} at h
  rw [inter_eq_right.mpr (show {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = r ^ 2 ∧ 0 ≤ p.2} ⊆
    (halfBallInversion r hr.ne').target from fun _ hp =>
      mem_halfBallInversion_source_of_snd_nonneg hr hp.2),
    inter_eq_right.mpr (show closedBall (0 : E) r ×ˢ {(0 : ℝ)} ⊆
      (halfBallInversion r hr.ne').source from fun p hp =>
        mem_halfBallInversion_source_of_snd_nonneg hr (le_of_eq hp.2.symm))] at h
  exact h

theorem halfBallInversion_eq_self_of_norm_eq {r : ℝ} (hr : r ≠ 0) {x : E}
    (hx : ‖x‖ = r) : halfBallInversion r hr (x, 0) = (x, 0) := by
  rw [halfBallInversion_apply, hx]
  have hc : 2 * r ^ 2 / (r ^ 2 + r ^ 2) = 1 := by
    field_simp
    ring
  simp only [hc, one_smul, zero_add, one_mul, sub_self]

end PartialDiffeomorph
