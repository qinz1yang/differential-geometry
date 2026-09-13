import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

noncomputable section
open Set Filter Manifold
open scoped Topology ContDiff

namespace Complex

private def forward (p z : ℂ) : ℂ := p * (1 + Complex.I * z) / (1 - Complex.I * z)
private def inverse (p w : ℂ) : ℂ := Complex.I * (p - w) / (p + w)

private theorem forward_denom_ne_zero {z : ℂ} (hz : z ≠ -Complex.I) : 1 - Complex.I * z ≠ 0 := by
  intro he
  apply hz
  have hIz : Complex.I * z = 1 := (sub_eq_zero.mp he).symm
  calc
    z = (-Complex.I * Complex.I) * z := by simp
    _ = -Complex.I * (Complex.I * z) := mul_assoc _ _ _
    _ = -Complex.I := by rw [hIz, mul_one]

private theorem inverse_denom_ne_zero {p w : ℂ} (hw : w ≠ -p) : p + w ≠ 0 := by
  intro he
  apply hw
  linear_combination he

private theorem forward_ne_antipode {p z : ℂ} (hp : p ≠ 0) (hz : z ≠ -Complex.I) :
    forward p z ≠ -p := by
  intro he
  have hd := forward_denom_ne_zero hz
  have h := (div_eq_iff hd).mp he
  have hzero : (2 : ℂ) * p = 0 := by
    linear_combination h
  exact (mul_ne_zero (by norm_num) hp) hzero

private theorem inverse_ne_pole {p w : ℂ} (hp : p ≠ 0) (hw : w ≠ -p) :
    inverse p w ≠ -Complex.I := by
  intro he
  have hd := inverse_denom_ne_zero hw
  have h := (div_eq_iff hd).mp he
  have hzero : (2 : ℂ) * Complex.I * p = 0 := by
    linear_combination h
  exact (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hzero

private theorem inverse_forward {p z : ℂ} (hp : p ≠ 0) (hz : z ≠ -Complex.I) :
    inverse p (forward p z) = z := by
  have hd := forward_denom_ne_zero hz
  dsimp only [inverse, forward]
  field_simp [hd, hp]
  ring_nf
  simp only [Complex.I_sq]
  field_simp [hp]

private theorem forward_inverse {p w : ℂ} (hp : p ≠ 0) (hw : w ≠ -p) :
    forward p (inverse p w) = w := by
  have hd := inverse_denom_ne_zero hw
  dsimp only [inverse, forward]
  field_simp [hd, hp]
  ring_nf
  simp only [Complex.I_sq]
  field_simp [hp]
  ring

private theorem norm_sq_difference (z : ℂ) :
    ‖1 - Complex.I * z‖ ^ 2 - ‖1 + Complex.I * z‖ ^ 2 = 4 * z.im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  ring

private theorem norm_forward_le_one_iff {p z : ℂ} (hp : ‖p‖ = 1) (hz : z ≠ -Complex.I) :
    ‖forward p z‖ ≤ 1 ↔ 0 ≤ z.im := by
  have hd : 0 < ‖1 - Complex.I * z‖ := norm_pos_iff.mpr (forward_denom_ne_zero hz)
  rw [forward, norm_div, norm_mul, hp, one_mul, div_le_one hd,
    ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor <;> intro h <;> nlinarith [norm_sq_difference z]

private theorem norm_forward_lt_one_iff {p z : ℂ} (hp : ‖p‖ = 1) (hz : z ≠ -Complex.I) :
    ‖forward p z‖ < 1 ↔ 0 < z.im := by
  have hd : 0 < ‖1 - Complex.I * z‖ := norm_pos_iff.mpr (forward_denom_ne_zero hz)
  rw [forward, norm_div, norm_mul, hp, one_mul, div_lt_one hd,
    ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor <;> intro h <;> nlinarith [norm_sq_difference z]

private theorem norm_forward_eq_one_iff {p z : ℂ} (hp : ‖p‖ = 1) (hz : z ≠ -Complex.I) :
    ‖forward p z‖ = 1 ↔ z.im = 0 := by
  constructor
  · intro he
    have hle := (norm_forward_le_one_iff hp hz).mp he.le
    have hnot : ¬ 0 < z.im := by rw [← norm_forward_lt_one_iff hp hz, he]; exact lt_irrefl _
    exact le_antisymm (le_of_not_gt hnot) hle
  · intro he
    apply le_antisymm ((norm_forward_le_one_iff hp hz).mpr he.ge)
    apply le_of_not_gt
    rw [norm_forward_lt_one_iff hp hz, he]
    exact lt_irrefl _

private theorem hasDerivAt_forward (p : ℂ) {z : ℂ} (hz : z ≠ -Complex.I) :
    HasDerivAt (forward p) (2 * Complex.I * p / (1 - Complex.I * z) ^ 2) z := by
  have hI : HasDerivAt (fun w => Complex.I * w) Complex.I z := hasDerivAt_const_mul Complex.I
  have hA : HasDerivAt (fun w => 1 + Complex.I * w) Complex.I z := by
    convert! HasDerivAt.add (hasDerivAt_const z 1) hI using 1
    simp
  have hN : HasDerivAt (fun w => p * (1 + Complex.I * w)) (p * Complex.I) z :=
    (hasDerivAt_const_mul p).comp z hA
  have hD : HasDerivAt (fun w => 1 - Complex.I * w) (-Complex.I) z := by
    convert! HasDerivAt.sub (hasDerivAt_const z 1) hI using 1
    simp
  convert! hN.div hD (forward_denom_ne_zero hz) using 1
  ring

private theorem hasDerivAt_inverse (p : ℂ) {w : ℂ} (hw : w ≠ -p) :
    HasDerivAt (inverse p) (-2 * Complex.I * p / (p + w) ^ 2) w := by
  have hA : HasDerivAt (fun z => p - z) (-1) w := by
    convert! HasDerivAt.sub (hasDerivAt_const w p) (hasDerivAt_id w) using 1
    simp
  have hN : HasDerivAt (fun z => Complex.I * (p - z)) (-Complex.I) w := by
    convert! (hasDerivAt_const_mul Complex.I).comp w hA using 1
    ring
  have hD : HasDerivAt (fun z => p + z) 1 w := by
    convert! HasDerivAt.add (hasDerivAt_const w p) (hasDerivAt_id w) using 1
    simp
  convert! hN.div hD (inverse_denom_ne_zero hw) using 1
  ring

private theorem contDiffOn_forward (p : ℂ) : ContDiffOn ℂ ∞ (forward p) {z | z ≠ -Complex.I} := by
  exact (contDiffOn_const.mul (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id))).div
    (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id))
    (fun z hz => forward_denom_ne_zero hz)

private theorem contDiffOn_inverse (p : ℂ) : ContDiffOn ℂ ∞ (inverse p) {w | w ≠ -p} := by
  exact (contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id)).div
    (contDiffOn_const.add contDiffOn_id) (fun w hw => inverse_denom_ne_zero hw)

def diskBoundaryChart (p : ℂ) (hp : ‖p‖ = 1) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ := by
  have hp₀ : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero)
  exact {
    toFun := forward p
    invFun := inverse p
    source := {z | z ≠ -Complex.I}
    target := {w | w ≠ -p}
    map_source' := fun _ hz => forward_ne_antipode hp₀ hz
    map_target' := fun _ hw => inverse_ne_pole hp₀ hw
    left_inv' := fun _ hz => inverse_forward hp₀ hz
    right_inv' := fun _ hw => forward_inverse hp₀ hw
    open_source := isOpen_ne
    open_target := isOpen_ne
    contMDiffOn_toFun := ((contDiffOn_forward p).restrict_scalars ℝ).contMDiffOn
    contMDiffOn_invFun := ((contDiffOn_inverse p).restrict_scalars ℝ).contMDiffOn }

theorem diskBoundaryChart_source (p : ℂ) (hp : ‖p‖ = 1) :
    (diskBoundaryChart p hp).source = {z | z ≠ -Complex.I} := rfl

theorem diskBoundaryChart_target (p : ℂ) (hp : ‖p‖ = 1) :
    (diskBoundaryChart p hp).target = {w | w ≠ -p} := rfl

theorem diskBoundaryChart_apply (p : ℂ) (hp : ‖p‖ = 1) (z : ℂ) :
    diskBoundaryChart p hp z = p * (1 + Complex.I * z) / (1 - Complex.I * z) := rfl

theorem diskBoundaryChart_symm_apply (p : ℂ) (hp : ‖p‖ = 1) (w : ℂ) :
    (diskBoundaryChart p hp).symm w = Complex.I * (p - w) / (p + w) := rfl

theorem diskBoundaryChart_zero (p : ℂ) (hp : ‖p‖ = 1) : diskBoundaryChart p hp 0 = p := by
  simp only [diskBoundaryChart_apply, mul_zero, add_zero, sub_zero, mul_one, div_one]

theorem hasDerivAt_diskBoundaryChart (p : ℂ) (hp : ‖p‖ = 1) {z : ℂ}
    (hz : z ∈ (diskBoundaryChart p hp).source) :
    HasDerivAt (diskBoundaryChart p hp) (2 * Complex.I * p / (1 - Complex.I * z) ^ 2) z :=
  hasDerivAt_forward p hz

theorem hasDerivAt_diskBoundaryChart_symm (p : ℂ) (hp : ‖p‖ = 1) {w : ℂ}
    (hw : w ∈ (diskBoundaryChart p hp).target) :
    HasDerivAt (diskBoundaryChart p hp).symm (-2 * Complex.I * p / (p + w) ^ 2) w :=
  hasDerivAt_inverse p hw

theorem deriv_diskBoundaryChart_ne_zero (p : ℂ) (hp : ‖p‖ = 1) {z : ℂ}
    (hz : z ∈ (diskBoundaryChart p hp).source) : deriv (diskBoundaryChart p hp) z ≠ 0 := by
  rw [(hasDerivAt_diskBoundaryChart p hp hz).deriv]
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (norm_ne_zero_iff.mp (by rw [hp]; exact one_ne_zero))
  · exact pow_ne_zero 2 (forward_denom_ne_zero hz)

theorem norm_diskBoundaryChart_le_one_iff (p : ℂ) (hp : ‖p‖ = 1) {z : ℂ}
    (hz : z ∈ (diskBoundaryChart p hp).source) : ‖diskBoundaryChart p hp z‖ ≤ 1 ↔ 0 ≤ z.im :=
  norm_forward_le_one_iff hp hz

theorem norm_diskBoundaryChart_lt_one_iff (p : ℂ) (hp : ‖p‖ = 1) {z : ℂ}
    (hz : z ∈ (diskBoundaryChart p hp).source) : ‖diskBoundaryChart p hp z‖ < 1 ↔ 0 < z.im :=
  norm_forward_lt_one_iff hp hz

theorem norm_diskBoundaryChart_eq_one_iff (p : ℂ) (hp : ‖p‖ = 1) {z : ℂ}
    (hz : z ∈ (diskBoundaryChart p hp).source) : ‖diskBoundaryChart p hp z‖ = 1 ↔ z.im = 0 :=
  norm_forward_eq_one_iff hp hz

private theorem ne_neg_I_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z ≠ -Complex.I := by
  intro he
  rw [he] at hz
  norm_num at hz

theorem diskBoundaryChart_image_upperHalfPlane (p : ℂ) (hp : ‖p‖ = 1) :
    diskBoundaryChart p hp '' {z | 0 < z.im} = Metric.ball (0 : ℂ) 1 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr ((norm_diskBoundaryChart_lt_one_iff p hp
      (ne_neg_I_of_im_nonneg hz.le)).mpr hz)
  · intro hw
    have hn : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have ht : w ∈ (diskBoundaryChart p hp).target := by
      intro he
      rw [he, norm_neg, hp] at hn
      exact (lt_irrefl (1 : ℝ)) hn
    have hs : (diskBoundaryChart p hp).symm w ∈ (diskBoundaryChart p hp).source :=
      (diskBoundaryChart p hp).toPartialEquiv.map_target ht
    have hi : diskBoundaryChart p hp ((diskBoundaryChart p hp).symm w) = w :=
      (diskBoundaryChart p hp).toPartialEquiv.right_inv ht
    refine ⟨(diskBoundaryChart p hp).symm w, ?_, hi⟩
    apply (norm_diskBoundaryChart_lt_one_iff p hp hs).mp
    rwa [hi]

theorem diskBoundaryChart_image_closed_upperHalfPlane (p : ℂ) (hp : ‖p‖ = 1) :
    diskBoundaryChart p hp '' {z | 0 ≤ z.im} = Metric.closedBall (0 : ℂ) 1 \ {-p} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hs : z ∈ (diskBoundaryChart p hp).source := ne_neg_I_of_im_nonneg hz
    refine ⟨mem_closedBall_zero_iff.mpr ((norm_diskBoundaryChart_le_one_iff p hp hs).mpr hz), ?_⟩
    exact (diskBoundaryChart p hp).toOpenPartialHomeomorph.map_source hs
  · rintro ⟨hw, ht⟩
    have hs : (diskBoundaryChart p hp).symm w ∈ (diskBoundaryChart p hp).source :=
      (diskBoundaryChart p hp).toPartialEquiv.map_target ht
    have hi : diskBoundaryChart p hp ((diskBoundaryChart p hp).symm w) = w :=
      (diskBoundaryChart p hp).toPartialEquiv.right_inv ht
    refine ⟨(diskBoundaryChart p hp).symm w, ?_, hi⟩
    apply (norm_diskBoundaryChart_le_one_iff p hp hs).mp
    rw [hi]
    exact mem_closedBall_zero_iff.mp hw

theorem diskBoundaryChart_image_real_axis (p : ℂ) (hp : ‖p‖ = 1) :
    diskBoundaryChart p hp '' {z | z.im = 0} = Metric.sphere (0 : ℂ) 1 \ {-p} := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hs : z ∈ (diskBoundaryChart p hp).source := ne_neg_I_of_im_nonneg hz.ge
    refine ⟨?_, (diskBoundaryChart p hp).toOpenPartialHomeomorph.map_source hs⟩
    exact mem_sphere_zero_iff_norm.mpr ((norm_diskBoundaryChart_eq_one_iff p hp hs).mpr hz)
  · rintro ⟨hw, ht⟩
    have hs : (diskBoundaryChart p hp).symm w ∈ (diskBoundaryChart p hp).source :=
      (diskBoundaryChart p hp).toPartialEquiv.map_target ht
    have hi : diskBoundaryChart p hp ((diskBoundaryChart p hp).symm w) = w :=
      (diskBoundaryChart p hp).toPartialEquiv.right_inv ht
    refine ⟨(diskBoundaryChart p hp).symm w, ?_, hi⟩
    apply (norm_diskBoundaryChart_eq_one_iff p hp hs).mp
    rw [hi]
    exact mem_sphere_zero_iff_norm.mp hw


end Complex
