import DifferentialGeometry.Topology.Manifold.HalfSpaceExtension
import DifferentialGeometry.Topology.Manifold.SmoothExtension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold ComplexConjugate

namespace DifferentialGeometry.Topology

private def diskBoundaryCoordinates (p z : ℂ) : ℝ × ℝ :=
  ((conj p * z).im, 1 - ‖z‖ ^ 2)

private def diskBoundaryInverse (p : ℂ) (q : ℝ × ℝ) : ℂ :=
  p * ((Real.sqrt (1 - q.2 - q.1 ^ 2) : ℂ) + q.1 * Complex.I)

private theorem diskBoundaryCoordinates_contDiff (p : ℂ) :
    ContDiff ℝ ∞ (diskBoundaryCoordinates p) :=
  (Complex.imCLM.contDiff.comp (contDiff_const.mul contDiff_id)).prodMk
    (contDiff_const.sub (contDiff_norm_sq ℝ))

private theorem diskBoundaryInverse_contDiffOn (p : ℂ) :
    ContDiffOn ℝ ∞ (diskBoundaryInverse p)
      {q : ℝ × ℝ | 0 < 1 - q.2 - q.1 ^ 2} := by
  have hs : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => Real.sqrt (1 - q.2 - q.1 ^ 2))
      {q : ℝ × ℝ | 0 < 1 - q.2 - q.1 ^ 2} :=
    ((contDiff_const.sub contDiff_snd).sub (contDiff_fst.pow 2)).contDiffOn.sqrt
      (fun q hq => ne_of_gt hq)
  have hr := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  exact contDiffOn_const.mul
    (hr.add ((Complex.ofRealCLM.contDiff.comp contDiff_fst).contDiffOn.mul contDiffOn_const))

private theorem diskBoundaryInverse_mem_closedBall {p : ℂ} (hp : ‖p‖ = 1)
    {q : ℝ × ℝ} (hq : 0 < 1 - q.2 - q.1 ^ 2) (hqt : 0 ≤ q.2) :
    diskBoundaryInverse p q ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hsq : ‖diskBoundaryInverse p q‖ ^ 2 = 1 - q.2 := by
    rw [diskBoundaryInverse, norm_mul, hp, one_mul, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add]
    nlinarith [Real.sq_sqrt hq.le]
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg (diskBoundaryInverse p q)]

private theorem diskBoundaryInverse_left_inv {p z : ℂ} (hp : ‖p‖ = 1)
    (hz : 0 < (conj p * z).re) :
    diskBoundaryInverse p (diskBoundaryCoordinates p z) = z := by
  have hnorm : ‖conj p * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_conj, hp, one_mul]
  have hrad : 1 - (1 - ‖z‖ ^ 2) - (conj p * z).im ^ 2 = (conj p * z).re ^ 2 := by
    rw [sub_sub_cancel, ← hnorm]
    exact Complex.sq_norm_sub_sq_im _
  have hunit : p * conj p = 1 := by rw [Complex.mul_conj', hp]; norm_num
  change p * ((Real.sqrt (1 - (1 - ‖z‖ ^ 2) - (conj p * z).im ^ 2) : ℂ) +
    (conj p * z).im * Complex.I) = z
  rw [hrad, Real.sqrt_sq hz.le, Complex.re_add_im, ← mul_assoc, hunit, one_mul]

private theorem diskBoundaryCoordinates_self {p : ℂ} (hp : ‖p‖ = 1) :
    diskBoundaryCoordinates p p = (0, 0) := by
  have hunit : conj p * p = 1 := by rw [Complex.conj_mul', hp]; norm_num
  simp [diskBoundaryCoordinates, hunit, hp]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiffOn_extension_across_closedDisk_boundary
    {f : ℂ → M} {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hpU : p ∈ U)
    (hp : ‖p‖ = 1)
    (hf : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ f (U ∩ Metric.closedBall (0 : ℂ) 1)) :
    ∃ V : Set ℂ, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ∃ g : ℂ → M, ContMDiffOn 𝓘(ℝ, ℂ) I ∞ g V ∧
        EqOn g f (V ∩ Metric.closedBall (0 : ℂ) 1) := by
  let A := {q : ℝ × ℝ | 0 < 1 - q.2 - q.1 ^ 2}
  have hA : IsOpen A := isOpen_lt continuous_const (by fun_prop)
  have hi : ContDiffOn ℝ ∞ (diskBoundaryInverse p) A := diskBoundaryInverse_contDiffOn p
  let W := A ∩ diskBoundaryInverse p ⁻¹' U
  have hW : IsOpen W := hi.continuousOn.isOpen_inter_preimage hA hU
  have h0W : ((0, 0) : ℝ × ℝ) ∈ W := by
    constructor
    · norm_num [A]
    · simpa [diskBoundaryInverse] using hpU
  have hfi : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (f ∘ diskBoundaryInverse p)
      (W ∩ (univ ×ˢ Ici (0 : ℝ))) := by
    apply hf.comp (hi.mono (inter_subset_left.trans inter_subset_left)).contMDiffOn
    intro q hq
    exact ⟨hq.1.2, diskBoundaryInverse_mem_closedBall hp hq.1.1 hq.2.2⟩
  obtain ⟨B, hB, h0B, _, g, hg, heq⟩ :=
    exists_contMDiffOn_extension_across_halfSpace_boundary hW h0W hfi
  let V := U ∩ {z : ℂ | 0 < (conj p * z).re} ∩ diskBoundaryCoordinates p ⁻¹' B
  have hV : IsOpen V := (hU.inter (isOpen_lt continuous_const (by fun_prop))).inter
    (hB.preimage (diskBoundaryCoordinates_contDiff p).continuous)
  have hpV : p ∈ V := by
    refine ⟨⟨hpU, ?_⟩, ?_⟩
    · have hunit : conj p * p = 1 := by rw [Complex.conj_mul', hp]; norm_num
      change 0 < (conj p * p).re
      rw [hunit]
      norm_num
    · change diskBoundaryCoordinates p p ∈ B
      rwa [diskBoundaryCoordinates_self hp]
  refine ⟨V, hV, hpV, fun z hz => hz.1.1, g ∘ diskBoundaryCoordinates p,
    hg.comp (diskBoundaryCoordinates_contDiff p).contMDiff.contMDiffOn
      (fun z hz => hz.2), ?_⟩
  intro z hz
  have hzt : 0 ≤ (diskBoundaryCoordinates p z).2 := by
    have hzn : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    change 0 ≤ 1 - ‖z‖ ^ 2
    nlinarith [norm_nonneg z]
  change g (diskBoundaryCoordinates p z) = f z
  rw [heq ⟨hz.1.2, mem_univ _, hzt⟩]
  exact congrArg f (diskBoundaryInverse_left_inv hp hz.1.1.2)

theorem exists_contMDiffOn_extension_closedDisk
    {f : ℂ → M} (hf : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ f (Metric.closedBall (0 : ℂ) 1)) :
    ∃ g : ℂ → M, Continuous g ∧ EqOn g f (Metric.closedBall (0 : ℂ) 1) ∧
      ∃ N : Set ℂ, IsOpen N ∧ Metric.closedBall (0 : ℂ) 1 ⊆ N ∧
        ContMDiffOn 𝓘(ℝ, ℂ) I ∞ g N := by
  obtain ⟨g, hg, heq, N, hN, hKN, hgs⟩ :=
    exists_contMDiffOn_extension_closedBall (I := I) (n := ⊤) (0 : ℂ)
      (by norm_num : (0 : ℝ) ≤ 1) (fun z => f z) (by
        intro x
        by_cases hx : ‖(x : ℂ)‖ < 1
        · refine ⟨f, Metric.ball (0 : ℂ) 1, Metric.isOpen_ball, ?_,
            hf.mono Metric.ball_subset_closedBall, fun y _ => rfl⟩
          simpa only [Metric.mem_ball, dist_zero_right] using hx
        · have hxn : ‖(x : ℂ)‖ = 1 := by
            have hle : ‖(x : ℂ)‖ ≤ 1 := by
              simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
            exact le_antisymm hle (le_of_not_gt hx)
          obtain ⟨V, hV, hxV, _, F, hF, hFf⟩ :=
            exists_contMDiffOn_extension_across_closedDisk_boundary isOpen_univ
              (mem_univ (x : ℂ)) hxn (by simpa only [univ_inter] using hf)
          exact ⟨F, V, hV, hxV, hF, fun y hy => hFf ⟨hy, y.property⟩⟩)
  exact ⟨g, hg, fun z hz => heq ⟨z, hz⟩, N, hN, hKN, hgs⟩

end DifferentialGeometry.Topology
