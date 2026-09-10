import DifferentialGeometry.Analysis.Calculus.Derivative.Coordinates.JacobianSign

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem det_fderivWithin_ne_zero_of_inverse
    {S T : Set E} (hS : UniqueDiffOn ℝ S)
    (f g : E → E) (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g T)
    (hmap : MapsTo f S T) (hleft : ∀ x ∈ S, g (f x) = x) {x : E} (hx : x ∈ S) :
    (fderivWithin ℝ f S x).toLinearMap.det ≠ 0 := by
  let A := fderivWithin ℝ f S x
  let B := fderivWithin ℝ g T (f x)
  have hA : HasFDerivWithinAt f A S x :=
    (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt
  have hB : HasFDerivWithinAt g B T (f x) :=
    (hg.differentiableOn (by simp) (f x) (hmap hx)).hasFDerivWithinAt
  have heq : (id : E → E) =ᶠ[𝓝[S] x] g ∘ f := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hleft y hy).symm
  have hBA : B.comp A = ContinuousLinearMap.id ℝ E :=
    (hS x hx).eq ((hB.comp x hA hmap).congr_of_eventuallyEq heq (hleft x hx).symm)
      (hasFDerivAt_id x).hasFDerivWithinAt
  have hprod : B.toLinearMap.det * A.toLinearMap.det = 1 := by
    rw [← LinearMap.det_comp]
    change (B.comp A).toLinearMap.det = 1
    rw [hBA]
    simp
  intro h
  change A.toLinearMap.det = 0 at h
  rw [h, mul_zero] at hprod
  exact zero_ne_one hprod

theorem det_fderivWithin_pos_iff_of_inverse
    {S T : Set E} (hS : UniqueDiffOn ℝ S) (hconn : IsPreconnected S)
    (f g : E → E) (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g T)
    (hmap : MapsTo f S T) (hleft : ∀ x ∈ S, g (f x) = x)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    0 < (fderivWithin ℝ f S x).toLinearMap.det ↔
      0 < (fderivWithin ℝ f S y).toLinearMap.det := by
  have hc : ContinuousOn (fun z ↦ (fderivWithin ℝ f S z).toLinearMap.det) S :=
    ContinuousLinearMap.continuous_det.comp_continuousOn (hf.continuousOn_fderivWithin hS (by simp))
  have hprop (a b : E) (ha : a ∈ S) (hb : b ∈ S)
      (hp : 0 < (fderivWithin ℝ f S a).toLinearMap.det) :
      0 < (fderivWithin ℝ f S b).toLinearMap.det := by
    by_contra hn
    obtain ⟨z, hz, hzero⟩ := hconn.intermediate_value hb ha hc
      (show (0 : ℝ) ∈ Icc (fderivWithin ℝ f S b).toLinearMap.det
        (fderivWithin ℝ f S a).toLinearMap.det from ⟨le_of_not_gt hn, hp.le⟩)
    exact det_fderivWithin_ne_zero_of_inverse hS f g hf hg hmap hleft hz hzero
  exact ⟨hprop x y hx hy, hprop y x hy hx⟩

end Poincare.Analysis
