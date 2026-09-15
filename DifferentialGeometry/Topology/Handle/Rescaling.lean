import DifferentialGeometry.Analysis.Calculus.Rescaling
import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Embedding.LinearEquiv
import DifferentialGeometry.Topology.Embedding.Stability
import DifferentialGeometry.Topology.Handle.Embedding
import Mathlib.Analysis.Normed.Operator.Banach

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_closedCell_rescaling_eventually_isSmoothEmbedding (m : ℕ)
    {f : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hf : ContDiff ℝ ∞ f) (a : EuclideanSpace ℝ (Fin (m + 1)))
    (hderiv : Function.Bijective (fderiv ℝ f a)) :
    ∃ L : ℝ × ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡 (m + 1)) ∞ L ∧
      (∀ x : ClosedCell (m + 1), L (0, x) = fderiv ℝ f a x.val) ∧
      (∀ s (x : ClosedCell (m + 1)), s • L (s, x) = f (a + s • x.val) - f a) ∧
      (∀ s, s ≠ 0 → ∀ x : ClosedCell (m + 1),
        L (s, x) = s⁻¹ • (f (a + s • x.val) - f a)) ∧
      ∀ᶠ s in 𝓝 (0 : ℝ), Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
        (fun x => L (s, x)) := by
  obtain ⟨R, hR, hzero, hscale, hnonzero, _⟩ :=
    DifferentialGeometry.Analysis.Calculus.exists_contDiff_rescaling hf a
  let L : ℝ × ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => R (p.1, p.2.val)
  have hL : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (m + 1))) (𝓡 (m + 1)) ∞ L :=
    hR.comp_contMDiff (contMDiff_fst.prodMk_space
      ((closedCellInclusion_contMDiff m).comp contMDiff_snd))
  let e : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ f a)
      (LinearMap.ker_eq_bot.mpr hderiv.1) (LinearMap.range_eq_top.mpr hderiv.2)
  have hLe : (fun x : ClosedCell (m + 1) => L (0, x)) =
      e ∘ (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) := by
    funext x
    exact hzero x.val
  have he : Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (fun x => L (0, x)) := by
    rw [hLe]
    exact (closedCellInclusion_isSmoothEmbedding m).continuousLinearEquiv_comp e
  exact ⟨L, hL, fun x => hzero x.val, fun s x => hscale s x.val,
    fun s hs x => hnonzero s hs x.val,
    Manifold.eventually_isSmoothEmbedding_halfspace hL he⟩

end DifferentialGeometry.Topology.Handle
