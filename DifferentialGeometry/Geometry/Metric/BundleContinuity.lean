import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Topology.VectorBundle.Riemannian

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞ω}

theorem IsContMDiffRiemannianBundle.isContinuousRiemannianBundle
    [h : IsContMDiffRiemannianBundle I n F V] : IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, hinner⟩ := h.exists_contMDiff
  exact ⟨g, hg.continuous, hinner⟩
