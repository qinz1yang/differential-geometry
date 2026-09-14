import DifferentialGeometry.Topology.Attachment.Basic
import DifferentialGeometry.Topology.Embedding.Derivative
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Handle.Embedding
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Handle

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

theorem exists_contDiff_closedCell_extension_bijective_fderiv (m : ℕ)
    {u : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))}
    (hu : Manifold.IsImmersion (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ u) :
    ∃ F : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)),
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      (∀ x : ClosedCell (m + 1), F x.val = u x) ∧
      ∀ x : ClosedCell (m + 1), Function.Bijective (fderiv ℝ F x.val) := by
  obtain ⟨F, hF, hFc, _, hFu⟩ :=
    (closedCellInclusion_isSmoothEmbedding m).exists_contDiff_compact_extension_halfspace
      hu.contMDiff isCompact_univ isOpen_univ (Set.subset_univ _)
  have hcomp : F ∘ (Subtype.val : ClosedCell (m + 1) →
      EuclideanSpace ℝ (Fin (m + 1))) = u := by
    funext x
    exact hFu (Set.mem_univ x)
  refine ⟨F, hF, hFc, fun x => congrFun hcomp x, ?_⟩
  intro x
  let : FiniteDimensional ℝ (TangentSpace (𝓡∂ (m + 1)) x) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (m + 1)))
    infer_instance
  have hi := (hu.isImmersionAt x).injective_mfderiv (by simp)
  rw [← hcomp, mfderiv_comp x
    (hF.contMDiff.mdifferentiable (by simp) x.val)
    ((closedCellInclusion_contMDiff m).mdifferentiable (by simp) x),
    mfderiv_eq_fderiv] at hi
  have hs : Function.Surjective ((fderiv ℝ F x.val).comp
      (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
        (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x)) :=
    LinearMap.surjective_of_injective
      (f := ((fderiv ℝ F x.val).comp
        (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
          (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x)).toLinearMap) hi
  change Function.Surjective (fun v : TangentSpace (𝓡∂ (m + 1)) x =>
    fderiv ℝ F x.val (mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
      (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x v)) at hs
  have hFsurj : Function.Surjective (fderiv ℝ F x.val) :=
    Function.Surjective.of_comp (f := fderiv ℝ F x.val)
      (g := mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
        (Subtype.val : ClosedCell (m + 1) → EuclideanSpace ℝ (Fin (m + 1))) x) hs
  exact ⟨(LinearMap.injective_iff_surjective
    (f := (fderiv ℝ F x.val).toLinearMap)).mpr hFsurj, hFsurj⟩

end DifferentialGeometry.Topology.Handle
