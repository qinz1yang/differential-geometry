import DifferentialGeometry.Bundle.SmoothSubbundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {m n : WithTop ℕ∞} [ContMDiffVectorBundle n F V I] [IsContMDiffRiemannianBundle I m F V]

namespace ContMDiffVectorSubbundle

theorem isContMDiffRiemannianBundle
    (S : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := n)) (hmn : m ≤ n) :
    letI := S.totalSpaceTopology
    letI := S.fiberBundle
    letI := S.vector_bundle
    IsContMDiffRiemannianBundle I m (Fin S.rank → ℝ) (fun x => S.fiber x) := by
  let _ := S.totalSpaceTopology
  let _ := S.fiberBundle
  let _ := S.vector_bundle
  let _ := S.contMDiffVectorBundle
  obtain ⟨g, hg, hinner⟩ :=
    IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := m) (F := F) (E := V)
  have hinc := ContMDiff.clm_bundle_of_map
    (φ := fun x => (S.fiber x).subtypeL) (S.contMDiff_subtypeVal.of_le hmn)
  refine ⟨fun x => (g x).bilinearComp (S.fiber x).subtypeL (S.fiber x).subtypeL,
    hg.clm_bundle_bilinearComp hinc hinc, ?_⟩
  intro x v w
  exact hinner x v w

end ContMDiffVectorSubbundle
