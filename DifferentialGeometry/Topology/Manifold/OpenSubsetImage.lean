import DifferentialGeometry.Topology.Embedding.CompactFrontier
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Handle.Manifold
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology.Handle (chartedSpaceOfHomeomorph isManifoldOfHomeomorph
  contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
  contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph)
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E F H H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem exists_manifold_image_open_subtype (U : TopologicalSpace.Opens M) (K : Set U)
    [ChartedSpace H K] [IsManifold I ∞ K]
    (hclosed : IsClosed (Subtype.val '' K : Set M))
    (hinduced : IsSmoothEmbedding I J ∞ (Subtype.val : K → U))
    (hinterior : (Subtype.val : K → U) '' I.interior K = interior K) :
    ∃ charts : ChartedSpace H (Subtype.val '' K : Set M),
      letI := charts
      IsManifold I ∞ (Subtype.val '' K : Set M) ∧
      IsSmoothEmbedding I J ∞ (Subtype.val : (Subtype.val '' K : Set M) → M) ∧
      (Subtype.val : (Subtype.val '' K : Set M) → M) ''
        I.interior (Subtype.val '' K : Set M) = interior (Subtype.val '' K : Set M) ∧
      (Subtype.val : (Subtype.val '' K : Set M) → M) ''
        I.boundary (Subtype.val '' K : Set M) = frontier (Subtype.val '' K : Set M) := by
  let R : Set M := Subtype.val '' K
  let e : K ≃ₜ R := _root_.Topology.IsEmbedding.subtypeVal.homeomorphImage K
  let _ : ChartedSpace H R := chartedSpaceOfHomeomorph e.symm
  let _ : IsManifold I ∞ R := isManifoldOfHomeomorph I e.symm
  let D : R ≃ₘ⟮I, I⟯ K :=
    { toEquiv := e.symm.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e.symm I ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e.symm I ∞ }
  have hval (x : K) : (D.symm x).val = x.val.val := rfl
  have hval' (x : R) : (D x).val.val = x.val := by
    have h := hval (D x)
    have hh : x.val = (D x).val.val := by simpa only [D.symm_apply_apply] using h
    exact hh.symm
  have hinterior' : (Subtype.val : R → M) '' I.interior R = interior R := by
    rw [← D.symm.image_interior (by simp), image_image]
    change (fun x : K => x.val.val) '' I.interior K = interior R
    rw [← image_image, hinterior]
    exact Embedding.image_interior_of_isOpenEmbedding U.isOpenEmbedding' K
  refine ⟨inferInstance, inferInstance, ?_, hinterior', ?_⟩
  · have h := isSmoothEmbedding_diffeomorph_precomp
      (Subtype.val ∘ (Subtype.val : K → U))
      (isSmoothEmbedding_fromOpen I J U (Subtype.val : K → U) hinduced) D
    simpa only [Function.comp_def, hval'] using h
  · change (Subtype.val : R → M) '' I.boundary R = frontier R
    rw [← I.compl_interior, image_compl_eq_range_sdiff_image Subtype.val_injective,
      Subtype.range_coe, hinterior', frontier, hclosed.closure_eq]

end DifferentialGeometry.Topology.Manifold
