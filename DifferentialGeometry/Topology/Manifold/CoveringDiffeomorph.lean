import DifferentialGeometry.Topology.Manifold.CoveringAtlas
import Mathlib.Geometry.Manifold.Diffeomorph



noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E H M C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace C] {p : C → M} (hp : IsLocalHomeomorph p)
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]

def coveringProjectionDiffeomorph (U : TopologicalSpace.Opens C)
    (e : U ≃ₜ M) (he : ∀ x : U, e x = p x) :
    letI := coveringChartedSpace (H := H) hp
    Diffeomorph I I U M ∞ := by
  letI := coveringChartedSpace (H := H) hp
  letI := covering_isManifold hp I
  have hs : Function.RightInverse (fun x : M => (e.symm x : C)) p := fun x =>
    (he (e.symm x)).symm.trans (e.apply_symm_apply x)
  refine {
    toEquiv := e.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_
  }
  · have h : (e : U → M) = p ∘ Subtype.val := funext he
    change ContMDiff I I ∞ (e : U → M)
    rw [h]
    exact (covering_projection_contMDiff hp I).comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact covering_section_contMDiff hp I
      ⟨fun x => (e.symm x : C), continuous_subtype_val.comp e.symm.continuous⟩ hs


theorem coveringProjectionDiffeomorph_apply (U : TopologicalSpace.Opens C)
    (e : U ≃ₜ M) (he : ∀ x : U, e x = p x) (x : U) :
    coveringProjectionDiffeomorph hp I U e he x = p x := he x

end DifferentialGeometry.Topology.Manifold
