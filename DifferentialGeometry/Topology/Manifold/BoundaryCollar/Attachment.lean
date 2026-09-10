import DifferentialGeometry.Topology.Attachment.MappingCylinder
import DifferentialGeometry.Geometry.Boundary.Metric.Induced

open Set Function Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H)

abbrev BoundaryAttachment := DifferentialGeometry.Topology.MappingCylinder
  (⟨boundaryInclusion I M, continuous_subtype_val⟩ : C(BoundaryManifold I M, M))


def attachmentOriginal : C(M, BoundaryAttachment (M := M) I) :=
  DifferentialGeometry.Topology.mappingCylinderOriginal _


def attachmentProduct : C(BoundaryManifold I M × Icc (0 : ℝ) 1, BoundaryAttachment (M := M) I) :=
  DifferentialGeometry.Topology.mappingCylinderProduct _


theorem attachment_seam (p : BoundaryManifold I M) :
    attachmentProduct I (p, 0) = attachmentOriginal I (boundaryInclusion I M p) :=
  DifferentialGeometry.Topology.mappingCylinder_seam _ p


theorem attachment_product_eq_original_iff (p : BoundaryManifold I M × Icc (0 : ℝ) 1)
    (x : M) : attachmentProduct I p = attachmentOriginal I x ↔
      p.2 = 0 ∧ boundaryInclusion I M p.1 = x :=
  DifferentialGeometry.Topology.mappingCylinder_product_eq_original_iff _ p x

theorem isClosedEmbedding_attachmentOriginal :
    IsClosedEmbedding (attachmentOriginal (M := M) I) :=
  DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderOriginal _

theorem isClosedEmbedding_attachmentProduct [IsManifold I 1 M] :
    IsClosedEmbedding (attachmentProduct (M := M) I) := by
  apply DifferentialGeometry.Topology.isClosedEmbedding_mappingCylinderProduct
  exact (I.isClosed_boundary (M := M) (n := 1) (by norm_num)).isClosedEmbedding_subtypeVal


theorem attachment_original_union_product :
    range (attachmentOriginal (M := M) I) ∪ range (attachmentProduct (M := M) I) = univ := by
  apply eq_univ_of_forall
  intro z
  refine Quot.inductionOn z ?_
  intro q
  cases q with
  | inl p => exact Or.inr ⟨p, rfl⟩
  | inr x => exact Or.inl ⟨x, rfl⟩

theorem attachment_outer_ne_original (p : BoundaryManifold I M) (x : M) :
    attachmentProduct I (p, 1) ≠ attachmentOriginal I x := by
  intro h
  have ht := ((attachment_product_eq_original_iff I (p, 1) x).mp h).1
  have ht' := congrArg (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ht
  norm_num at ht'

end DifferentialGeometry.Manifold.BoundaryCollar
