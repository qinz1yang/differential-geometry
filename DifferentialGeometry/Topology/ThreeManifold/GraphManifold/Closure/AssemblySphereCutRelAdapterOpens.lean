import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.OpenTarget
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Chapter-14 assembly, relative COMPARE side adapters (b): reading an open subset in the manifold

Lane ASM-L2f, group G1. The side adapters work in a component of the capped carrier (an open
subset `U` of `M`) and read every output in `M` through the inclusion.

* `pushOpens`: a partial diffeomorphism into `U`, read in `M` (`_apply`, `_source`, `_target`,
  `_image`, `_target_subset`, `_target_subset_interior`).
* `mem_interior_val_iff`, `image_val_boundary`: interior and boundary of an open subset.
* `isSmoothEmbedding_val_comp`, `bijective_mfderiv_val_comp`, `range_val_comp`,
  `image_val_comp_boundary`: an embedding into `U`, read in `M`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

section Push

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' X : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X] [ChartedSpace H' X]
  (U : TopologicalSpace.Opens M) (hU : Nonempty U)

/-- A partial diffeomorphism into an open subset `U`, read in the manifold. -/
def pushOpens (φ : PartialDiffeomorph J I X U ∞) : PartialDiffeomorph J I X M ∞ :=
  φ.trans (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU)

variable (φ : PartialDiffeomorph J I X U ∞)

theorem pushOpens_apply (x : X) : pushOpens U hU φ x = (φ x).val := rfl

theorem pushOpens_source : (pushOpens U hU φ).source = φ.source := by
  change φ.source ∩ φ ⁻¹' (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U
    hU).source = φ.source
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source, preimage_univ,
    inter_univ]

theorem pushOpens_target : (pushOpens U hU φ).target = Subtype.val '' φ.target := by
  ext y
  change y ∈ (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU).target ∩
    (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U hU).symm ⁻¹' φ.target ↔ _
  rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
  constructor
  · rintro ⟨hy, hyt⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rwa [mem_preimage, DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
      I U hU hy] at hyt
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    rw [mem_preimage, DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
      I U hU x.property]
    exact hx

theorem pushOpens_image (S : Set X) : pushOpens U hU φ '' S = Subtype.val '' (φ '' S) := by
  rw [image_image]
  rfl

theorem pushOpens_target_subset : (pushOpens U hU φ).target ⊆ U := by
  rw [pushOpens_target]
  rintro _ ⟨x, -, rfl⟩
  exact x.property

/-- A point of an open subset is interior in the subset iff it is interior in the manifold. -/
theorem mem_interior_val_iff {V : TopologicalSpace.Opens M} {x : V} :
    x.val ∈ I.interior M ↔ x ∈ I.interior V :=
  I.isInteriorPoint_iff_isInteriorPoint_val.symm

theorem pushOpens_target_subset_interior (hφ : φ.target ⊆ I.interior U) :
    (pushOpens U hU φ).target ⊆ I.interior M := by
  rw [pushOpens_target]
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_interior_val_iff (x := x)).mpr (hφ hx)

/-- The boundary of an open subset, read in the manifold. -/
theorem image_val_boundary : Subtype.val '' I.boundary U = I.boundary M ∩ (U : Set M) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨I.isBoundaryPoint_iff_isBoundaryPoint_val.mp hx, x.property⟩
  · rintro ⟨hy, hyU⟩
    exact ⟨⟨y, hyU⟩, I.isBoundaryPoint_iff_isBoundaryPoint_val.mpr hy, rfl⟩

end Push

section Embedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' L : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace L] [ChartedSpace H' L]
  (U : TopologicalSpace.Opens M) (η : L → U)

theorem isSmoothEmbedding_val_comp [IsManifold I ∞ M] (hη : IsSmoothEmbedding J I ∞ η) :
    IsSmoothEmbedding J I ∞ (Subtype.val ∘ η) :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen J I U η hη

theorem bijective_mfderiv_val_comp (x : L) (hη : Bijective (mfderiv J I η x)) :
    Bijective (mfderiv J I (Subtype.val ∘ η) x) := by
  rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp U η x]
  exact hη

omit [TopologicalSpace L] in
theorem range_val_comp (S : Set U) (hη : range η = Sᶜ) :
    range (Subtype.val ∘ η) = (U : Set M) \ Subtype.val '' S := by
  rw [range_comp, hη]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.property, ?_⟩
    rintro ⟨x', hx', he⟩
    exact hx (Subtype.ext he ▸ hx')
  · rintro ⟨hyU, hy⟩
    exact ⟨⟨y, hyU⟩, fun h => hy ⟨_, h, rfl⟩, rfl⟩

theorem image_val_comp_boundary {T : Set U}
    (hη : η '' J.boundary L = I.boundary U ∪ T) :
    (Subtype.val ∘ η) '' J.boundary L = (I.boundary M ∩ (U : Set M)) ∪ Subtype.val '' T := by
  rw [image_comp, hη, image_union, image_val_boundary]

end Embedding

end GC.GraphManifold.Assembly
