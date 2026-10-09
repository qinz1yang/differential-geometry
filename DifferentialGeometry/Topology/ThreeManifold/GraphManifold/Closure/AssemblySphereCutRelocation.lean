import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

/-!
# Chapter-14 assembly, L2-relative: the target region of the cap relocation

Lane ASM-L2, group G2 (first part). The V2 statement `exists_capRelocation_into_fibrePiece`
(`build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean:912–924`, review item 6, D9) moves a cap ball
into the set `capRelocationTarget R j b`: the image in `Q` of the cut-interior part of the
trivialization domain over `b` of the fibred piece `j` of a raw presentation `R`.

* `isOpen_capRelocationTarget`: the target is open in `Q` (the reconstruction restricted to the cut
  interior is the open embedding `R.interiorDiffeomorph`).
* `capRelocationTarget_nonempty`, `capRelocationTarget_inter_interior_nonempty`: the target is
  nonempty and meets the interior of `Q` (the projection of the piece is onto, and the manifold
  interiors are dense).

The remaining input of `exists_capRelocation_into_fibrePiece` is the classical relocation of a
smoothly embedded closed ball, by an ambient isotopy fixed near `∂Q`, into a given nonempty open
subset of the interior of a connected carrier (sheet `build-logs/resume/sheet-ASM-L2.md`, row 5).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The V2 target region of the cap relocation: the image in `Q` of the cut-interior part of the
trivialization domain over `b` of the fibred piece `j`. -/
def capRelocationTarget {Q : CompactCarrier.{u}} (R : RawGraphPresentation Q)
    (j : Fin R.components.count) (b : (R.fibration j).base.Carrier) : Set Q.Carrier :=
  (R.reconstruction ∘ R.pairing.quotientMap) ''
    ((Subtype.val '' (TopologicalSpace.Opens.comap (R.fibration j).projection
        ((R.fibration j).neighborhood b) : Set (R.components.piece j))) ∩
      (R.cutCarrier.interior : Set R.cutCarrier.Carrier))

/-- The trivialization domain over `b`, as a subset of the cut carrier, is open. -/
theorem isOpen_fibreDomain {Q : CompactCarrier.{u}} (R : RawGraphPresentation Q)
    (j : Fin R.components.count) (b : (R.fibration j).base.Carrier) :
    IsOpen (Subtype.val '' (TopologicalSpace.Opens.comap (R.fibration j).projection
        ((R.fibration j).neighborhood b) : Set (R.components.piece j))) :=
  (R.components.piece j).isOpen.isOpenMap_subtype_val _
    (TopologicalSpace.Opens.comap (R.fibration j).projection
      ((R.fibration j).neighborhood b)).isOpen

/-- On the cut interior, the reconstruction is the open embedding `interiorDiffeomorph`: the image
of an open subset of the cut interior is open in `Q`. -/
theorem isOpen_image_reconstruction_of_subset_interior {Q : CompactCarrier.{u}}
    (R : RawGraphPresentation Q) {O : Set R.cutCarrier.Carrier} (hO : IsOpen O)
    (hOI : O ⊆ R.cutCarrier.interior) :
    IsOpen ((R.reconstruction ∘ R.pairing.quotientMap) '' O) := by
  have heq : (R.reconstruction ∘ R.pairing.quotientMap) '' O =
      Subtype.val '' (R.interiorDiffeomorph '' (Subtype.val ⁻¹' O)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨R.interiorDiffeomorph ⟨x, hOI hx⟩, ⟨⟨x, hOI hx⟩, hx, rfl⟩, ?_⟩
      exact R.interior_map ⟨x, hOI hx⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.val, hx, (R.interior_map x).symm⟩
  rw [heq]
  exact R.interiorImage.isOpen.isOpenMap_subtype_val _
    (R.interiorDiffeomorph.toHomeomorph.isOpenMap _ (hO.preimage continuous_subtype_val))

/-- The cap relocation target is open in `Q`. -/
theorem isOpen_capRelocationTarget {Q : CompactCarrier.{u}} (R : RawGraphPresentation Q)
    (j : Fin R.components.count) (b : (R.fibration j).base.Carrier) :
    IsOpen (capRelocationTarget R j b) :=
  isOpen_image_reconstruction_of_subset_interior R
    ((isOpen_fibreDomain R j b).inter R.cutCarrier.interior.isOpen) inter_subset_right

/-- The cap relocation target is nonempty. -/
theorem capRelocationTarget_nonempty {Q : CompactCarrier.{u}} (R : RawGraphPresentation Q)
    (j : Fin R.components.count) (b : (R.fibration j).base.Carrier) :
    (capRelocationTarget R j b).Nonempty := by
  obtain ⟨x, hx⟩ := (R.fibration j).surjective b
  have hxA : x.val ∈ Subtype.val '' (TopologicalSpace.Opens.comap (R.fibration j).projection
      ((R.fibration j).neighborhood b) : Set (R.components.piece j)) := by
    refine ⟨x, ?_, rfl⟩
    change (R.fibration j).projection x ∈ (R.fibration j).neighborhood b
    rw [hx]
    exact (R.fibration j).mem_neighborhood b
  obtain ⟨y, hy⟩ := (ModelWithCorners.dense_interior R.cutCarrier.model).inter_open_nonempty _
    (isOpen_fibreDomain R j b) ⟨_, hxA⟩
  exact ⟨_, y, hy, rfl⟩

/-- The cap relocation target meets the interior of `Q`. -/
theorem capRelocationTarget_inter_interior_nonempty {Q : CompactCarrier.{u}}
    (R : RawGraphPresentation Q) (j : Fin R.components.count)
    (b : (R.fibration j).base.Carrier) :
    (capRelocationTarget R j b ∩ Q.interior).Nonempty :=
  (ModelWithCorners.dense_interior Q.model).inter_open_nonempty _
    (isOpen_capRelocationTarget R j b) (capRelocationTarget_nonempty R j b)

end GC.GraphManifold.Assembly
