import DifferentialGeometry.Topology.ThreeManifold.CoreBandGluing
import DifferentialGeometry.Topology.Attachment.Reparametrization
import DifferentialGeometry.Bundle.Orientation.Map

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Band" => S2 × Icc (-1 : ℝ) 1

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

def coreImageHomeomorph : T.core ≃ₜ range C.coreInclusion := by
  let _ := C.coreCharts
  exact C.core_embedding.isEmbedding.toHomeomorph

@[simp] theorem coreImageHomeomorph_apply (x : T.core) :
    (C.coreImageHomeomorph x).val = C.coreInclusion x := rfl

def capBandBoundaryEquiv (S : Finset T.Index) : (Σ _a : S, Bool × S2) ≃ (Σ _a : S, Bool × S2) where
  toFun q := ⟨q.1, q.2.1, C.attaching (q.1.val, q.2.1) q.2.2⟩
  invFun q := ⟨q.1, q.2.1, (C.attaching (q.1.val, q.2.1)).symm q.2.2⟩
  left_inv := by rintro ⟨a, b, z⟩; simp
  right_inv := by rintro ⟨a, b, z⟩; simp

def cappedCoreBandBoundaryInclusion (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → (Σ _a : S, Band) :=
  T.coreBandBoundaryInclusion S ∘ C.capBandBoundaryEquiv S

def cappedCoreBandAttachingMap (S : Finset T.Index) :
    (Σ _a : S, Bool × S2) → range C.coreInclusion :=
  C.coreImageHomeomorph ∘ T.coreBandAttachingMap S ∘ C.capBandBoundaryEquiv S

theorem cappedCoreBandAttachingMap_val (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    (C.cappedCoreBandAttachingMap S q).val =
      C.cap (q.1.val, q.2.1) (sphereToClosedCell q.2.2) :=
  (C.boundary_eq (q.1.val, q.2.1) q.2.2).symm

abbrev CappedCoreBandGluing (S : Finset T.Index) :=
  AdjunctionSpace (C.cappedCoreBandBoundaryInclusion S) (C.cappedCoreBandAttachingMap S)

def cappedCoreBandHomeomorph (S : Finset T.Index) :
    C.CappedCoreBandGluing S ≃ₜ (T.core ∪ ⋃ a ∈ S, T.band a : Set M.Carrier) :=
  ((adjunctionHomeoOfLowerEquiv (C.cappedCoreBandBoundaryInclusion S)
    (T.coreBandAttachingMap S ∘ C.capBandBoundaryEquiv S) C.coreImageHomeomorph).trans
      (adjunctionHomeomorphOfBoundaryEquiv (T.coreBandBoundaryInclusion S)
        (T.coreBandAttachingMap S) (C.capBandBoundaryEquiv S))).trans
    (T.coreBandHomeomorph S)

@[simp] theorem cappedCoreBandHomeomorph_core (S : Finset T.Index) (x : T.core) :
    (C.cappedCoreBandHomeomorph S
      (adjunctionLower (i := C.cappedCoreBandBoundaryInclusion S)
        (C.cappedCoreBandAttachingMap S) (C.coreImageHomeomorph x))).val = x.val := by
  change (T.coreBandHomeomorph S
    (adjunctionLower (i := T.coreBandBoundaryInclusion S) (T.coreBandAttachingMap S)
      (C.coreImageHomeomorph.symm (C.coreImageHomeomorph x)))).val = x.val
  rw [C.coreImageHomeomorph.symm_apply_apply, T.coreBandHomeomorph_core]

@[simp] theorem cappedCoreBandHomeomorph_band (S : Finset T.Index) (q : Σ _a : S, Band) :
    (C.cappedCoreBandHomeomorph S
      (adjunctionCell (C.cappedCoreBandBoundaryInclusion S) (C.cappedCoreBandAttachingMap S) q)).val =
      T.coreBandMap S q := rfl

theorem cappedCoreBandGluing_seam (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    adjunctionCell (C.cappedCoreBandBoundaryInclusion S) (C.cappedCoreBandAttachingMap S)
      (C.cappedCoreBandBoundaryInclusion S q) =
    adjunctionLower (i := C.cappedCoreBandBoundaryInclusion S)
      (C.cappedCoreBandAttachingMap S) (C.cappedCoreBandAttachingMap S q) :=
  adjunction_coherence _ _ q

theorem cappedCoreBandHomeomorph_boundary (S : Finset T.Index) (q : Σ _a : S, Bool × S2) :
    (C.cappedCoreBandHomeomorph S
      (adjunctionLower (i := C.cappedCoreBandBoundaryInclusion S)
        (C.cappedCoreBandAttachingMap S) (C.cappedCoreBandAttachingMap S q))).val =
      T.boundarySphere (q.1.val, q.2.1) (C.attaching (q.1.val, q.2.1) q.2.2) := by
  change (C.cappedCoreBandHomeomorph S
    (adjunctionLower (i := C.cappedCoreBandBoundaryInclusion S)
      (C.cappedCoreBandAttachingMap S)
      (C.coreImageHomeomorph (T.coreBoundarySphere (q.1.val, q.2.1)
        (C.attaching (q.1.val, q.2.1) q.2.2))))).val = _
  rw [C.cappedCoreBandHomeomorph_core]
  rfl

theorem cappedCoreBandGluing_seam_insert [DecidableEq T.Index] (S : Finset T.Index)
    (e a : T.Index) (ha : a ∈ S) (b : Bool) (z : S2) :
    adjunctionCell (C.cappedCoreBandBoundaryInclusion (insert e S))
        (C.cappedCoreBandAttachingMap (insert e S))
        (C.cappedCoreBandBoundaryInclusion (insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩) =
      adjunctionLower (i := C.cappedCoreBandBoundaryInclusion (insert e S))
        (C.cappedCoreBandAttachingMap (insert e S))
        (C.cappedCoreBandAttachingMap (insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩) :=
  C.cappedCoreBandGluing_seam (insert e S) ⟨⟨a, Finset.mem_insert_of_mem ha⟩, b, z⟩

def cappedCoreBandHomeomorphSource : C.CappedCoreBandGluing Finset.univ ≃ₜ M.Carrier :=
  ((adjunctionHomeoOfLowerEquiv (C.cappedCoreBandBoundaryInclusion Finset.univ)
    (T.coreBandAttachingMap Finset.univ ∘ C.capBandBoundaryEquiv Finset.univ) C.coreImageHomeomorph).trans
      (adjunctionHomeomorphOfBoundaryEquiv (T.coreBandBoundaryInclusion Finset.univ)
        (T.coreBandAttachingMap Finset.univ) (C.capBandBoundaryEquiv Finset.univ))).trans
    T.coreBandHomeomorphSource

@[simp] theorem cappedCoreBandHomeomorphSource_core (x : T.core) :
    C.cappedCoreBandHomeomorphSource
      (adjunctionLower (i := C.cappedCoreBandBoundaryInclusion Finset.univ)
        (C.cappedCoreBandAttachingMap Finset.univ) (C.coreImageHomeomorph x)) = x.val := by
  change T.coreBandHomeomorphSource
    (adjunctionLower (i := T.coreBandBoundaryInclusion Finset.univ) (T.coreBandAttachingMap Finset.univ)
      (C.coreImageHomeomorph.symm (C.coreImageHomeomorph x))) = x.val
  rw [C.coreImageHomeomorph.symm_apply_apply, T.coreBandHomeomorphSource_core]

@[simp] theorem cappedCoreBandHomeomorphSource_band
    (q : Σ _a : (Finset.univ : Finset T.Index), Band) :
    C.cappedCoreBandHomeomorphSource
      (adjunctionCell (C.cappedCoreBandBoundaryInclusion Finset.univ)
        (C.cappedCoreBandAttachingMap Finset.univ) q) = T.coreBandMap Finset.univ q := rfl

theorem coreInclusion_inverse_orientation (x : T.core) :
    letI := C.coreCharts
    (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier) x),
    ∃ hj : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) C.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) C.coreInclusion x).toLinearMap hj).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
            (Subtype.val : T.core → M.Carrier) x).toLinearMap hi))
        (N.orientation.orientation (C.coreInclusion x)) = M.orientation.orientation x.val := by
  let _ := C.coreCharts
  intro hx
  obtain ⟨hi, hj, h⟩ := C.core_positive x hx
  let A := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
    (Subtype.val : T.core → M.Carrier) x).toLinearMap hi
  let B := LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) C.coreInclusion x).toLinearMap hj
  refine ⟨hi, hj, ?_⟩
  change Orientation.map (Fin 3) (B.symm.trans A) (N.orientation.orientation (C.coreInclusion x)) = _
  rw [← h, DifferentialGeometry.VectorBundle.map_orientation_trans_between]
  have heq : (A.symm.trans B).trans (B.symm.trans A) = LinearEquiv.refl ℝ _ := by ext v; simp
  rw [heq, Orientation.map_refl]
  rfl

end DifferentialGeometry.Topology.SphericalCapping
