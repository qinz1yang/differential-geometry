import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold Set
open scoped Manifold ContDiff
namespace GC.GraphManifold
universe u

def BoundaryTori.transport {W W' : CompactCarrier.{u}} {n : ℕ}
    (T : BoundaryTori W n) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) : BoundaryTori W' n where
  collar i := (T.collar i).trans e.toPartialDiffeomorph
  source_eq i := by
    change (T.collar i).source ∩ (T.collar i) ⁻¹' univ = halfCollarSource
    simpa using T.source_eq i
  boundary_zero i x := (e.isLocalDiffeomorph _).isBoundaryPoint_iff (by simp) |>.mp (T.boundary_zero i x)
  disjoint := by
    intro i j hij
    have ht (k : Fin n) : ((T.collar k).trans e.toPartialDiffeomorph).target = e.symm ⁻¹' (T.collar k).target := by
      ext x
      change (x ∈ (univ : Set W'.Carrier) ∧ e.symm x ∈ (T.collar k).target) ↔ e.symm x ∈ (T.collar k).target
      simp only [mem_univ, true_and]
    rw [ht, ht]
    exact (T.disjoint hij).preimage _

private def openImageDiffeomorph {W W' : CompactCarrier.{u}}
    (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier) (U : TopologicalSpace.Opens W.Carrier) :
    U ≃ₘ⟮W.model, W'.model⟯ (⟨e '' U, e.toHomeomorph.isOpenMap _ U.isOpen⟩ : TopologicalSpace.Opens W'.Carrier) where
  toFun x := ⟨e x, mem_image_of_mem e x.property⟩
  invFun y := ⟨e.symm y, by obtain ⟨x, hx, he⟩ := y.property; rw [← he, e.symm_apply_apply]; exact hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff _ _).mp (e.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff _ _).mp (e.symm.contMDiff.comp contMDiff_subtype_val)

def RawGraphPresentation.transport {W W' : CompactCarrier.{u}}
    (G : RawGraphPresentation W) (e : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (he : e.preservesOrientation W.orientation W'.orientation) : RawGraphPresentation W' where
  cutCarrier := G.cutCarrier
  components := G.components
  fibration := G.fibration
  pairing := G.pairing
  externalCount := G.externalCount
  external := G.external.transport e
  cutExternal := G.cutExternal
  external_exhausted := by
    rw [← e.image_boundary (by simp), G.external_exhausted]
    ext x
    simp only [BoundaryTori.image, mem_image, mem_iUnion, mem_range]
    constructor
    · rintro ⟨_, ⟨i, y, rfl⟩, rfl⟩
      exact ⟨i, y, rfl⟩
    · rintro ⟨i, y, rfl⟩
      exact ⟨G.external.torusMap i y, ⟨i, y, rfl⟩, rfl⟩
  cut_boundary_exhausted := G.cut_boundary_exhausted
  external_disjoint := G.external_disjoint
  reconstruction := G.reconstruction.trans e.toHomeomorph
  quotient_smooth := e.contMDiff.comp G.quotient_smooth
  quotient_oriented := by
    intro x
    obtain ⟨L, hL, ho⟩ := G.quotient_oriented x
    let R := (e.mfderivToContinuousLinearEquiv (by simp) (G.reconstruction (G.pairing.quotientMap x))).toLinearEquiv
    refine ⟨L.trans R, ?_, ?_⟩
    · intro v
      change R (L v) = mfderiv G.cutCarrier.model W'.model (e ∘ (G.reconstruction ∘ G.pairing.quotientMap)) x v
      rw [mfderiv_comp (I' := W.model) x (e.mdifferentiable (by simp) _) (G.quotient_smooth.mdifferentiable (by simp) x)]
      rw [hL]
      rfl
    · have hmap : Orientation.map (Fin 3) (L.trans R) (G.cutCarrier.orientation.orientation x) =
          Orientation.map (Fin 3) R (Orientation.map (Fin 3) L (G.cutCarrier.orientation.orientation x)) := by
        generalize G.cutCarrier.orientation.orientation x = o
        induction o using Module.Ray.ind with
        | h v hv => rfl
      exact hmap.trans ((congrArg (fun o => Orientation.map (Fin 3) R o) ho).trans (he _))
  interiorImage := ⟨e '' G.interiorImage, e.toHomeomorph.isOpenMap _ G.interiorImage.isOpen⟩
  interiorDiffeomorph := G.interiorDiffeomorph.trans (openImageDiffeomorph e G.interiorImage)
  interior_map x := congrArg e (G.interior_map x)
  seam i := (G.seam i).trans e.toPartialDiffeomorph
  seam_source i := by
    change (G.seam i).source ∩ (G.seam i) ⁻¹' univ = signedCollarSource
    simpa using G.seam_source i
  seam_zero i t := congrArg e (G.seam_zero i t)
  seam_positive i t s hs h := congrArg e (G.seam_positive i t s hs h)
  seam_negative i t s hs h := congrArg e (G.seam_negative i t s hs h)
  seam_interior := by
    intro i x hx
    have hi : e.symm x ∈ (G.seam i).target := hx.2
    have := (e.isLocalDiffeomorph (e.symm x)).isInteriorPoint_iff (by simp) |>.mp (G.seam_interior i hi)
    change W'.model.IsInteriorPoint x
    simpa only [e.apply_symm_apply] using this
  seam_disjoint := by
    intro i j hij
    have ht (k : Fin G.pairing.count) : ((G.seam k).trans e.toPartialDiffeomorph).target = e.symm ⁻¹' (G.seam k).target := by
      ext x
      change (x ∈ (univ : Set W'.Carrier) ∧ e.symm x ∈ (G.seam k).target) ↔ e.symm x ∈ (G.seam k).target
      simp only [mem_univ, true_and]
    rw [ht, ht]
    exact (G.seam_disjoint hij).preimage _
  marked_collar i p hp := congrArg e (G.marked_collar i p hp)
  external_seam_disjoint := by
    intro i j
    change Disjoint ((G.external.collar i).trans e.toPartialDiffeomorph).target ((G.seam j).trans e.toPartialDiffeomorph).target
    change Disjoint (univ ∩ e.symm ⁻¹' (G.external.collar i).target) (univ ∩ e.symm ⁻¹' (G.seam j).target)
    simpa only [univ_inter] using (G.external_seam_disjoint i j).preimage (fun x => e.symm x)
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned := G.left_owned
  right_owned := G.right_owned
  externalPiece := G.externalPiece
  external_owned := G.external_owned

end GC.GraphManifold
