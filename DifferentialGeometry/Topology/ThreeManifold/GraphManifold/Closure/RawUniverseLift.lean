import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CircleFibrationUniverseLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryGluingUniverseLift
import DifferentialGeometry.Topology.Manifold.Diffeomorph

/-!
# Universe lifts of raw presentation reconstructions

The actual lifted gluing and component fibrations reconstruct the same lifted ambient carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RawUniverseLift

def boundaryTori (C : CompactCarrier.{0}) {n : ℕ} (T : BoundaryTori C n) :
    BoundaryTori (carrier.{u} C) n where
  collar i := (T.collar i).trans (up.{u} C).toPartialDiffeomorph
  source_eq i := by
    change (T.collar i).source ∩ (T.collar i) ⁻¹' univ = halfCollarSource
    simpa only [preimage_univ, inter_univ] using T.source_eq i
  boundary_zero i t :=
    (((up.{u} C).isLocalDiffeomorph (T.collar i (t, halfZero))).isBoundaryPoint_iff
      (by simp)).mp (T.boundary_zero i t)
  disjoint i j hij := by
    change Disjoint (univ ∩ ULift.down ⁻¹' (T.collar i).target)
      (univ ∩ ULift.down ⁻¹' (T.collar j).target)
    simpa only [univ_inter] using (T.disjoint hij).preimage
      (ULift.down : ULift.{u} C.Carrier → C.Carrier)

theorem boundaryTori_image (C : CompactCarrier.{0}) {n : ℕ} (T : BoundaryTori C n) :
    (boundaryTori.{u} C T).image = ULift.down ⁻¹' T.image := by
  ext x
  simp only [BoundaryTori.image, mem_iUnion, mem_range, mem_preimage]
  constructor
  · rintro ⟨i, t, ht⟩
    exact ⟨i, t, congrArg ULift.down ht⟩
  · rintro ⟨i, t, ht⟩
    refine ⟨i, t, ?_⟩
    exact ULift.ext ht

theorem reverses_up (C : CompactCarrier.{0})
    (l r : Torus × EuclideanHalfSpace 1 → C.Carrier)
    (h : ReversesBoundaryOrientation C l r) :
    ReversesBoundaryOrientation (carrier.{u} C) (ULift.up ∘ l) (ULift.up ∘ r) := by
  intro t
  obtain ⟨L, R, hL, hR, ho⟩ := h t
  have hd (f : Torus × EuclideanHalfSpace 1 → C.Carrier) :
      mfderiv halfCollarModel C.model (ULift.up ∘ f) (t, halfZero) =
        mfderiv halfCollarModel C.model f (t, halfZero) := by
    change mfderiv halfCollarModel C.model ((up.{u} C) ∘ f) (t, halfZero) = _
    rw [(up.{u} C).mfderiv_comp (by simp)]
    change (mfderiv C.model C.model (ULift.up : C.Carrier → ULift.{u} C.Carrier)
      (f (t, halfZero))).comp (mfderiv halfCollarModel C.model f (t, halfZero)) = _
    rw [mfderiv_ulift_up]
    exact ContinuousLinearMap.id_comp _
  refine ⟨L, R, ?_, ?_, ?_⟩
  · intro v
    rw [hd l]
    exact hL v
  · intro v
    rw [hd r]
    exact hR v
  · change Orientation.map (Fin 3) L.symm
        (uliftTangentOrientation C.model C.Carrier C.orientation (ULift.up (l (t, halfZero)))) =
      -Orientation.map (Fin 3) R.symm
        (uliftTangentOrientation C.model C.Carrier C.orientation (ULift.up (r (t, halfZero))))
    rw [uliftTangentOrientation_apply, uliftTangentOrientation_apply]
    exact ho

def pairing (C : CompactCarrier.{0}) (P : TorusPairing C) : TorusPairing (carrier.{u} C) where
  count := P.count
  gluing := boundaryGluing P.gluing
  leftParam i := (P.leftParam i).trans (boundarySetDown (P.gluing.left i)).symm
  rightParam i := (P.rightParam i).trans (boundarySetDown (P.gluing.right i)).symm
  matching := P.matching
  matching_eq i t := by
    apply Subtype.ext
    exact congrArg ULift.up (congrArg Subtype.val (P.matching_eq i t))
  leftCollar i := (P.leftCollar i).trans (up.{u} C).toPartialDiffeomorph
  rightCollar i := (P.rightCollar i).trans (up.{u} C).toPartialDiffeomorph
  left_source i := by
    change (P.leftCollar i).source ∩ (P.leftCollar i) ⁻¹' univ = halfCollarSource
    simpa only [preimage_univ, inter_univ] using P.left_source i
  right_source i := by
    change (P.rightCollar i).source ∩ (P.rightCollar i) ⁻¹' univ = halfCollarSource
    simpa only [preimage_univ, inter_univ] using P.right_source i
  left_zero i t := congrArg ULift.up (P.left_zero i t)
  right_zero i t := congrArg ULift.up (P.right_zero i t)
  reversing i := reverses_up C (P.leftCollar i)
    (fun p => P.rightCollar i (P.matching i p.1, p.2)) (P.reversing i)

theorem boundary_lift (C : CompactCarrier.{0}) :
    (carrier.{u} C).model.boundary (carrier.{u} C).Carrier =
      ULift.down ⁻¹' C.model.boundary C.Carrier := by
  ext x
  exact (((up.{u} C).isLocalDiffeomorph x.down).isBoundaryPoint_iff (by simp)).symm

theorem derivative_down (C : CompactCarrier.{0}) (x : (carrier.{u} C).Carrier) :
    mfderiv C.model C.model (ULift.down : (carrier.{u} C).Carrier → C.Carrier) x =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
  obtain ⟨x⟩ := x
  have h := _root_.mfderiv_comp x
    ((up.{u} C).symm.mdifferentiable (by simp) (up.{u} C x))
    ((up.{u} C).mdifferentiable (by simp) x)
  change mfderiv C.model C.model (id : C.Carrier → C.Carrier) x =
    (mfderiv C.model C.model (ULift.down : (carrier.{u} C).Carrier → C.Carrier)
      (ULift.up x)).comp
        (mfderiv C.model C.model (ULift.up : C.Carrier → (carrier.{u} C).Carrier) x) at h
  rw [mfderiv_id, mfderiv_ulift_up] at h
  ext v
  exact (congrArg (fun A => A v) h).symm

def raw (W : CompactCarrier.{0}) (G : RawGraphPresentation W) :
    RawGraphPresentation (carrier.{u} W) where
  cutCarrier := carrier.{u} G.cutCarrier
  components := components.{u} G.cutCarrier G.components
  fibration i := fibration.{u} G.cutCarrier (G.components.piece i) (G.fibration i)
  pairing := pairing.{u} G.cutCarrier G.pairing
  externalCount := G.externalCount
  external := boundaryTori.{u} W G.external
  cutExternal := boundaryTori.{u} G.cutCarrier G.cutExternal
  external_exhausted := by rw [boundary_lift.{u}, G.external_exhausted, boundaryTori_image.{u}]
  cut_boundary_exhausted := by
    rw [boundary_lift.{u}, G.cut_boundary_exhausted, preimage_union, preimage_iUnion,
      boundaryTori_image]
    rfl
  external_disjoint := by
    rw [boundaryTori_image.{u}]
    change Disjoint (⋃ i, ULift.down ⁻¹' G.pairing.gluing.block i)
      (ULift.down ⁻¹' G.cutExternal.image)
    simpa only [preimage_iUnion] using G.external_disjoint.preimage
      (ULift.down : (carrier.{u} G.cutCarrier).Carrier → G.cutCarrier.Carrier)
  reconstruction := ((quotientDown.{u} G.pairing.gluing).trans G.reconstruction).trans
    (up.{u} W).toHomeomorph
  quotient_smooth := (up.{u} W).contMDiff.comp
    (G.quotient_smooth.comp (up.{u} G.cutCarrier).symm.contMDiff)
  quotient_oriented := by
    intro x
    obtain ⟨L, hL, ho⟩ := G.quotient_oriented x.down
    refine ⟨L, ?_, ?_⟩
    · intro v
      let f := G.reconstruction ∘ G.pairing.quotientMap
      have hd := _root_.mfderiv_comp x
        (G.quotient_smooth.mdifferentiable (by simp) x.down)
        ((up.{u} G.cutCarrier).symm.mdifferentiable (by simp) x)
      change mfderiv G.cutCarrier.model W.model
        (f ∘ ULift.down) x = (mfderiv G.cutCarrier.model W.model f x.down).comp
          (mfderiv G.cutCarrier.model G.cutCarrier.model
            (ULift.down : (carrier.{u} G.cutCarrier).Carrier → G.cutCarrier.Carrier) x) at hd
      rw [derivative_down] at hd
      have hd' : mfderiv G.cutCarrier.model W.model (f ∘ ULift.down) x =
          mfderiv G.cutCarrier.model W.model f x.down := by
        ext w
        exact congrArg (fun A => A w) hd
      change L v = mfderiv G.cutCarrier.model W.model
        ((up.{u} W) ∘ (f ∘ ULift.down)) x v
      rw [(up.{u} W).mfderiv_comp (by simp)]
      change L v = ((mfderiv W.model W.model
        (ULift.up : W.Carrier → (carrier.{u} W).Carrier) (f x.down)).comp
          (mfderiv G.cutCarrier.model W.model (f ∘ ULift.down) x)) v
      rw [mfderiv_ulift_up]
      change L v = mfderiv G.cutCarrier.model W.model (f ∘ ULift.down) x v
      rw [hd']
      exact hL v
    · change Orientation.map (Fin 3) L
        (uliftTangentOrientation G.cutCarrier.model G.cutCarrier.Carrier
          G.cutCarrier.orientation (ULift.up x.down)) =
        uliftTangentOrientation W.model W.Carrier W.orientation
          (ULift.up (G.reconstruction (G.pairing.quotientMap x.down)))
      rw [uliftTangentOrientation_apply, uliftTangentOrientation_apply]
      exact ho
  interiorImage := openLift.{u} W G.interiorImage
  interiorDiffeomorph := ((interiorDown.{u} G.cutCarrier).trans G.interiorDiffeomorph).trans
    (openDown.{u} W G.interiorImage).symm
  interior_map x := congrArg ULift.up (G.interior_map (interiorDown.{u} G.cutCarrier x))
  seam i := (G.seam i).trans (up.{u} W).toPartialDiffeomorph
  seam_source i := by
    change (G.seam i).source ∩ (G.seam i) ⁻¹' univ = signedCollarSource
    simpa only [preimage_univ, inter_univ] using G.seam_source i
  seam_zero i t := congrArg ULift.up (G.seam_zero i t)
  seam_positive i t s hs h := congrArg ULift.up (G.seam_positive i t s hs h)
  seam_negative i t s hs h := congrArg ULift.up (G.seam_negative i t s hs h)
  seam_interior i x hx :=
    (interior_up.{u} (C := W) (x := x.down)).mpr (G.seam_interior i hx.2)
  seam_disjoint i j hij := by
    change Disjoint (univ ∩ ULift.down ⁻¹' (G.seam i).target)
      (univ ∩ ULift.down ⁻¹' (G.seam j).target)
    simpa only [univ_inter] using (G.seam_disjoint hij).preimage
      (ULift.down : (carrier.{u} W).Carrier → W.Carrier)
  marked_collar i p hp := congrArg ULift.up (G.marked_collar i p hp)
  external_seam_disjoint i j := by
    change Disjoint (univ ∩ ULift.down ⁻¹' (G.external.collar i).target)
      (univ ∩ ULift.down ⁻¹' (G.seam j).target)
    simpa only [univ_inter] using (G.external_seam_disjoint i j).preimage
      (ULift.down : (carrier.{u} W).Carrier → W.Carrier)
  leftPiece := G.leftPiece
  rightPiece := G.rightPiece
  left_owned i x hx := G.left_owned i hx
  right_owned i x hx := G.right_owned i hx
  externalPiece := G.externalPiece
  external_owned i x hx := by
    obtain ⟨t, ht⟩ := hx
    exact G.external_owned i ⟨t, congrArg ULift.down ht⟩

theorem nonempty_rawGraphPresentation_ulift
    (M : ConnectedClosedOrientedManifold.{0} 3)
    (G : RawGraphPresentation (NoCuts.carrier M)) :
    Nonempty (RawGraphPresentation (NoCuts.carrier M.ulift.{0, u})) :=
  ⟨raw.{u} (NoCuts.carrier M) G⟩

end GC.GraphManifold.RawUniverseLift
