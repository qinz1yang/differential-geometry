import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryFold

/-!
Pointwise orientation descent on the actual torus quotient. Inverse seam coordinates identify
both representatives, and the actual fold differential factors through those coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}} (P : TorusPairing C) (D : C.Components) {n : ℕ}
  (E : BoundaryTori C n)
  (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
    (P.surgerySideCollar j).target)
  (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
  (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
  {k : CarrierModel} [ChartedSpace k.Space P.QuotientSpace]
  (hpatch : ∀ i, ContMDiffOn (P.surgeryPatchModel n i) k.model ∞
      (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
    ContMDiffOn k.model (P.surgeryPatchModel n i) ∞
      (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target)

include D E he hb hpatch in
theorem surgeryQuotientFoldTangentEquiv_seam (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x =
      (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx).trans
        (carrierSurgeryPatchTangentEquiv
          (E := (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ)
          (F := EuclideanSpace ℝ (Fin 3)) (I := signedCollarModel) (J := k.model)
          (P.surgerySeamDiffeomorphism D E hd he hb hpatch j)
          ((P.surgerySignedSeam_source hd j).symm.subset
            (P.surgerySeamInverseCoordinates_mem j hx))) := by
  let d := P.surgerySeamDiffeomorphism D E hd he hb hpatch j
  have hm : P.surgerySeamInverseCoordinates j x ∈ d.source :=
    (P.surgerySignedSeam_source hd j).symm.subset (P.surgerySeamInverseCoordinates_mem j hx)
  have hcoord := (P.surgerySeamInverseCoordinates_contMDiffOn hd j).contMDiffAt
    (((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx)
  have heq : P.quotientMap =ᶠ[𝓝 x]
      (d : Torus × ℝ → P.QuotientSpace) ∘ P.surgerySeamInverseCoordinates j := by
    filter_upwards
      [((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx] with y hy
    exact ((P.surgerySignedSeam_apply hd j _ (P.surgerySeamInverseCoordinates_mem j hy)).trans
      (P.surgerySeamInverseCoordinates_fold j hy)).symm
  have hmf : mfderiv C.model k.model P.quotientMap x =
      mfderiv C.model k.model (d ∘ P.surgerySeamInverseCoordinates j) x := by
    ext v
    exact congrArg (fun A => A v) (heq.mfderiv_eq (I := C.model) (I' := k.model))
  ext v
  exact (congrArg (fun A => A v) hmf).trans
    (mfderiv_comp_apply x (d.mdifferentiableAt (by simp) hm)
      (hcoord.mdifferentiableAt (by simp)) v)

include D E hd he hb hpatch in
set_option backward.isDefEq.respectTransparency false in
theorem surgeryFoldOrientation_wellDefined
    (o : Fin P.count → ManifoldOrientation signedCollarModel surgerySignedDomain 3)
    (ho : ∀ (j : Fin P.count) (x : C.Carrier)
      (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target),
      Orientation.map (Fin 3) (P.surgerySeamInverseCoordinatesTangentEquiv hd j hx)
        (C.orientation.orientation x) =
        (o j).orientation ⟨P.surgerySeamInverseCoordinates j x,
          P.surgerySeamInverseCoordinates_mem j hx⟩)
    {x y : C.Carrier} (hxy : P.quotientMap x = P.quotientMap y) :
    Orientation.map (Fin 3) (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x)
      (C.orientation.orientation x) =
    Orientation.map (Fin 3) (P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch y)
      (C.orientation.orientation y) := by
  classical
  by_cases hx : ∃ j, x ∈ P.gluing.block j
  · obtain ⟨j, hj⟩ := hx
    have hxs : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
      rcases hj with hl | hr
      · rw [← P.leftCollar_zero_range] at hl
        obtain ⟨t, rfl⟩ := hl
        exact Or.inl ((P.leftCollar j).map_source (by
          rw [P.left_source]
          exact zero_mem_halfCollarSource t))
      · rw [← P.rightCollar_zero_range] at hr
        obtain ⟨t, rfl⟩ := hr
        exact Or.inr ((P.rightCollar j).map_source (by
          rw [P.right_source]
          exact zero_mem_halfCollarSource t))
    have hyq : P.quotientMap y ∈ range (P.surgerySeamMap j) := by
      rw [← hxy]
      exact (P.surgerySeamMap_preimage_range hd j).symm.subset hxs
    have hys := (P.surgerySeamMap_preimage_range hd j).subset hyq
    have hg : P.surgerySeamInverseCoordinates j x = P.surgerySeamInverseCoordinates j y := by
      rw [← P.surgerySignedSeam_symm_quotientMap hd j hxs,
        ← P.surgerySignedSeam_symm_quotientMap hd j hys, hxy]
    rw [P.surgeryQuotientFoldTangentEquiv_seam D E hd he hb hpatch j hxs,
      P.surgeryQuotientFoldTangentEquiv_seam D E hd he hb hpatch j hys,
      DifferentialGeometry.orientation_map_trans, DifferentialGeometry.orientation_map_trans,
      ho j x hxs, ho j y hys]
    have hsub : (⟨P.surgerySeamInverseCoordinates j x,
        P.surgerySeamInverseCoordinates_mem j hxs⟩ : surgerySignedDomain) =
        ⟨P.surgerySeamInverseCoordinates j y, P.surgerySeamInverseCoordinates_mem j hys⟩ :=
      Subtype.ext hg
    rw [hsub]
    let d := P.surgerySeamDiffeomorphism D E hd he hb hpatch j
    have hxg : P.surgerySeamInverseCoordinates j x ∈ d.source :=
      (P.surgerySignedSeam_source hd j).symm.subset
        (P.surgerySeamInverseCoordinates_mem j hxs)
    have hyg : P.surgerySeamInverseCoordinates j y ∈ d.source :=
      (P.surgerySignedSeam_source hd j).symm.subset
        (P.surgerySeamInverseCoordinates_mem j hys)
    exact congrArg (fun A => Orientation.map (Fin 3) A
      ((o j).orientation ⟨P.surgerySeamInverseCoordinates j y,
        P.surgerySeamInverseCoordinates_mem j hys⟩))
      (carrierSurgeryPatchTangentEquiv_congr d hxg hyg hg)
  · have heq : x = y := P.gluing.eq_of_rel_of_notMem
      (fun j hj => hx ⟨j, hj⟩) ((P.surgery_quotientMap_eq_iff x y).mp hxy)
    subst y
    rfl

end GC.GraphManifold.TorusPairing
