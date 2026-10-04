import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryDifferential
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryTangent

/-!
The differential of the actual torus quotient fold is bijective at every original carrier point,
including both identified boundary tori. The induced tangent equivalence is the actual derivative.
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

include D E hd he hb hpatch in
theorem surgeryQuotientFold_mfderiv_injective (x : C.Carrier) :
    Function.Injective (mfderiv C.model k.model P.quotientMap x) := by
  rcases P.surgeryPatches_cover D E hd he hb (P.quotientMap x) with hi | hs | hext
  · have hx : x ∈ C.interior := (P.surgeryInteriorPatch_preimage_target D
      (P.surgeryCoreBoundarySubset E hb)).subset hi
    let d := P.surgeryInteriorDiffeomorphism (k := k) D E hd he hb hpatch
    have hm : x ∈ d.source := (P.surgeryInteriorPatch_source D
      (P.surgeryCoreBoundarySubset E hb)).symm.subset hx
    have heq : P.quotientMap =ᶠ[𝓝 x] (d : C.Carrier → P.QuotientSpace) := by
      filter_upwards [C.interior.isOpen.mem_nhds hx] with y hy
      exact (P.surgeryInteriorPatch_apply D (P.surgeryCoreBoundarySubset E hb) hy).symm
    have hmf : mfderiv C.model k.model P.quotientMap x =
        mfderiv C.model k.model d x := by
      ext v
      exact congrArg (fun A => A v) (heq.mfderiv_eq (I := C.model) (I' := k.model))
    rw [hmf]
    exact (carrierSurgeryPatchTangentEquiv d hm).injective
  · obtain ⟨j, hj⟩ := hs
    have hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target := by
      rw [P.surgerySignedSeam_target] at hj
      exact (P.surgerySeamMap_preimage_range hd j).subset hj
    let d := P.surgerySeamDiffeomorphism (k := k) D E hd he hb hpatch j
    have hm : P.surgerySeamInverseCoordinates j x ∈ d.source :=
      (P.surgerySignedSeam_source hd j).symm.subset (P.surgerySeamInverseCoordinates_mem j hx)
    have hcoord := (P.surgerySeamInverseCoordinates_contMDiffOn hd j).contMDiffAt
      (((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx)
    have heq : P.quotientMap =ᶠ[𝓝 x]
        (d : Torus × ℝ → P.QuotientSpace) ∘ P.surgerySeamInverseCoordinates j := by
      filter_upwards
        [((P.leftCollar j).open_target.union (P.rightCollar j).open_target).mem_nhds hx]
        with y hy
      exact ((P.surgerySignedSeam_apply hd j _ (P.surgerySeamInverseCoordinates_mem j hy)).trans
        (P.surgerySeamInverseCoordinates_fold j hy)).symm
    have hmf : mfderiv C.model k.model P.quotientMap x =
        mfderiv C.model k.model (d ∘ P.surgerySeamInverseCoordinates j) x := by
      ext v
      exact congrArg (fun A => A v) (heq.mfderiv_eq (I := C.model) (I' := k.model))
    rw [hmf, mfderiv_comp x (d.mdifferentiableAt (by simp) hm)
      (hcoord.mdifferentiableAt (by simp))]
    exact (carrierSurgeryPatchTangentEquiv d hm).injective.comp
      (P.surgerySeamInverseCoordinates_mfderiv_injective hd j hx)
  · obtain ⟨j, hj⟩ := hext
    have hx : x ∈ (E.collar j).target :=
      (P.surgeryExternalCollar_preimage_target E he j).subset hj
    let d := P.surgeryExternalDiffeomorphism (k := k) D E hd he hb hpatch j
    have hm : (E.collar j).symm x ∈ d.source := by
      rw [show d.source = halfCollarSource from P.surgeryExternalCollar_source E he j]
      exact (E.source_eq j).subset ((E.collar j).map_target hx)
    have heq : P.quotientMap =ᶠ[𝓝 x]
        (d : Torus × EuclideanHalfSpace 1 → P.QuotientSpace) ∘ (E.collar j).symm := by
      filter_upwards [(E.collar j).open_target.mem_nhds hx] with y hy
      have hs : (E.collar j).symm y ∈ halfCollarSource :=
        (E.source_eq j).subset ((E.collar j).map_target hy)
      change P.quotientMap y = P.surgeryExternalCollar E he j ((E.collar j).symm y)
      rw [P.surgeryExternalCollar_apply E he j hs]
      exact congrArg P.quotientMap ((E.collar j).right_inv' hy).symm
    have hmf : mfderiv C.model k.model P.quotientMap x =
        mfderiv C.model k.model (d ∘ (E.collar j).symm) x := by
      ext v
      exact congrArg (fun A => A v) (heq.mfderiv_eq (I := C.model) (I' := k.model))
    rw [hmf, mfderiv_comp x (d.mdifferentiableAt (by simp) hm)
      ((E.collar j).symm.mdifferentiableAt (by simp) hx)]
    exact (carrierSurgeryPatchTangentEquiv d hm).injective.comp
      (carrierSurgeryPatchTangentEquiv (E.collar j).symm hx).injective

include D E hd he hb hpatch in
theorem surgeryQuotientFold_mfderiv_bijective (x : C.Carrier) :
    Function.Bijective (mfderiv C.model k.model P.quotientMap x) := by
  have hinj := P.surgeryQuotientFold_mfderiv_injective D E hd he hb hpatch x
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

def surgeryQuotientFoldTangentEquiv (x : C.Carrier) :
    TangentSpace C.model x ≃ₗ[ℝ] TangentSpace k.model (P.quotientMap x) :=
  LinearEquiv.ofBijective (mfderiv C.model k.model P.quotientMap x).toLinearMap
    (P.surgeryQuotientFold_mfderiv_bijective D E hd he hb hpatch x)

theorem surgeryQuotientFoldTangentEquiv_apply (x : C.Carrier) (v : TangentSpace C.model x) :
    P.surgeryQuotientFoldTangentEquiv D E hd he hb hpatch x v =
      mfderiv C.model k.model P.quotientMap x v := rfl

end GC.GraphManifold.TorusPairing
