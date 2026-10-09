import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySmoothPatches
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryOrientation

/-!
The actual inverse signed seam coordinates have invertible differentials on both original sides,
including the identified zero tori. Their tangent equivalence is the actual manifold derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

private theorem surgeryRightCoordinates_injective (P : TorusPairing C) (j : Fin P.count)
    (p : Torus × EuclideanHalfSpace 1) :
    Function.Injective (mfderiv halfCollarModel signedCollarModel
      (fun z : Torus × EuclideanHalfSpace 1 => ((P.matching j).symm z.1, z.2.val 0)) p) := by
  let T : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  have ht := hasMFDerivAt_halfSpaceOneCoordinate p.2
  change Function.Injective (mfderiv halfCollarModel signedCollarModel
    (Prod.map (P.matching j).symm (fun h : EuclideanHalfSpace 1 => h.val 0)) p)
  rw [mfderiv_prodMap ((P.matching j).symm.contMDiff.mdifferentiableAt (by simp))
    ht.mdifferentiableAt, ht.mfderiv]
  let hm := ((P.matching j).symm.toPartialDiffeomorph.isLocalDiffeomorphAt
    torusModel torusModel ∞ (mem_univ p.1)).mfderivToContinuousLinearEquiv
    (by simp)
  intro v w hvw
  apply Prod.ext
  · apply hm.injective
    change mfderiv torusModel torusModel
      ((P.matching j).symm : Torus → Torus) p.1 v.1 =
      mfderiv torusModel torusModel ((P.matching j).symm : Torus → Torus) p.1 w.1
    exact congrArg Prod.fst hvw
  · apply T.injective
    exact congrArg Prod.snd hvw

theorem surgerySeamInverseCoordinates_mfderiv_injective (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    Function.Injective (mfderiv C.model signedCollarModel
      (P.surgerySeamInverseCoordinates j) x) := by
  classical
  rcases hx with hx | hx
  · have he : P.surgerySeamInverseCoordinates j =ᶠ[𝓝 x]
        (fun y => (((P.leftCollar j).symm y).1, -((P.leftCollar j).symm y).2.val 0)) := by
      filter_upwards [(P.leftCollar j).open_target.mem_nhds hx] with y hy
      simp only [surgerySeamInverseCoordinates, hy, ↓reduceIte]
    have hg : ContMDiff halfCollarModel signedCollarModel ∞
        (fun p : Torus × EuclideanHalfSpace 1 => (p.1, -p.2.val 0)) :=
      contMDiff_fst.prodMk ((contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd).neg)
    have hc := (P.leftCollar j).symm.mdifferentiableAt (by simp) hx
    have hmf : mfderiv C.model signedCollarModel (P.surgerySeamInverseCoordinates j) x =
        mfderiv C.model signedCollarModel
          ((fun p : Torus × EuclideanHalfSpace 1 => (p.1, -p.2.val 0)) ∘
            (P.leftCollar j).symm) x := by
      ext v
      exact congrArg (fun A => A v) (he.mfderiv_eq (I := C.model) (I' := signedCollarModel))
    rw [hmf, mfderiv_comp x (hg.mdifferentiableAt (by simp)) hc]
    have hgInj := injective_mfderiv_scaledHalfSpaceOneProductCoordinate torusModel
      (σ := (-1 : ℝ)) (by norm_num) ((P.leftCollar j).symm x)
    have hgEq : (fun p : Torus × EuclideanHalfSpace 1 => (p.1, -p.2.val 0)) =
        (fun p : Torus × EuclideanHalfSpace 1 => (p.1, (-1 : ℝ) * p.2.val 0)) := by
      funext p
      simp only [neg_one_mul]
    rw [hgEq]
    exact hgInj.comp (carrierSurgeryPatchTangentEquiv (P.leftCollar j).symm hx).injective
  · have he : P.surgerySeamInverseCoordinates j =ᶠ[𝓝 x]
        (fun y => ((P.matching j).symm ((P.rightCollar j).symm y).1,
          ((P.rightCollar j).symm y).2.val 0)) := by
      filter_upwards [(P.rightCollar j).open_target.mem_nhds hx] with y hy
      have hyl : y ∉ (P.leftCollar j).target := fun hl =>
        (hd (Sum.inl_ne_inr : Sum.inl j ≠ Sum.inr j)).le_bot ⟨hl, hy⟩
      simp only [surgerySeamInverseCoordinates, hyl, ↓reduceIte]
    have hg : ContMDiff halfCollarModel signedCollarModel ∞
        (fun p : Torus × EuclideanHalfSpace 1 => ((P.matching j).symm p.1, p.2.val 0)) :=
      ((P.matching j).symm.contMDiff.comp contMDiff_fst).prodMk
        (contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)
    have hc := (P.rightCollar j).symm.mdifferentiableAt (by simp) hx
    have hmf : mfderiv C.model signedCollarModel (P.surgerySeamInverseCoordinates j) x =
        mfderiv C.model signedCollarModel
          ((fun p : Torus × EuclideanHalfSpace 1 => ((P.matching j).symm p.1, p.2.val 0)) ∘
            (P.rightCollar j).symm) x := by
      ext v
      exact congrArg (fun A => A v) (he.mfderiv_eq (I := C.model) (I' := signedCollarModel))
    rw [hmf, mfderiv_comp x (hg.mdifferentiableAt (by simp)) hc]
    exact (P.surgeryRightCoordinates_injective j ((P.rightCollar j).symm x)).comp
      (carrierSurgeryPatchTangentEquiv (P.rightCollar j).symm hx).injective

theorem surgerySeamInverseCoordinates_mfderiv_bijective (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    Function.Bijective (mfderiv C.model signedCollarModel
      (P.surgerySeamInverseCoordinates j) x) := by
  have hinj := P.surgerySeamInverseCoordinates_mfderiv_injective hd j hx
  have hdim : Module.finrank ℝ (TangentSpace C.model x) =
      Module.finrank ℝ (TangentSpace signedCollarModel (P.surgerySeamInverseCoordinates j x)) :=
    by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
        Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ)
      simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv C.model signedCollarModel (P.surgerySeamInverseCoordinates j) x).toLinearMap)
    hdim).mp hinj⟩

def surgerySeamInverseCoordinatesTangentEquiv (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target) :
    TangentSpace C.model x ≃ₗ[ℝ]
      TangentSpace signedCollarModel (P.surgerySeamInverseCoordinates j x) :=
  LinearEquiv.ofBijective (mfderiv C.model signedCollarModel
    (P.surgerySeamInverseCoordinates j) x).toLinearMap
    (P.surgerySeamInverseCoordinates_mfderiv_bijective hd j hx)

theorem surgerySeamInverseCoordinatesTangentEquiv_apply (P : TorusPairing C)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (j : Fin P.count) {x : C.Carrier}
    (hx : x ∈ (P.leftCollar j).target ∪ (P.rightCollar j).target)
    (v : TangentSpace C.model x) :
    P.surgerySeamInverseCoordinatesTangentEquiv hd j hx v =
      mfderiv C.model signedCollarModel (P.surgerySeamInverseCoordinates j) x v := rfl

end GC.GraphManifold.TorusPairing
