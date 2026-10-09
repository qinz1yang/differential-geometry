import DifferentialGeometry.Topology.ThreeManifold.UncappingLocalMap
import DifferentialGeometry.Topology.ThreeManifold.CappedCoreBandGluing
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem uncappingInteriorMap_orientation_core
    (H : C.UncappingQuotient ≃ₜ M.Carrier)
    (hcore : ∀ x : T.core, H (Quot.mk C.innerCapRelation
      (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
        (C.coreImageHomeomorph x))) = x.val)
    (x : T.core) :
    letI := C.coreCharts
    ∀ hx : (𝓡∂ 3).IsInteriorPoint x,
      Orientation.map (Fin 3)
        ((C.isLocalDiffeomorphAt_uncappingInteriorMap_core H hcore x hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv
        (N.orientation.orientation (C.coreInclusion x)) = M.orientation.orientation x.val := by
  let _ := C.coreCharts
  let _ := C.coreSmooth
  intro hx
  let f : T.core → C.uncappingInterior :=
    fun z => ⟨C.coreInclusion z, C.coreInclusion_mem_uncappingInterior z⟩
  have hf : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ f :=
    (ContMDiff.subtypeVal_comp_iff C.uncappingInterior f).mp C.core_embedding.contMDiff
  have heq : (C.uncappingInteriorMap H) ∘ f = (Subtype.val : T.core → M.Carrier) :=
    funext (C.uncappingInteriorMap_core H hcore)
  have hloc := C.isLocalDiffeomorphAt_uncappingInteriorMap_core H hcore x hx
  let L : E3 ≃ₗ[ℝ] E3 := (hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  obtain ⟨hi, hj, hor⟩ := C.coreInclusion_inverse_orientation x hx
  let A : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : T.core → M.Carrier) x).toLinearMap hi
  let B : E3 ≃ₗ[ℝ] E3 := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) (𝓡 3) C.coreInclusion x).toLinearMap hj
  have hdf : (mfderiv (𝓡∂ 3) (𝓡 3) f x : E3 →L[ℝ] E3) =
      mfderiv (𝓡∂ 3) (𝓡 3) C.coreInclusion x :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp f x).symm
  have hchain := mfderiv_comp x (hloc.mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))
  rw [heq] at hchain
  have hLB (v : E3) : L (B v) = A v := by
    have h := congrArg (fun D : E3 →L[ℝ] E3 => D v) hchain
    have hfv : mfderiv (𝓡∂ 3) (𝓡 3) f x v = B v :=
      congrArg (fun D : E3 →L[ℝ] E3 => D v) hdf
    change A v = L (mfderiv (𝓡∂ 3) (𝓡 3) f x v) at h
    rw [hfv] at h
    exact h.symm
  have hL : L = B.symm.trans A := by
    apply LinearEquiv.ext
    intro v
    have h := hLB (B.symm v)
    rw [B.apply_symm_apply] at h
    exact h
  change Orientation.map (Fin 3) L (N.orientation.orientation (C.coreInclusion x)) = _
  rw [hL]
  exact hor

end DifferentialGeometry.Topology.SphericalCapping
