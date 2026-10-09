import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphMapDerivative
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionSurjectivity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem finrank_range_fderiv_normal_graph_map_eq
    (L : Submodule ℝ H) [FiniteDimensional ℝ L]
    (o : H) (g : L → Lᗮ) (T : H → L) (z : H)
    (hg : DifferentiableAt ℝ g (T z)) (hT : DifferentiableAt ℝ T z)
    (hclose : ‖fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z -
      L.starProjection‖ < 1) :
    Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z).toLinearMap) =
        Module.finrank ℝ L := by
  let A : H →L[ℝ] L := fderiv ℝ T z
  let B : L →L[ℝ] Lᗮ := fderiv ℝ g (T z)
  let C : L →L[ℝ] H := L.subtypeL+Lᗮ.subtypeL.comp B
  have hd : HasFDerivAt (fun y => o + orthogonalCoordinateSum L (T y, g (T y)))
      (L.subtypeL.comp A+Lᗮ.subtypeL.comp (B.comp A)) z := by
    exact ((L.subtypeL.hasFDerivAt.comp z hT.hasFDerivAt).add
      (Lᗮ.subtypeL.hasFDerivAt.comp z (hg.hasFDerivAt.comp z hT.hasFDerivAt))).const_add o
  have hfactor : fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z =
      C.comp A := by
    rw [hd.fderiv]
    ext w
    rfl
  have hleft (t : L) : L.orthogonalProjectionOnto (C t)=t := by
    change L.orthogonalProjectionOnto ((t : H)+(B t : H))=t
    rw [map_add,L.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal (B t).property,add_zero]
  have hCinj : Function.Injective C := by
    intro s t h
    have hh := congrArg L.orthogonalProjectionOnto h
    simpa only [hleft] using hh
  have hsurj := L.surjective_orthogonalProjectionOnto_comp_of_norm_sub_lt_one
    (fderiv ℝ (fun y => o + orthogonalCoordinateSum L (T y, g (T y))) z) hclose
  have hAsurj : Function.Surjective A := by
    intro t
    obtain ⟨w,hw⟩ := hsurj t
    refine ⟨w,?_⟩
    simpa only [hfactor,ContinuousLinearMap.comp_apply,hleft] using hw
  have hrange : LinearMap.range (C.comp A).toLinearMap = LinearMap.range C.toLinearMap := by
    ext y
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨A w,rfl⟩
    · rintro ⟨t,rfl⟩
      obtain ⟨w,rfl⟩ := hAsurj t
      exact ⟨w,rfl⟩
  rw [hfactor,hrange]
  exact LinearMap.finrank_range_of_inj hCinj

end DifferentialGeometry.Analysis
