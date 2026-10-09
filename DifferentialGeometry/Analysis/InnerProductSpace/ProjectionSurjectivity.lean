import DifferentialGeometry.Analysis.Normed.Operator.SurjectivePerturbation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

set_option autoImplicit false
noncomputable section
namespace Submodule

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem surjective_orthogonalProjectionOnto_comp_of_norm_sub_lt_one
    (P : Submodule 𝕜 H) [CompleteSpace P]
    (A : H →L[𝕜] H) (hclose : ‖A - P.starProjection‖ < 1) :
    Function.Surjective (P.orthogonalProjectionOnto.comp A) := by
  apply ContinuousLinearMap.surjective_of_norm_comp_sub_id_lt_one _ P.subtypeL
  apply lt_of_le_of_lt _ hclose
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro n
  have heq : ((P.orthogonalProjectionOnto.comp A).comp P.subtypeL -
      ContinuousLinearMap.id 𝕜 P) n =
        P.orthogonalProjectionOnto ((A - P.starProjection) (n : H)) := by
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, Submodule.subtypeL_apply, map_sub,
      P.starProjection_mem_subspace_eq_self, P.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [heq]
  exact (P.norm_orthogonalProjectionOnto_apply_le _).trans
    ((A - P.starProjection).le_opNorm (n : H))

theorem surjective_fderiv_orthogonalProjectionOnto_of_error
    (P : Submodule 𝕜 H) [CompleteSpace P]
    (f : H → H) (o x : H) (hf : DifferentiableAt 𝕜 f x)
    (herror : ‖fderiv 𝕜 (fun y => f y - P.starProjection (y - o)) x‖ < 1) :
    Function.Surjective (fderiv 𝕜 (fun y => P.orthogonalProjectionOnto (f y)) x) := by
  have hp : HasFDerivAt (fun y => P.starProjection (y - o)) P.starProjection x := by
    have hi : HasFDerivAt (fun y : H => y - o) (ContinuousLinearMap.id 𝕜 H) x :=
      (hasFDerivAt_id (𝕜 := 𝕜) x).sub_const o
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using
      P.starProjection.hasFDerivAt.comp (f := fun y : H => y - o) x hi
  have heq : fderiv 𝕜 (fun y => f y - P.starProjection (y - o)) x =
      fderiv 𝕜 f x - P.starProjection := (hf.hasFDerivAt.sub hp).fderiv
  have hproj : fderiv 𝕜 (fun y => P.orthogonalProjectionOnto (f y)) x =
      P.orthogonalProjectionOnto.comp (fderiv 𝕜 f x) :=
    (P.orthogonalProjectionOnto.hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  rw [hproj]
  apply surjective_orthogonalProjectionOnto_comp_of_norm_sub_lt_one P
  rwa [← heq]

end Submodule
