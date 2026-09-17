import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Topology.Manifold.Quotient

open scoped ContDiff Manifold

namespace AddCircle

noncomputable def diffeomorphCircle :
    Diffeomorph 𝓘(ℝ, ℝ) (𝓡 1) (AddCircle (1 : ℝ)) Circle ∞ where
  toEquiv := (homeomorphCircle one_ne_zero).toEquiv
  contMDiff_toFun := by
    apply isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective QuotientAddGroup.mk_surjective
    have heq (t : ℝ) : homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ)) =
        Circle.exp (2 * Real.pi * t) := by
      rw [homeomorphCircle_apply, toCircle_apply_mk]
      congr 1
      ring
    exact (contMDiff_circleExp.comp (contDiff_const.mul contDiff_id).contMDiff).congr heq
  contMDiff_invFun := by
    have hf : ContMDiff (𝓡 1) (𝓡 1) ∞
        ((homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : Circle → AddCircle (1 : ℝ)) :=
      DifferentialGeometry.Manifold.contMDiff_homeomorphChartedSpace (𝓡 1)
        (homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
    exact (DifferentialGeometry.Manifold.contMDiff_chartedSpaceTransHomeomorph_iff
      (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)) euclideanSpaceFinOneHomeomorphReal
      euclideanSpaceFinOneContinuousLinearEquivReal (fun _ => rfl) (I₀ := 𝓡 1)).mpr hf

end AddCircle
