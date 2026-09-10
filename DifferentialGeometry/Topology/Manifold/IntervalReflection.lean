import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section
open Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

def unitIntervalReflection : Diffeomorph (𝓡∂ 1) (𝓡∂ 1) unitInterval unitInterval ∞ where
  toEquiv := unitInterval.symmHomeomorph.toEquiv
  contMDiff_toFun := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨unitInterval.continuous_symm, contMDiff_const.sub contMDiff_subtypeVal_Icc⟩
  contMDiff_invFun := by
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨unitInterval.continuous_symm, contMDiff_const.sub contMDiff_subtypeVal_Icc⟩

@[simp] theorem unitIntervalReflection_apply (t : unitInterval) :
    unitIntervalReflection t = unitInterval.symm t := rfl

@[simp] theorem unitIntervalReflection_symm_apply (t : unitInterval) :
    unitIntervalReflection.symm t = unitInterval.symm t := rfl

end DifferentialGeometry.Topology.Manifold
