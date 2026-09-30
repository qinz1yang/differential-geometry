import DifferentialGeometry.Analysis.Calculus.Derivative.LeftEndpoint
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real


set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.Analysis


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivWithin_inter_Iic_eq_of_mem_nhdsWithin {f : ℝ → F} {J : Set ℝ} {t : ℝ}
    (h : Iic t ∈ 𝓝[J] t) : derivWithin f (J ∩ Iic t) t = derivWithin f J t :=
  derivWithin_congr_set (mem_nhdsWithin_iff_eventuallyEqSet.mp h).symm

theorem derivWithin_eq_derivWithin_Iic_of_mem_nhdsLE {f : ℝ → F} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (hJ : J ∈ 𝓝[≤] t)
    (hu : UniqueDiffWithinAt ℝ J t) : derivWithin f J t = derivWithin f (Iic t) t :=
  (hasDerivWithinAt_left_of_mem_nhdsLE hf hJ).derivWithin hu

theorem derivWithin_inter_Iic_eq_of_differentiableWithinAt {f : ℝ → F} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (h : UniqueDiffWithinAt ℝ (J ∩ Iic t) t) :
    derivWithin f (J ∩ Iic t) t = derivWithin f J t :=
  (hf.hasDerivWithinAt.mono inter_subset_left).derivWithin h

end DifferentialGeometry.Analysis
