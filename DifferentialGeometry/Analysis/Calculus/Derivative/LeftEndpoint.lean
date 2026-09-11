import Mathlib.Analysis.Calculus.Deriv.Slope


set_option autoImplicit false
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood


theorem hasDerivWithinAt_left_of_mem_nhdsLE
    {f : ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hf : DifferentiableWithinAt ℝ f J t) (hJ : J ∈ 𝓝[≤] t) :
    HasDerivWithinAt f (derivWithin f (Iic t) t) J t := by
  have hleft : HasDerivWithinAt f (derivWithin f J t) (Iic t) t :=
    hf.hasDerivWithinAt.mono_of_mem_nhdsWithin hJ
  rw [hleft.derivWithin (uniqueDiffWithinAt_Iic t)]
  exact hf.hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
