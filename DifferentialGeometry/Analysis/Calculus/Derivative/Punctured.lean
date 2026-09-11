import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_of_punct {f g : ℝ → E} {x : ℝ}
    (h : ∀ᶠ y in 𝓝[≠] x, HasDerivAt f (g y) y) (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : HasDerivAt f (g x) x := by
  have hGT : ∀ᶠ y in 𝓝[>] x, HasDerivAt f (g y) y :=
    h.filter_mono (nhdsGT_le_nhdsNE x)
  have hLT : ∀ᶠ y in 𝓝[<] x, HasDerivAt f (g y) y :=
    h.filter_mono (nhdsLT_le_nhdsNE x)
  have hgGT : Tendsto g (𝓝[>] x) (𝓝 (g x)) := tendsto_inf_left hg
  have hgLT : Tendsto g (𝓝[<] x) (𝓝 (g x)) := tendsto_inf_left hg
  have hright : HasDerivWithinAt f (g x) (Ici x) x := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := {y | HasDerivAt f (g y) y})
    · intro y hy
      exact hy.differentiableAt.differentiableWithinAt
    · exact hf.continuousWithinAt
    · exact hGT
    · exact hgGT.congr' (hGT.mono fun _ hy => hy.deriv.symm)
  have hleft : HasDerivWithinAt f (g x) (Iic x) x := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (s := {y | HasDerivAt f (g y) y})
    · intro y hy
      exact hy.differentiableAt.differentiableWithinAt
    · exact hf.continuousWithinAt
    · exact hLT
    · exact hgLT.congr' (hLT.mono fun _ hy => hy.deriv.symm)
  have hfull := hleft.union hright
  rw [Iic_union_Ici] at hfull
  exact hfull.hasDerivAt univ_mem

end DifferentialGeometry
