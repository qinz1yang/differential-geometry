import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod

open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem derivative_comp_eq_id_of_left_inverse_on_halfspace
    {f : E × ℝ → F × ℝ} {g : F × ℝ → E × ℝ} {p : E}
    {A : E × ℝ →L[ℝ] F × ℝ} {B : F × ℝ →L[ℝ] E × ℝ}
    (hf : HasFDerivWithinAt f A {q : E × ℝ | 0 ≤ q.2} (p, 0))
    (hg : HasFDerivWithinAt g B {q : F × ℝ | 0 ≤ q.2} (f (p, 0)))
    (hleft : (g ∘ f) =ᶠ[𝓝[{q : E × ℝ | 0 ≤ q.2}] (p, (0 : ℝ))] id)
    (hmap : ∀ᶠ q in 𝓝[{q : E × ℝ | 0 ≤ q.2}] (p, (0 : ℝ)), 0 ≤ (f q).2) :
    B.comp A = ContinuousLinearMap.id ℝ (E × ℝ) := by
  have hUD : UniqueDiffWithinAt ℝ {q : E × ℝ | 0 ≤ q.2} (p, 0) := by
    simpa only [Set.univ_prod, Set.preimage, Set.mem_Ici] using
      (uniqueDiffWithinAt_univ (𝕜 := ℝ) (x := p)).prod (uniqueDiffWithinAt_Ici 0)
  have hcomp := hg.comp_of_tendsto (p, 0) hf
    (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hmap⟩)
  exact hUD.eq
    (hcomp.congr_of_eventuallyEq hleft.symm
      (hleft.eq_of_nhdsWithin (by simp)).symm)
    (hasFDerivWithinAt_id (p, 0) {q : E × ℝ | 0 ≤ q.2})

theorem derivative_injective_of_left_inverse_on_halfspace
    {f : E × ℝ → F × ℝ} {g : F × ℝ → E × ℝ} {p : E}
    {A : E × ℝ →L[ℝ] F × ℝ} {B : F × ℝ →L[ℝ] E × ℝ}
    (hf : HasFDerivWithinAt f A {q : E × ℝ | 0 ≤ q.2} (p, 0))
    (hg : HasFDerivWithinAt g B {q : F × ℝ | 0 ≤ q.2} (f (p, 0)))
    (hleft : (g ∘ f) =ᶠ[𝓝[{q : E × ℝ | 0 ≤ q.2}] (p, (0 : ℝ))] id)
    (hmap : ∀ᶠ q in 𝓝[{q : E × ℝ | 0 ≤ q.2}] (p, (0 : ℝ)), 0 ≤ (f q).2) :
    Function.Injective A := by
  have hcomp := derivative_comp_eq_id_of_left_inverse_on_halfspace hf hg hleft hmap
  have hBA (v : E × ℝ) : B (A v) = v :=
    congrArg (fun L : E × ℝ →L[ℝ] E × ℝ => L v) hcomp
  exact Function.LeftInverse.injective hBA

end DifferentialGeometry.Analysis
