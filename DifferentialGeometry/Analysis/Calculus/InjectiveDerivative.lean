import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

theorem ContinuousLinearMap.hasDerivWithinAt_of_injective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) (hA : Function.Injective A)
    {f : 𝕜 → E} {f' : E} {s : Set 𝕜} {x : 𝕜}
    (hf : HasDerivWithinAt (fun t => A (f t)) (A f') s x) : HasDerivWithinAt f f' s x := by
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective A.toLinearMap
    (LinearMap.ker_eq_bot_of_injective hA)
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x hf
  have hLA (v : E) : L (A v) = v := LinearMap.congr_fun hL v
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', hLA] using h

theorem ContinuousLinearMap.hasDerivWithinAt_comp_iff_of_injective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) (hA : Function.Injective A)
    {f : 𝕜 → E} {f' : E} {s : Set 𝕜} {x : 𝕜} :
    HasDerivWithinAt (fun t => A (f t)) (A f') s x ↔ HasDerivWithinAt f f' s x := by
  exact ⟨A.hasDerivWithinAt_of_injective hA, fun h =>
    A.hasFDerivAt.comp_hasDerivWithinAt x h⟩

theorem ContinuousLinearMap.hasDerivAt_comp_iff_of_injective
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →L[𝕜] F) (hA : Function.Injective A)
    {f : 𝕜 → E} {f' : E} {x : 𝕜} :
    HasDerivAt (fun t => A (f t)) (A f') x ↔ HasDerivAt f f' x := by
  rw [← hasDerivWithinAt_univ, ← hasDerivWithinAt_univ]
  exact A.hasDerivWithinAt_comp_iff_of_injective hA
