import Mathlib.Geometry.Manifold.Immersion

set_option autoImplicit false
open scoped Manifold ContDiff

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

theorem ModelWithCorners.isImmersion_coe (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) :
    Manifold.IsImmersion I 𝓘(𝕜, E) n I := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := PUnit.{1})
  intro x
  exact Manifold.IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    (by fun_prop) (.prodUnique ..) (by simp [Function.comp_def, chartAt_self_eq])
