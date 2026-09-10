import Mathlib.Geometry.Manifold.ContMDiff.Basic

open Set Function Manifold TopologicalSpace
open scoped ContDiff
set_option autoImplicit false
namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}


theorem contMDiffWithinAt_subtypeVal_comp_iff (U : Opens N) (f : M → U) (s : Set M) (x : M) :
    ContMDiffWithinAt I J n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I J n f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..


theorem contMDiffAt_subtypeVal_comp_iff (U : Opens N) (f : M → U) (x : M) :
    ContMDiffAt I J n (Subtype.val ∘ f) x ↔ ContMDiffAt I J n f x :=
  contMDiffWithinAt_subtypeVal_comp_iff U f univ x


theorem contMDiffOn_subtypeVal_comp_iff (U : Opens N) (f : M → U) (s : Set M) :
    ContMDiffOn I J n (Subtype.val ∘ f) s ↔ ContMDiffOn I J n f s := by
  simp only [ContMDiffOn, contMDiffWithinAt_subtypeVal_comp_iff]


theorem contMDiff_subtypeVal_comp_iff (U : Opens N) (f : M → U) :
    ContMDiff I J n (Subtype.val ∘ f) ↔ ContMDiff I J n f := by
  simp only [ContMDiff, contMDiffAt_subtypeVal_comp_iff]

end DifferentialGeometry.Manifold
