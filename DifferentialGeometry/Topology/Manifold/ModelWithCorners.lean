import Mathlib.Geometry.Manifold.Diffeomorph

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]

instance boundaryless_transContinuousLinearEquiv
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (e : E ≃L[𝕜] F) :
    (I.transContinuousLinearEquiv e).Boundaryless where
  range_eq_univ := by
    rw [I.transContinuousLinearEquiv_range, I.range_eq_univ, Set.image_univ]
    exact e.surjective.range_eq

end ModelWithCorners
