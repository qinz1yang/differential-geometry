import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

theorem localShiUniformConstant (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    LocalShiUniformConstant.{u, uE, uH} I :=
  fun m _ _ _ hT hK hR => shi_local_all_orders_uniform_constant I m hT hK hR

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
