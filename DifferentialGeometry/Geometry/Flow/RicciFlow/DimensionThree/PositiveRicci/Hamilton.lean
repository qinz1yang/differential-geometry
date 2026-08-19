import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Compactness

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HamiltonPositiveRicci

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem hamilton_positive_ricci
    (hM : Closed3Manifold (I := I) (M := M))
    (hpos : AdmitsPosRicci (I := I) (M := M)) :
    AdmitsConstPosSec (I := I) (M := M) ∧
      SphericalSpaceForm (I := I) (M := M) := by
  haveI : I.Boundaryless := hM.2.2.1
  haveI : NeZero (Module.finrank Real E) := ⟨by
    rw [hM.2.2.2]; norm_num⟩
  exact hamilton_positive_ricci_classification (I := I) (M := M) hM hpos


end HamiltonPositiveRicci
end RicciFlow
end PDE
end DifferentialGeometry
