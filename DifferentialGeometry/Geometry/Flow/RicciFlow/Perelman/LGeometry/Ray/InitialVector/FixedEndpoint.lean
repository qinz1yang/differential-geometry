import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.InitialVector.VariableEndpoint

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
theorem isBounded_range_initialVector_of_lRegularizedAction_le_fixed_parameter
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : Nat → TangentSpace I x) (B A : Real) (hB : 0 < B)
    (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular)
    (hdom : ∀ n, B ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n,
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 B ≤ A) :
    Bornology.IsBounded (Set.range Z) := by
  exact isBounded_range_initialVector_of_lRegularizedAction_le
    (I := I) S hS T x Z (fun _ ↦ B) B B A hB
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) hslab hdom hact

end DifferentialGeometry.PDE.RicciFlow.Perelman
