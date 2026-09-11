import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem mem_lCutDomain_of_distinct_minimizer_same_endpoint
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z W : TangentSpace I x} {tau : Real}
    (hcut : (Z : E) ∈ lCutDomain S T x tau)
    (hWne : W ≠ Z)
    (hWmin : ((W : E), tau) ∈ lMinDomain S T x)
    (hend : lExp S T x W tau = lExp S T x Z tau) :
    (W : E) ∈ lCutDomain S T x tau := by
  apply (mem_lCutDomain S T x tau (W : E)).2
  refine ⟨hWmin, ?_⟩
  rintro ⟨sigma, htauSigma, hWsigma⟩
  have htau : 0 < tau := lMinDomain_pos S T x (W : E) tau hWmin
  have hZmin : ((Z : E), tau) ∈ lMinDomain S T x :=
    ((mem_lCutDomain S T x tau (Z : E)).1 hcut).1
  have hZW : Z = W :=
    lMinimizingVector_unique_lt S hS T x (Z := W) (W := Z)
      hWsigma htau htauSigma hZmin hend.symm
  exact hWne hZW.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
