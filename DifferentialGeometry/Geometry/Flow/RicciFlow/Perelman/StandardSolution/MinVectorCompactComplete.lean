import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostLocalBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVectorCompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lMinVec_compact_over_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    {Cpt : Set M} (hCpt : IsCompact Cpt) :
    ∃ A : ℝ, 0 ≤ A ∧
      (∀ y ∈ Cpt, lCost S T x y tau ≤ A) ∧
      (∀ Z : TangentSpace I x,
        (Z, tau) ∈ lMinDomain S T x →
        lExp S T x Z tau ∈ Cpt →
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A) ∧
      IsCompact {Z : TangentSpace I x |
        (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Cpt} := by
  obtain ⟨A, hA, hcost⟩ :=
    lCost_bddAbove_on_compact_of_rm (I := I) S hS K T tau htau
      hreg hRm x hCpt
  have hact : ∀ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x →
      lExp S T x Z tau ∈ Cpt →
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤ A := by
    intro Z hmin hend
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 tau := by
        change lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
          (lRegularizedCurve S T x Z) tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau :=
        ((mem_lMinDomain S T x Z tau).mp hmin).2
      _ ≤ A := hcost (lExp S T x Z tau) hend
  exact ⟨A, hA, hcost, hact,
    isCompact_lMinVec_over_of_rm (I := I) S hS K T hg x tau htau
      hreg hRm hCpt A hact⟩

end DifferentialGeometry.PDE.RicciFlow

end
