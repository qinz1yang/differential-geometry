import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.HamiltonBaseProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.ResidualCost

set_option autoImplicit false

/-!
# Level-zero arbitrary-dimensional curvature residual

This module joins the solution-level Hamilton evolution of lowered Riemann to
the quantitative `StarSum2` cost ledger.  It is the base case for the direct
arbitrary-dimensional curvature-tower recursion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [InnerProductSpace Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]
variable {D : RealTimeInterval}

/-- The canonical level-zero reaction field has the exact residual cost and
realizes the curvature heat equation in every finite orthonormal basis. -/
theorem e0Residual
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] :
    StarSum2Cost (I := I) Idx S (t : Real) 0
        (e0Field (I := I) S (t : Real))
        (rmResidualCost (Fintype.card Idx) 0) ∧
      ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x))
          (_horth : ∀ i j : Idx,
            (S.base.metric (t : Real)).inner x (basis i) (basis j) =
              if i = j then (1 : Real) else 0)
          (m : Fin 4 → Idx),
        HasDerivWithinAt
          (fun r : Real ↦
            tensor0SComponent (I := I)
              (nablaKRm04Field (I := I) S r 0 x) (fun i ↦ basis i) m)
          (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx))
                (nablaKRm04Field (I := I) S (t : Real) 2 x) +
              e0Field (I := I) S (t : Real) x)
            (fun i ↦ basis i) m)
          D.carrier (t : Real) := by
  refine ⟨?_, ?_⟩
  · simpa only [rmResidualCost] using
      e0Field_cost_any (I := I) (Idx := Idx) S (t : Real)
  · intro x basis _horth m
    have hlhs :
        (fun r : Real ↦
          tensor0SComponent (I := I)
            (nablaKRm04Field (I := I) S r 0 x) (fun i ↦ basis i) m) =
          (fun r : Real ↦ S.base.rm04 r x (fun p ↦ basis (m p))) := rfl
    have hval :
        tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx))
                (nablaKRm04Field (I := I) S (t : Real) 2 x) +
              e0Field (I := I) S (t : Real) x)
            (fun i ↦ basis i) m =
          tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx))
                (nablaKRm04Field (I := I) S (t : Real) 2 x))
              (fun i ↦ basis i) m +
            e0Field (I := I) S (t : Real) x (fun p ↦ basis (m p)) := rfl
    have horth' : ∀ i j : Idx,
        (S.family.metric (t : Real)).inner x (basis i) (basis j) =
          if i = j then (1 : Real) else 0 := by
      simpa only [SolutionOn.family_metric] using _horth
    rw [hlhs, hval,
      e0Field_comp_any (I := I) S (t : Real) basis horth' m]
    simpa only [rmBaseReact, nablaKRm04Field_zero] using
      rm04Base_of_solution_any (I := I) S hS t x basis _horth m

/-- Compatibility wrapper exposing the canonical level-zero residual as an
existential field. -/
theorem rmResidual_zero
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : RealTimeInterval.RegularTime D)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 4,
      StarSum2Cost (I := I) Idx S (t : Real) 0 T
          (rmResidualCost (Fintype.card Idx) 0) ∧
      ∀ (x : M) (basis : Module.Basis Idx Real (TangentSpace I x))
          (_horth : ∀ i j : Idx,
            (S.base.metric (t : Real)).inner x (basis i) (basis j) =
              if i = j then (1 : Real) else 0)
          (m : Fin 4 → Idx),
        HasDerivWithinAt
          (fun r : Real ↦
            tensor0SComponent (I := I)
              (nablaKRm04Field (I := I) S r 0 x) (fun i ↦ basis i) m)
          (tensor0SComponent (I := I)
            (metricTrace0S2TensorInBasis (I := I) basis
                (identityInvMetric (Idx := Idx))
                (nablaKRm04Field (I := I) S (t : Real) 2 x) + T x)
            (fun i ↦ basis i) m)
          D.carrier (t : Real) := by
  exact ⟨e0Field (I := I) S (t : Real), e0Residual (I := I) S hS t⟩

end DifferentialGeometry.PDE.RicciFlow
