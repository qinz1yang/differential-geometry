import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The covariant derivative of the rough Laplacian of `∇ᵏRm`

Thin Ricci-flow specialisation of the formalism-A metric-trace/∇ commutation
bridge `nabla_metricTraceFirstTwo0S` (`Tensor/RSTensor/MetricTrace/NablaTraceGen.lean`)
to the iterated curvature tower `nablaKRm04Field`.

`Δ(∇ᵏRm) = roughLap0S(∇ᵏRm) = metricTraceFirstTwoField g (∇^{k+2}Rm)`
(the metric trace of the two new derivative slots of `∇²(∇ᵏRm) = ∇^{k+2}Rm`).
`nabla_roughLap0S_nablaKRm` differentiates it covariantly along `X`, expressing the
result as the slot-shifted trace of `∇^{k+3}Rm`:

`∇(Δ∇ᵏRm)(X :: tail) = Σᵢⱼ gⁱʲ · ∇^{k+3}Rm (X :: eᵢ :: eⱼ :: tail)`.

This is the clean trace/∇-commute (no curvature term); the slot-shift discrepancy
between this `metricTrace(slots 1,2 of ∇^{k+3}Rm)` and the standard rough-Laplacian
trace `Δ(∇^{k+1}Rm) = metricTrace(slots 0,1)` is converted to controlled
`Rm ∗ ∇ᵏRm` star terms downstream, via the all-`k` Ricci identity
`nablaKRm04_ricciIdentityAt`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **The covariant derivative of the rough Laplacian of `∇ᵏRm`, as a slot-shifted
trace of `∇^{k+3}Rm`.**  Specialisation of `nabla_metricTraceFirstTwo0S` to
`A = ∇^{k+2}Rm = nablaKRm04Field S t (k+2)`, identifying the differentiated factor
`totalNabla0SFun (∇^{k+2}Rm)` with `∇^{k+3}Rm` via `nablaKRm04Field_succ`. -/
theorem nabla_roughLap0S_nablaKRm
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          nablaKRm04Field (I := I) S t (k + 3) x
            (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) := by
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      (S.family.connection t) (1 : WithTop ℕ∞) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one
        (I := I) (M := M) (S.base.metric t)
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen (I := I)
      (S.family.connection t) (S.base.metric t) := by
    simpa [SolutionFamily.connection, metricCov] using
      leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (S.base.metric t)
  refine (nabla_metricTraceFirstTwo0S (I := I) (M := M) (S.family.connection t) hcov
    (S.base.metric t) hmc (nablaKRm04Field (I := I) S t (k + 2)) basis gInv hinv X
    tail).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1

/-- **The spatial Laplacian–covariant-derivative commutator `[Δ, ∇]∇ᵏRm`, all `k`,
as a trace-difference of `∇^{k+3}Rm`.**  The bundled all-`k` analogue of the `k = 1`
`nablaLapComm_trace`:

`Δ(∇^{k+1}Rm)(X, tail) − ∇(Δ∇ᵏRm)(X, tail)
  = Σᵢⱼ gⁱʲ · [ ∇^{k+3}Rm(eᵢ, eⱼ, X, tail) − ∇^{k+3}Rm(X, eᵢ, eⱼ, tail) ]`.

The left side is the spatial commutator `[Δ, ∇_X]∇ᵏRm`: `Δ(∇^{k+1}Rm) =
roughLap(∇^{k+1}Rm) = metricTraceFirstTwo0STensor g (∇^{k+3}Rm)` (trace of the two
outer derivative slots), and `∇(Δ∇ᵏRm)` is `nabla_roughLap0S_nablaKRm` (trace of the
two middle derivative slots).  The right side is their difference — the cyclic
antisymmetrisation of the three leading derivative slots of `∇^{k+3}Rm`, which the
all-`k` Ricci identity `nablaKRm04_ricciIdentityAt` converts to controlled
`Rm ∗ ∇ᵏRm` / `∇Rm ∗ ∇^{k-1}Rm` star terms (the next StarSum2 brick). -/
theorem spatialComm_nablaKRm_traceDiff
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric t) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric t)
        (nablaKRm04Field (I := I) S t (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection t)
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric t)
          (nablaKRm04Field (I := I) S t (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          (nablaKRm04Field (I := I) S t (k + 3) x
              (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
            nablaKRm04Field (I := I) S t (k + 3) x
              (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail))) := by
  rw [metricTraceFirstTwo0STensor_apply (I := I) (S.base.metric t)
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := I) (S.base.metric t) basis gInv hinv
    (nablaKRm04Field (I := I) S t (k + 3) x) (Fin.cons X tail)]
  rw [metricTrace0S2InBasis]
  rw [nabla_roughLap0S_nablaKRm (I := I) (M := M) S t k basis gInv hinv X tail]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_sub]

/-- **Spatial commutator `[Δ,∇]∇ᵏRm`, all `k`, with the controlled curvature half
split off.**  Telescoping the trace-difference bracket of
`spatialComm_nablaKRm_traceDiff` through the middle slot ordering `(eᵢ, X, eⱼ)`
splits it into:

* the **slots-(1,2) antisymmetrisation** `∇^{k+3}Rm(eᵢ,eⱼ,X,tail) −
  ∇^{k+3}Rm(eᵢ,X,eⱼ,tail)` = `∇_{eᵢ}([∇_{eⱼ},∇_X]∇ᵏRm)` — the residual term-B,
  closed downstream by the route-4 curvature-action Leibniz; and
* the **controlled curvature term** `curvatureAction(rm13)(∇^{k+1}Rm)(eᵢ,X,eⱼ::tail)`
  — the slots-(0,1) antisymmetrisation, supplied directly by the all-`k` Ricci
  identity `nablaKRm04_ricciIdentityAt` at level `k+1`, hence bounded by
  `|Rm|·|∇^{k+1}Rm|` via `abs_curvatureAction0SAt_orthoBasis_le`. -/
theorem spatialComm_nablaKRm_split
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t : DifferentialGeometry.Integral.Connection.RealTimeInterval.RegularTime D)
    (k : ℕ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) (M := M) (S.base.metric (t : Real)) x basis gInv)
    (X : TangentSpace I x) (tail : Fin (4 + k) -> TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) (S.base.metric (t : Real))
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
        (Fin.cons X tail) -
      totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (4 + k) (S.family.connection (t : Real))
        (metricTraceFirstTwoField (I := I) (M := M) (S.base.metric (t : Real))
          (nablaKRm04Field (I := I) S (t : Real) (k + 2))) x (Fin.cons X tail) =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          ((nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) (basis j) (Fin.cons X tail)) -
              nablaKRm04Field (I := I) S (t : Real) (k + 3) x
                (metricTraceInput (I := I) (basis i) X (Fin.cons (basis j) tail))) +
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (nablaKRm04Field (I := I) S (t : Real) (k + 1) x)
              (basis i) X (Fin.cons (basis j) tail)) := by
  rw [spatialComm_nablaKRm_traceDiff (I := I) S (t : Real) k basis gInv hinv X tail]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have h := (nablaKRm04_ricciIdentityAt (I := I) S hS t (k + 1) x)
    (basis i) X (Fin.cons (basis j) tail)
  have hCC :
      (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (Fin.cons X (metricTraceInput (I := I) (basis i) (basis j) tail)) =
        (nablaKRm04Field (I := I) S (t : Real) (k + 3) x)
          (metricTraceInput (I := I) X (basis i) (Fin.cons (basis j) tail)) := rfl
  rw [hCC]
  linarith [h]

end DifferentialGeometry.PDE.RicciFlow
