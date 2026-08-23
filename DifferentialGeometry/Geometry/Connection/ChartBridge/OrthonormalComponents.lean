import DifferentialGeometry.Geometry.Connection.ChartBridge.MetricInverse
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.FiniteArrayNorm

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

theorem inner0S_orthoBasis_eq_compContract
    [Module.Finite Real E]
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A B : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    inner0S (I := I) g x s A B =
      ∑ m : Fin s → Idx,
        tensor0SComponent (I := I) A (fun i => basis i) m *
          tensor0SComponent (I := I) B (fun i => basis i) m := by
  classical
  rw [inner0S_eq_coord (I := I) g x s basis (identityInvMetric (Idx := Idx))
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A B]
  rw [coordInner0S_identity_eq_sum (I := I) (x := x) s A B basis]

theorem compNormSqMulti_orthoBasis_eq_normSq0S
    [FiniteDimensional Real E]
    (g : SmoothMetric_gen I M) {x : M} {s : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    compNormSqMulti (fun idx : Fin s → Idx => A (fun p => basis (idx p))) =
      normSq0S (I := I) g x s A := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis
    (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth) A]
  unfold compNormSqMulti
  refine Finset.sum_congr rfl fun idx _ => ?_
  rfl

end DifferentialGeometry.Geometry.Connection
