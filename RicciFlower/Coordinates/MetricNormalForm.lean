import RicciFlower.Coordinates.MetricCompatibility

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# First-order metric-normal coordinate frames

This file records the algebraic "snapshot" normal-coordinate condition:
the metric components are Euclidean at a point and their first coordinate
derivatives vanish there.  This is weaker than geodesic normal coordinates.
It does not assert that coordinate lines are geodesics, nor that the chart is
obtained from the exponential map.
-/

noncomputable section

namespace RicciFlower
namespace Coordinates

open Bundle
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

/-- A first-order metric-normal local frame at `x`.

The fields say that `frame` is a `C^1` local frame near `x`, has coordinate
bracket zero at `x`, and satisfies
`g_ij(x) = delta_ij`, `partial_d g_ij(x) = 0`.

This is the Lean-facing form of the elementary quadratic coordinate-change
normalization.  Existence of such a coordinate-frame package is kept as a
separate frontier below; this structure is the reusable consumer API. -/
structure MetricNormalFormAt
    (g : SmoothRiemannianMetric I M) (x : M) where
  u : Set M
  frame : Idx -> (y : M) -> TangentSpace I y
  hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u
  isOpen_u : IsOpen u
  mem_base : x ∈ u
  bracket_zero :
    ∀ i j : Idx, VectorField.mlieBracket I (frame i) (frame j) x = 0
  metric_at :
    ∀ i j : Idx, metricCompForMetricInFrame (I := I) g frame x i j =
      if i = j then 1 else 0
  metric_deriv :
    ∀ d i j : Idx,
      extDerivFun (I := I)
        (fun y : M => metricCompForMetricInFrame (I := I) g frame y i j)
        x (frame d x) = 0

namespace MetricNormalFormAt

/-- Christoffel coefficient of a connection in the stored first-order normal
frame. -/
def gamma {g : SmoothRiemannianMetric I M} {x : M}
    (N : MetricNormalFormAt (I := I) (Idx := Idx) g x)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (i j k : Idx) : Real :=
  christoffelSymbolInFrame cov N.frame N.hframe x i j k

private theorem gamma_skew_last
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : MetricNormalFormAt (I := I) (Idx := Idx) g x)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (d a b : Idx) :
    N.gamma cov d a b + N.gamma cov d b a = 0 := by
  classical
  have hraw :=
    metricCompForMetricInFrame_extDerivFun_eq_christoffel
      (I := I) g cov hmc N.frame N.hframe N.isOpen_u N.mem_base d a b
  have h :
      (∑ p : Idx,
          christoffelSymbolInFrame cov N.frame N.hframe x d a p *
            metricCompForMetricInFrame (I := I) g N.frame x p b) +
        (∑ p : Idx,
          christoffelSymbolInFrame cov N.frame N.hframe x d b p *
            metricCompForMetricInFrame (I := I) g N.frame x a p) = 0 := by
    rw [← hraw]
    exact N.metric_deriv d a b
  simpa [gamma, N.metric_at] using h

private theorem gamma_symm_first
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : MetricNormalFormAt (I := I) (Idx := Idx) g x)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (htor : ∀ i j : Idx, cov.torsion x (N.frame i x) (N.frame j x) = 0)
    (i j k : Idx) :
    N.gamma cov i j k = N.gamma cov j i k := by
  have hi : MDiffAt (T% (N.frame i)) x :=
    ((N.hframe.contMDiffAt N.isOpen_u N.mem_base i).mdifferentiableAt (by simp))
  have hj : MDiffAt (T% (N.frame j)) x :=
    ((N.hframe.contMDiffAt N.isOpen_u N.mem_base j).mdifferentiableAt (by simp))
  have hskew :=
    torsion_coeff_eq_christoffel_skew
      (I := I) cov N.frame N.hframe i j k hi hj
  have hzero :
      N.hframe.coeff k x (cov.torsion x (N.frame i x) (N.frame j x)) = 0 := by
    rw [htor i j]
    simp
  rw [hzero, N.bracket_zero i j] at hskew
  have hsub : N.gamma cov i j k - N.gamma cov j i k = 0 := by
    simpa [gamma] using hskew.symm
  exact sub_eq_zero.mp hsub

/-- In a first-order metric-normal frame, every metric-compatible torsion-free
connection has zero Christoffel coefficients at the base point. -/
theorem gamma_eq_zero
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : MetricNormalFormAt (I := I) (Idx := Idx) g x)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htor : ∀ i j : Idx, cov.torsion x (N.frame i x) (N.frame j x) = 0)
    (i j k : Idx) :
    N.gamma cov i j k = 0 := by
  have hsk₁ := gamma_skew_last (I := I) N hmc i j k
  have hsym₁ := gamma_symm_first (I := I) N htor i k j
  have hsk₂ := gamma_skew_last (I := I) N hmc k i j
  have hsym₂ := gamma_symm_first (I := I) N htor k j i
  have hsk₃ := gamma_skew_last (I := I) N hmc j k i
  have hsym₃ := gamma_symm_first (I := I) N htor j i k
  linarith

/-- Existing normal-frame predicate recovered from the first-order metric
normal form. -/
theorem isNormalFrame
    {g : SmoothRiemannianMetric I M} {x : M}
    (N : MetricNormalFormAt (I := I) (Idx := Idx) g x)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (htor : ∀ i j : Idx, cov.torsion x (N.frame i x) (N.frame j x) = 0) :
    IsNormalFrameForConnectionAt cov N.frame N.hframe x := by
  intro i j k
  exact N.gamma_eq_zero hmc htor i j k

end MetricNormalFormAt

/-- Frontier: the elementary quadratic coordinate-change construction should
produce a first-order metric-normal coordinate frame at every point.

This is intentionally not the geodesic normal-coordinate theorem.  It is the
algebraic snapshot normal form from an arbitrary local coordinate chart. -/
theorem exists_metricNormal
    [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (x : M) :
    Nonempty (MetricNormalFormAt (I := I)
      (Idx := CoordinateIdx (𝕜 := Real) E) g x) := by
  sorry

end Coordinates
end RicciFlower

