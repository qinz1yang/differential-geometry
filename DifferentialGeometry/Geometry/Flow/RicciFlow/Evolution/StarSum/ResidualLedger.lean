import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SpatialMember

set_option autoImplicit false

/-!
# Arbitrary-dimensional curvature-residual ledger

This file records the constructor-tree costs used by the direct curvature-tower
recursion.  It sits below the time-recursion proof so the generic successor can
state its exact cost without creating an import cycle.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

/-- Cost of the Christoffel-time correction at level `k` in dimension `d`. -/
def rmGammaCost (d k : ℕ) : Real :=
  (d : Real) ^ 2 * (12 + 3 * k)

/-- The generic spatial-commutator cost is nonnegative. -/
theorem commStarCost_nonneg (d k : ℕ) :
    0 ≤ commStarCost d k := by
  unfold commStarCost
  positivity

/-- The Christoffel-time correction cost is nonnegative. -/
theorem rmGammaCost_nonneg (d k : ℕ) :
    0 ≤ rmGammaCost d k := by
  unfold rmGammaCost
  positivity

/-- Explicit constructor-tree cost of the curvature heat residual.

The base has twelve double-trace quadratic terms.  A successor combines the
two differentiated daughters, the spatial commutator, and the Christoffel-time
correction. -/
def rmResidualCost (d : ℕ) : ℕ → Real
  | 0 => 12 * (d : Real) ^ 2
  | k + 1 =>
      2 * rmResidualCost d k + commStarCost d k + rmGammaCost d k

/-- The curvature-residual constructor cost is nonnegative. -/
theorem rmResidualCost_nonneg (d k : ℕ) :
    0 ≤ rmResidualCost d k := by
  induction k with
  | zero =>
      simp only [rmResidualCost]
      positivity
  | succ k ih =>
      simp only [rmResidualCost]
      have hcomm := commStarCost_nonneg d k
      have hgamma := rmGammaCost_nonneg d k
      positivity

end DifferentialGeometry.PDE.RicciFlow
