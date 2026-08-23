import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.SpatialCommutator
open DifferentialGeometry.PDE.RicciFlow

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

def rmGammaCost (d k : ℕ) : Real :=
  (d : Real) ^ 2 * (12 + 3 * k)

theorem commStarCost_nonneg (d k : ℕ) :
    0 ≤ commStarCost d k := by
  unfold commStarCost
  positivity

theorem rmGammaCost_nonneg (d k : ℕ) :
    0 ≤ rmGammaCost d k := by
  unfold rmGammaCost
  positivity

def rmResidualCost (d : ℕ) : ℕ → Real
  | 0 => 12 * (d : Real) ^ 2
  | k + 1 =>
      2 * rmResidualCost d k + commStarCost d k + rmGammaCost d k

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
