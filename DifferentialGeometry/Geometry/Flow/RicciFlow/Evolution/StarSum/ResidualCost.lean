import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TimeRecursion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.ResidualLedger
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton

set_option autoImplicit false

/-!
# Arbitrary-dimensional curvature-residual costs

Explicit constructor-tree costs for the direct curvature-tower producer.  The
definitions generalize the checked dimension-three recurrence without claiming
that the corresponding arbitrary-dimensional residual theorem is already
proved.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators

/-- Direct reaction coefficient obtained from the whole residual estimate. -/
def rmTowerCost (d k : ℕ) : Real :=
  2 * Real.sqrt (Fintype.card (Fin (4 + k) -> Fin d) : Real) *
    (((4 + k : Nat) : Real) * (d : Real) ^ 2 + rmResidualCost d k)

/-- The direct tower reaction coefficient is nonnegative. -/
theorem rmTowerCost_nonneg (d k : ℕ) :
    0 ≤ rmTowerCost d k := by
  have hres := rmResidualCost_nonneg d k
  unfold rmTowerCost
  positivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

set_option backward.isDefEq.respectTransparency false in
/-- The level-zero curvature reaction has the same explicit constructor cost
for every finite orthonormal-frame index type. -/
theorem e0Field_cost_any {Idx : Type*} [Fintype Idx]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    StarSum2Cost (I := I) Idx S t 0 (e0Field (I := I) S t)
      (12 * (Fintype.card Idx : Real) ^ 2) := by
  unfold e0Field
  convert StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
    (StarSum2Cost.add (StarSum2Cost.add (StarSum2Cost.add
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 btPermE))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt2)))
      (StarSum2Cost.smul (-2) (StarSum2Cost.base 0 0 0 0 σBt3)))
      (StarSum2Cost.smul 2 (StarSum2Cost.base 0 0 0 0 σBt4)))
      (StarSum2Cost.base 0 0 0 0 σD1))
      (StarSum2Cost.base 0 0 0 0 σD2))
      (StarSum2Cost.base 0 0 0 0 σD3))
      (StarSum2Cost.base 0 0 0 0 σD4) using 1
  norm_num
  ring

/-- Compatibility alias for the canonical Hamilton reaction encoded by the
eight generators of `e0Field`. -/
def rmBaseReact {Idx : Type*} [Fintype Idx]
    (R : (Fin 4 -> Idx) -> Real) (m : Fin 4 -> Idx) : Real :=
  DifferentialGeometry.Integral.Connection.hamiltonRmReact R m

set_option backward.isDefEq.respectTransparency false in
/-- In every finite orthonormal frame, `e0Field` realizes the explicit
arbitrary-dimensional quadratic curvature reaction. -/
theorem e0Field_comp_any {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    [InnerProductSpace Real E]
    (S : SolutionOn (I := I) (M := M) D) (t : Real) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j : Idx,
      (S.family.metric t).inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0)
    (m : Fin 4 -> Idx) :
    e0Field (I := I) S t x (fun p => basis (m p)) =
      rmBaseReact
        (fun q => nablaKRm04Field (I := I) S t 0 x (fun p => basis (q p))) m := by
  have hev :
      e0Field (I := I) S t x (fun p => basis (m p)) =
        -2 * starBaseField (I := I) S t 0 0 0 0 btPermE x (fun p => basis (m p))
          + 2 * starBaseField (I := I) S t 0 0 0 0 σBt2 x (fun p => basis (m p))
          + -2 * starBaseField (I := I) S t 0 0 0 0 σBt3 x (fun p => basis (m p))
          + 2 * starBaseField (I := I) S t 0 0 0 0 σBt4 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD1 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD2 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD3 x (fun p => basis (m p))
          + starBaseField (I := I) S t 0 0 0 0 σD4 x (fun p => basis (m p)) := rfl
  rw [hev, btStar_eq (I := I) S t basis horth m,
    btStar2 (I := I) S t basis horth m, btStar3 (I := I) S t basis horth m,
    btStar4 (I := I) S t basis horth m, drStar1 (I := I) S t basis horth m,
    drStar2 (I := I) S t basis horth m, drStar3 (I := I) S t basis horth m,
    drStar4 (I := I) S t basis horth m]
  rfl

/-- The generic gamma cost specializes to the checked dimension-three cost. -/
theorem rmGammaCost_three (k : ℕ) :
    rmGammaCost 3 k = gammaStarCost k := by
  norm_num [rmGammaCost, gammaStarCost]

/-- The generic residual ledger specializes exactly to the checked
dimension-three constructor ledger. -/
theorem rmResidualCost_three (k : ℕ) :
    rmResidualCost 3 k = resStarCost k := by
  induction k with
  | zero => norm_num [rmResidualCost, resStarCost]
  | succ k ih =>
      simp only [rmResidualCost, resStarCost]
      rw [ih, rmGammaCost_three]

end DifferentialGeometry.PDE.RicciFlow
