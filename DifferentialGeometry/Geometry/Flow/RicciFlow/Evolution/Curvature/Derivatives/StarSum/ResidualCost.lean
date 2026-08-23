import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.TimeRecursion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.ResidualDecomposition
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Hamilton
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped Manifold ContDiff BigOperators

def rmTowerCost (d k : ℕ) : Real :=
  2 * Real.sqrt (Fintype.card (Fin (4 + k) -> Fin d) : Real) *
    (((4 + k : Nat) : Real) * (d : Real) ^ 2 + rmResidualCost d k)

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
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless]
  [SigmaCompactSpace M] in
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

def rmBaseReact {Idx : Type*} [Fintype Idx]
    (R : (Fin 4 -> Idx) -> Real) (m : Fin 4 -> Idx) : Real :=
  DifferentialGeometry.Geometry.Connection.hamiltonRmReact R m

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem e0Field_comp_any {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
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

theorem rmGammaCost_three (k : ℕ) :
    rmGammaCost 3 k = gammaStarCost k := by
  norm_num [rmGammaCost, gammaStarCost]

theorem rmResidualCost_three (k : ℕ) :
    rmResidualCost 3 k = resStarCost k := by
  induction k with
  | zero => norm_num [rmResidualCost, resStarCost]
  | succ k ih =>
      simp only [rmResidualCost, resStarCost]
      rw [ih, rmGammaCost_three]

end DifferentialGeometry.PDE.RicciFlow
