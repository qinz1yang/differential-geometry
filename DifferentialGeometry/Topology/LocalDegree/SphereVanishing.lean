import DifferentialGeometry.Topology.LocalDegree.SphereHomology
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Metric
noncomputable section
namespace Poincare.LocalDegree
open Poincare.Homology
variable {k : Type} [Ring k] (R : ModuleCat k)

private theorem pathConnected_euclideanSphere (d : ℕ) :
    PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (d + 2))) 1) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · exact Module.one_lt_rank_of_one_lt_finrank (by simp)
  · norm_num

theorem isZero_euclideanSphere_reducedHomology (d n : ℕ) (h : n ≠ d) :
    IsZero (reducedSingularHomology R
      (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)) n) := by
  induction d generalizing n with
  | zero =>
    cases n with
    | zero => exact (h rfl).elim
    | succ n => exact isZero_euclideanZeroSphere_reducedHomology_succ R n
  | succ d ih =>
    cases n with
    | zero =>
      let := pathConnected_euclideanSphere d
      exact isZero_reducedSingularHomology_zero_of_pathConnected R _
    | succ n =>
      exact IsZero.of_iso (ih n (by omega))
        (euclideanSphereReducedHomologySuccIso R (d + 1) n)

end Poincare.LocalDegree
