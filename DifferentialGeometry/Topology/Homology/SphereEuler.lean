import DifferentialGeometry.Topology.Homology.OpenCover
import DifferentialGeometry.Topology.LocalDegree.SphereCover

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Metric
open DifferentialGeometry.LocalDegree
noncomputable section
namespace DifferentialGeometry.Homology
variable (k : Type) [Field k]

private theorem sphereCover_finite_euler (n : ℕ)
    (hi : finiteHomologyType k (TopCat.of (poleIntersection (euclideanNorth n)))) :
    finiteHomologyType k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ∧
      eulerChar k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
        2 - eulerChar k (TopCat.of (poleIntersection (euclideanNorth n))) := by
  let X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  let v := euclideanNorth n
  let s : Set X := poleComplement v
  let t : Set X := poleComplement (-v)
  let := contractibleSpace_poleComplement v
  let := contractibleSpace_poleComplement (-v)
  have hs : IsOpen s := (poleComplement v).isOpen
  have ht : IsOpen t := (poleComplement (-v)).isOpen
  have hcover : s ∪ t = Set.univ :=
    congrArg (fun U : TopologicalSpace.Opens X => (U : Set X)) (poleComplement_sup v)
  have hfs : finiteHomologyType k (TopCat.of s) := finiteHomologyType_of_contractible k
  have hft : finiteHomologyType k (TopCat.of t) := finiteHomologyType_of_contractible k
  refine ⟨finiteHomologyType_of_openCover X s t k hs ht hcover hfs hft hi, ?_⟩
  have he := eulerChar_openCover X s t k hs ht hcover hfs hft hi
  rw [eulerChar_of_contractible k (X := TopCat.of s),
    eulerChar_of_contractible k (X := TopCat.of t)] at he
  exact he

private theorem sphere_finite_euler (n : ℕ) :
    finiteHomologyType k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ∧
      eulerChar k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
        1 + (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
    let := isEmpty_euclideanZeroSphereIntersection
    have h := sphereCover_finite_euler k 0 (finiteHomologyType_of_subsingleton k)
    exact ⟨h.1, by simpa only [eulerChar_of_isEmpty, sub_zero, pow_zero, Int.reduceAdd] using h.2⟩
  | succ n hn =>
    let A := TopCat.of (poleIntersection (euclideanNorth (n + 1)))
    let B := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    let e : ContinuousMap.HomotopyEquiv A B := euclideanPoleIntersectionHomotopyEquiv (n + 1)
    have hi := (finiteHomologyType_iff_of_homotopyEquiv k (X := A) (Y := B) e).mpr hn.1
    have h := sphereCover_finite_euler k (n + 1) hi
    refine ⟨h.1, ?_⟩
    rw [h.2, eulerChar_eq_of_homotopyEquiv k (X := A) (Y := B) e, hn.2, pow_succ]
    ring

theorem finiteHomologyType_euclideanSphere (n : ℕ) :
    finiteHomologyType k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  (sphere_finite_euler k n).1


theorem eulerChar_euclideanSphere (n : ℕ) :
    eulerChar k (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) =
      1 + (-1 : ℤ) ^ n :=
  (sphere_finite_euler k n).2

end DifferentialGeometry.Homology
