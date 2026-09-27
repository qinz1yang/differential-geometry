import DifferentialGeometry.Topology.Homology.Local.Chart
import DifferentialGeometry.Topology.Homology.SphereEuler
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric ContinuousMap
namespace DifferentialGeometry.Homology

def puncturedSpaceSphereHomotopyEquiv (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ({0}ᶜ : Set E) ≃ₕ sphere (0 : E) 1 := by
  let := (convex_Ioi (0 : ℝ)).contractibleSpace (show (Ioi (0 : ℝ)).Nonempty from ⟨(1 : ℝ), by norm_num⟩)
  let e := Classical.choice (ContractibleSpace.hequiv_unit (Ioi (0 : ℝ)))
  exact (homeomorphUnitSphereProd E).toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl _).prodCongr e).trans
      (Homeomorph.prodUnique (sphere (0 : E) 1) Unit).toHomotopyEquiv)


theorem puncturedSpaceSphereHomotopyEquiv_apply (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (x : ({0}ᶜ : Set E)) :
    ((puncturedSpaceSphereHomotopyEquiv E) x : E) = ‖x.val‖⁻¹ • x.val := by
  change ((homeomorphUnitSphereProd E x).1 : E) = _
  exact homeomorphUnitSphereProd_apply_fst_coe E x

variable (k : Type) [Field k]


theorem finiteHomologyType_puncturedEuclidean (n : ℕ) :
    finiteHomologyType k
      (TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
  (finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (Y := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (puncturedSpaceSphereHomotopyEquiv _)).mpr (finiteHomologyType_euclideanSphere k n)


theorem eulerChar_puncturedEuclidean (n : ℕ) :
    eulerChar k (TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1))))) =
      1 + (-1 : ℤ) ^ n :=
  (eulerChar_eq_of_homotopyEquiv k
    (X := TopCat.of ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (Y := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (puncturedSpaceSphereHomotopyEquiv _)).trans (eulerChar_euclideanSphere k n)


theorem finiteHomologyType_localEuclidean (n : ℕ) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) (ModuleCat.of k k)) := by
  apply finiteHomologyType_relativeChainComplex
  · cases n with
    | zero => exact finiteHomologyType_of_subsingleton k
    | succ n => exact finiteHomologyType_puncturedEuclidean k n
  · exact finiteHomologyType_of_contractible k


theorem relativeEulerChar_localEuclidean (n : ℕ) :
    relativeEulerChar (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) k = (-1 : ℤ) ^ n := by
  cases n with
  | zero =>
    have : IsEmpty ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) :=
      ⟨fun x => x.property (Subsingleton.elim x.val 0)⟩
    rw [relativeEulerChar_eq_sub (TopCat.of (EuclideanSpace ℝ (Fin 0)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) k (finiteHomologyType_of_subsingleton k)
      (finiteHomologyType_of_contractible k), eulerChar_of_contractible,
      eulerChar_of_isEmpty, pow_zero, sub_zero]
  | succ n =>
    rw [relativeEulerChar_eq_sub (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) k (finiteHomologyType_puncturedEuclidean k n)
      (finiteHomologyType_of_contractible k), eulerChar_of_contractible,
      eulerChar_puncturedEuclidean, pow_succ]
    ring


theorem finiteHomologyType_localEuclidean_at (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n))) (ModuleCat.of k k)) := by
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have h := finiteHomologyType_chart_iff
    (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e p (mem_univ p) k
  have he : e p = 0 := sub_self p
  rw [he] at h
  exact h.mpr (finiteHomologyType_localEuclidean k n)


theorem relativeEulerChar_localEuclidean_at (n : ℕ) (p : EuclideanSpace ℝ (Fin n)) :
    relativeEulerChar (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n))) k = (-1 : ℤ) ^ n := by
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have h := relativeEulerChar_chart
    (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e p (mem_univ p) k
  have he : e p = 0 := sub_self p
  rw [h, he]
  exact relativeEulerChar_localEuclidean k n

end DifferentialGeometry.Homology
