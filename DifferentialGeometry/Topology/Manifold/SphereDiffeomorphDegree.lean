import DifferentialGeometry.Topology.Manifold.SphereOrientationIsotopy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable (f : Diffeomorph (𝓡 2) (𝓡 2)
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)

private abbrev uniqueSphereFiber (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Unique {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 // f x = y} where
  default := ⟨f.symm y, f.apply_symm_apply y⟩
  uniq := by
    intro x
    apply Subtype.ext
    exact f.injective (x.2.trans (f.apply_symm_apply y).symm)

def sphereDiffeomorphPreimageCount (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : ℤ := by
  classical
  let := uniqueSphereFiber f y
  exact ∑ x : {x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 // f x = y},
    if 0 < (fderiv ℝ (sphereRadialExtension f) (x.1 : EuclideanSpace ℝ (Fin 3))).toLinearMap.det
    then 1 else
    if (fderiv ℝ (sphereRadialExtension f) (x.1 : EuclideanSpace ℝ (Fin 3))).toLinearMap.det < 0
    then -1 else 0

theorem sphereDiffeomorphPreimageCount_eq
    (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphPreimageCount f y =
      if 0 < (fderiv ℝ (sphereRadialExtension f)
        (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then 1 else -1 := by
  classical
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let := uniqueSphereFiber f y
  have hnz := det_fderiv_sphereRadialExtension_ne_zero f (ne_zero_of_mem_unit_sphere (f.symm y))
  simp only [sphereDiffeomorphPreimageCount, Fintype.sum_unique]
  change (if 0 < (fderiv ℝ (sphereRadialExtension f)
    (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then (1 : ℤ) else
    if (fderiv ℝ (sphereRadialExtension f)
    (f.symm y : EuclideanSpace ℝ (Fin 3))).toLinearMap.det < 0 then -1 else 0) = _
  split_ifs with hp hn
  · rfl
  · rfl
  · exact False.elim (hnz (le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)))

theorem sphereDiffeomorphPreimageCount_independent
    (y z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphPreimageCount f y = sphereDiffeomorphPreimageCount f z := by
  classical
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hsign := det_fderiv_sphereRadialExtension_pos_iff hrank f
    (ne_zero_of_mem_unit_sphere (f.symm y)) (ne_zero_of_mem_unit_sphere (f.symm z))
  simp only [sphereDiffeomorphPreimageCount_eq, hsign]

def sphereDiffeomorphDegree : ℤ :=
  sphereDiffeomorphPreimageCount f ⟨EuclideanSpace.single 0 1, by simp⟩

theorem sphereDiffeomorphDegree_eq_sign
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphDegree f =
      if 0 < (fderiv ℝ (sphereRadialExtension f)
        (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det then 1 else -1 := by
  classical
  unfold sphereDiffeomorphDegree
  rw [sphereDiffeomorphPreimageCount_independent f _ (f v), sphereDiffeomorphPreimageCount_eq,
    f.symm_apply_apply]

theorem sphereDiffeomorphDegree_eq_one_iff
    (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereDiffeomorphDegree f = 1 ↔
      0 < (fderiv ℝ (sphereRadialExtension f) (v : EuclideanSpace ℝ (Fin 3))).toLinearMap.det := by
  classical
  rw [sphereDiffeomorphDegree_eq_sign f v]
  split_ifs <;> simp_all

theorem sphereDiffeomorphDegree_eq_one_iff_isotopy :
    sphereDiffeomorphDegree f = 1 ↔
    ∃ J : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
        (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞,
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 2)) (𝓡 2) ∞
        (fun q : ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (J q.1).symm q.2) ∧
      J 0 = f ∧ J 1 = Diffeomorph.refl (𝓡 2) _ ∞ := by
  let v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  exact (sphereDiffeomorphDegree_eq_one_iff f v).trans
    (sphere_isotopy_iff_positive_radial_derivative f v).symm

end DifferentialGeometry.Topology.Manifold
