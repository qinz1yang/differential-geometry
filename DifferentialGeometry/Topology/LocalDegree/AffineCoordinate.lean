import DifferentialGeometry.Topology.LocalDegree.LinearSphere
import DifferentialGeometry.Topology.LocalDegree.SphereMapParameter
import DifferentialGeometry.Topology.LocalDegree.Euclidean

set_option autoImplicit false
open Filter Metric Set
open scoped Topology
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem normalize_pos_smul (z : E) {a : ℝ} (ha : 0 < a) :
    ‖a • z‖⁻¹ • (a • z) = ‖z‖⁻¹ • z := by
  rw [norm_smul, Real.norm_of_nonneg ha.le, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

theorem exists_affineCoordinate_closedBall (A : E ≃L[ℝ] F) (x : E) (y : F)
    {S : ℝ} (hS : 0 < S) :
    ∃ R > 0, MapsTo (fun z => y + A (z - x)) (closedBall x R) (closedBall y S) := by
  have hc : Continuous (fun z : E => y + A (z - x)) :=
    continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))
  have hn : (fun z => y + A (z - x)) ⁻¹' ball y S ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds y hS)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z hz
  exact ball_subset_closedBall (hball (closedBall_subset_ball (by linarith) hz))

private theorem affineRadius_mem (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : MapsTo (fun z => y + A (z - x)) (closedBall x R) (closedBall y S))
    (r : Ioc (0 : ℝ) R) (v : sphere (0 : E) 1) : (r : ℝ) * ‖A v‖ ∈ Ioc (0 : ℝ) S := by
    have hv : (v : E) ≠ 0 := by
      intro he
      have hn := norm_eq_of_mem_sphere v
      rw [he, norm_zero] at hn
      exact zero_ne_one hn
    refine ⟨mul_pos r.property.1 (norm_pos_iff.mpr (mt A.map_eq_zero_iff.mp hv)), ?_⟩
    have hmem : x + (r : ℝ) • (v : E) ∈ closedBall x R := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]
      exact r.property.2
    have hh := hball hmem
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, map_smul,
      norm_smul, Real.norm_of_nonneg r.property.1.le] using hh

private def affineRadius (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : MapsTo (fun z => y + A (z - x)) (closedBall x R) (closedBall y S))
    (r : Ioc (0 : ℝ) R) : C(sphere (0 : E) 1, Ioc (0 : ℝ) S) where
  toFun v := ⟨(r : ℝ) * ‖A v‖, affineRadius_mem A x y hball r v⟩
  continuous_toFun := (continuous_const.mul
    (A.continuous.comp continuous_subtype_val).norm).subtype_mk _

private theorem affineRadius_direction (A : E ≃L[ℝ] F) (x : E) (y : F) {R S : ℝ}
    (hball : MapsTo (fun z => y + A (z - x)) (closedBall x R) (closedBall y S))
    (r : Ioc (0 : ℝ) R) (v : sphere (0 : E) 1) :
    (affineRadius A x y hball r v : ℝ) • (linearSphereMap A v : F) =
      A ((r : ℝ) • (v : E)) := by
  have hn : ‖A v‖ ≠ 0 := by
    have hp := (affineRadius A x y hball r v).property.1
    change 0 < (r : ℝ) * ‖A v‖ at hp
    intro hh
    rw [hh, mul_zero] at hp
    exact lt_irrefl 0 hp
  change ((r : ℝ) * ‖A v‖) • (linearSphereMap A v : F) = _
  rw [linearSphereMap_apply, map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]

theorem sphereMap_affineCoordinate_homotopy (A : E ≃L[ℝ] F) (x : E) (y : F)
    {V : F → F} {R S : ℝ} (hS : 0 < S)
    (hV : ContinuousOn V (closedBall y S))
    (hz : ∀ z ∈ closedBall y S, z ≠ y → V z ≠ 0)
    (hball : MapsTo (fun z => y + A (z - x)) (closedBall x R) (closedBall y S))
    (hP : ContinuousOn (fun z => A.symm (V (y + A (z - x)))) (closedBall x R))
    (hPz : ∀ z ∈ closedBall x R, z ≠ x → A.symm (V (y + A (z - x))) ≠ 0)
    (r : Ioc (0 : ℝ) R) :
    Nonempty ((sphereMap (fun z => A.symm (V (y + A (z - x)))) x R hP hPz r).Homotopy
      ((linearSphereMap A.symm).comp
        ((sphereMap V y S hV hz ⟨S, hS, le_rfl⟩).comp (linearSphereMap A)))) := by
  let rv := affineRadius A x y hball r
  let H := sphereMapParameterHomotopy V y S hV hz rv
    (ContinuousMap.const _ ⟨S, hS, le_rfl⟩) (linearSphereMap A)
  have heq : (linearSphereMap A.symm).comp
      (sphereMapParameter V y S hV hz rv (linearSphereMap A)) =
      sphereMap (fun z => A.symm (V (y + A (z - x)))) x R hP hPz r := by
    apply ContinuousMap.ext
    intro v
    apply Subtype.ext
    have harg : y + (rv v : ℝ) • (linearSphereMap A v : F) =
        y + A ((r : ℝ) • (v : E)) := by
      rw [affineRadius_direction]
    have hnorm : 0 < ‖V (y + A ((r : ℝ) • (v : E)))‖ := by
      have hh := (sphereMapParameter V y S hV hz rv (linearSphereMap A) v).property
      rw [mem_sphere, dist_zero_right] at hh
      by_contra hn
      have he : V (y + A ((r : ℝ) • (v : E))) = 0 :=
        norm_eq_zero.mp (le_antisymm (le_of_not_gt hn) (norm_nonneg _))
      have he' : (sphereMapParameter V y S hV hz rv (linearSphereMap A) v : F) = 0 := by
        rw [sphereMapParameter_apply, harg, he, smul_zero]
      rw [he', norm_zero] at hh
      exact zero_ne_one hh
    rw [ContinuousMap.comp_apply, linearSphereMap_apply, sphereMapParameter_apply, harg]
    simp only [map_smul, sphereMap_apply, add_sub_cancel_left]
    simpa only [map_smul] using
      normalize_pos_smul (A.symm (V (y + A ((r : ℝ) • (v : E))))) (inv_pos.mpr hnorm)
  exact ⟨((ContinuousMap.Homotopy.refl (linearSphereMap A.symm)).comp H).cast heq
    (by rw [sphereMapParameter_const])⟩

theorem isolatedZero_affineCoordinate (A : E ≃L[ℝ] F) (x : E) (y : F)
    {V : F → F} (hV : isolatedZero V y) :
    isolatedZero (fun z => A.symm (V (y + A (z - x)))) x := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨R, hR, hball⟩ := exists_affineCoordinate_closedBall A x y hS.pos
  refine ⟨R, hR, ?_, ?_⟩
  · exact A.symm.continuous.comp_continuousOn (hS.continuousOn.comp
      (continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))).continuousOn
      hball)
  · intro z hz
    rw [A.symm.map_eq_zero_iff, hS.zero_iff _ (hball hz)]
    simp only [add_eq_left, A.map_eq_zero_iff, sub_eq_zero]

variable {d : ℕ}


theorem euclideanSphereDegree_linear_inverse
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A.symm) *
      euclideanSphereDegree (linearSphereMap A) = 1 := by
  rw [← euclideanSphereDegree_comp]
  have he : (linearSphereMap A.symm).comp (linearSphereMap A) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    exact linearSphereMap_symm_apply A
  rw [he, euclideanSphereDegree_id]

theorem euclideanLocalDegree_affineCoordinate
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)))
    (x y : EuclideanSpace ℝ (Fin (d + 1)))
    {V : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hV : isolatedZero V y) :
    euclideanLocalDegree (fun z => A.symm (V (y + A (z - x)))) x
        (isolatedZero_affineCoordinate A x y hV) = euclideanLocalDegree V y hV := by
  obtain ⟨S, hS⟩ := hV
  obtain ⟨R, hR, hball⟩ := exists_affineCoordinate_closedBall A x y hS.pos
  have hP : IsolatingRadius (fun z => A.symm (V (y + A (z - x)))) x R := by
    refine ⟨hR, ?_, ?_⟩
    · exact A.symm.continuous.comp_continuousOn (hS.continuousOn.comp
        (continuous_const.add (A.continuous.comp (continuous_id.sub continuous_const))).continuousOn
        hball)
    · intro z hz
      rw [A.symm.map_eq_zero_iff, hS.zero_iff _ (hball hz)]
      simp only [add_eq_left, A.map_eq_zero_iff, sub_eq_zero]
  erw [euclideanLocalDegree_eq_sphereDegree _ hP ⟨R, hR, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree _ hS ⟨S, hS.pos, le_rfl⟩]
  obtain ⟨H⟩ := sphereMap_affineCoordinate_homotopy A x y hS.pos hS.continuousOn
    hS.nonzero hball hP.continuousOn hP.nonzero ⟨R, hR, le_rfl⟩
  rw [euclideanSphereDegree_eq_of_homotopy H, euclideanSphereDegree_comp,
    euclideanSphereDegree_comp]
  have hi := euclideanSphereDegree_linear_inverse A
  calc
    _ = (euclideanSphereDegree (linearSphereMap A.symm) *
        euclideanSphereDegree (linearSphereMap A)) *
        euclideanSphereDegree (sphereMap V y S hS.continuousOn hS.nonzero ⟨S, hS.pos, le_rfl⟩) :=
      by ring
    _ = _ := by rw [hi, one_mul]

end Poincare.LocalDegree
