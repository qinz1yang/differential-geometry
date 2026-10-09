import DifferentialGeometry.Topology.MetricSpace.RayExteriorDistance
import DifferentialGeometry.Geometry.Comparison.CommonOpposite

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

noncomputable def raySignedDistance (γ : Ici (0 : ℝ) → X) (x : X) : ℝ := by
  classical
  exact if x ∈ range γ then dist x (γ ⟨0, by simp⟩) else -dist x (γ ⟨0, by simp⟩)

theorem raySignedDistance_apply_isometry {γ : Ici (0 : ℝ) → X}
    (hγ : Isometry γ) (t : Ici (0 : ℝ)) : raySignedDistance γ (γ t) = t := by
  rw [raySignedDistance, ite_eq_left (mem_range_self t), hγ.dist_eq]
  change |(t : ℝ) - 0| = (t : ℝ)
  rw [sub_zero, abs_of_nonneg t.property]

theorem isometry_raySignedDistance {κ : ℝ} (hκ : 0 ≤ κ)
    (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hopen : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      IsOpen (σ '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}))
    {γ : Ici (0 : ℝ) → X} (hγ : Isometry γ) : Isometry (raySignedDistance γ) := by
  classical
  apply Isometry.of_dist_eq
  intro x y
  by_cases hx : x ∈ range γ
  · obtain ⟨s, rfl⟩ := hx
    by_cases hy : y ∈ range γ
    · obtain ⟨t, rfl⟩ := hy
      rw [raySignedDistance_apply_isometry hγ, raySignedDistance_apply_isometry hγ,
        hγ.dist_eq]
      rfl
    · rw [raySignedDistance_apply_isometry hγ, raySignedDistance, ite_eq_right hy,
        Real.dist_eq, sub_neg_eq_add, abs_of_nonneg (add_nonneg s.property dist_nonneg),
        dist_comm (γ s) y, dist_to_isometric_ray_of_not_mem_range hsegments hopen hγ hy s]
      ring
  · by_cases hy : y ∈ range γ
    · obtain ⟨t, rfl⟩ := hy
      rw [raySignedDistance_apply_isometry hγ, raySignedDistance, ite_eq_right hx,
        Real.dist_eq, show -dist x (γ ⟨0, by simp⟩) - (t : ℝ) =
          -(dist x (γ ⟨0, by simp⟩) + (t : ℝ)) by ring, abs_neg,
        abs_of_nonneg (add_nonneg dist_nonneg t.property),
        dist_to_isometric_ray_of_not_mem_range hsegments hopen hγ hx t]
    · let p := γ ⟨0, by simp⟩
      let z := γ ⟨1, by norm_num⟩
      have hzp : z ≠ p := by
        intro h
        have he := congrArg (fun t : Ici (0 : ℝ) => (t : ℝ)) (hγ.injective h)
        norm_num [z, p] at he
      have hpz : dist p z = 1 := by
        dsimp [p, z]
        rw [hγ.dist_eq]
        norm_num [Subtype.dist_eq, Real.dist_eq]
      have hxz : dist x z = dist x p + dist p z := by
        rw [hpz]
        exact dist_to_isometric_ray_of_not_mem_range hsegments hopen hγ hx ⟨1, by norm_num⟩
      have hyz : dist y z = dist y p + dist p z := by
        rw [hpz]
        exact dist_to_isometric_ray_of_not_mem_range hsegments hopen hγ hy ⟨1, by norm_num⟩
      have hd := dist_eq_abs_sub_of_common_opposite hκ hcomp
        (mem_univ p) (mem_univ x) (mem_univ y) (mem_univ z) hzp hxz hyz
      rw [raySignedDistance, ite_eq_right hx, raySignedDistance, ite_eq_right hy, Real.dist_eq]
      change |-dist x p - -dist y p| = dist x y
      rw [neg_sub_neg, abs_sub_comm]
      exact hd.symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
