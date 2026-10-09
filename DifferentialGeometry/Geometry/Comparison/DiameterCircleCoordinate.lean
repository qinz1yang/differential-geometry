import DifferentialGeometry.Geometry.Comparison.DiameterSegment
import DifferentialGeometry.Topology.MetricSpace.CircleDistance

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

noncomputable def diameterCircleCoordinate {D : ℝ} (hD : 0 < D)
    (σ : Icc (0 : ℝ) D → X) (x : X) : AddCircle (2 * D) := by
  classical
  exact if x ∈ range σ then ((dist x (σ ⟨0, le_rfl, hD.le⟩) : ℝ) : AddCircle (2 * D))
    else ((-dist x (σ ⟨0, le_rfl, hD.le⟩) : ℝ) : AddCircle (2 * D))

theorem diameterCircleCoordinate_apply_isometry {D : ℝ} (hD : 0 < D)
    {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ) (t : Icc (0 : ℝ) D) :
    diameterCircleCoordinate hD σ (σ t) = ((t : ℝ) : AddCircle (2 * D)) := by
  rw [diameterCircleCoordinate, ite_eq_left (mem_range_self t)]
  have hd : dist (σ t) (σ ⟨0, le_rfl, hD.le⟩) = (t : ℝ) := by
    rw [hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  rw [hd]

theorem isometry_diameterCircleCoordinate
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 < D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D) : Isometry (diameterCircleCoordinate hD σ) := by
  classical
  let p := σ ⟨0, le_rfl, hD.le⟩
  let q := σ ⟨D, hD.le, le_rfl⟩
  have h2D : 0 < 2 * D := by linarith
  have hmixed (x : X) (hx : x ∉ range σ) (t : Icc (0 : ℝ) D) :
      dist (diameterCircleCoordinate hD σ (σ t)) (diameterCircleCoordinate hD σ x) =
        dist (σ t) x := by
    have hsum := dist_add_dist_eq_of_outside_diameter_segment hsegments hD.le hσ ho hdiam hx
    change dist x p + dist x q = D at hsum
    have harg : (t : ℝ) + dist x p ∈ Icc (0 : ℝ) (2 * D) := by
      constructor
      · exact add_nonneg t.property.1 dist_nonneg
      · linarith [t.property.2, hdiam x p]
    rw [diameterCircleCoordinate_apply_isometry hD hσ, diameterCircleCoordinate,
      ite_eq_right hx, dist_eq_norm, ← AddCircle.coe_sub, sub_neg_eq_add,
      AddCircle.norm_coe_eq_min_of_mem_Icc h2D harg,
      dist_comm (σ t) x, dist_to_segment_of_not_mem_range hsegments hD.le hσ ho hx t]
    change min ((t : ℝ) + dist x p) (2 * D - ((t : ℝ) + dist x p)) =
      min (dist x p + (t : ℝ)) (dist x q + (D - (t : ℝ)))
    congr 1 <;> linarith
  apply Isometry.of_dist_eq
  intro x y
  by_cases hx : x ∈ range σ
  · obtain ⟨s, rfl⟩ := hx
    by_cases hy : y ∈ range σ
    · obtain ⟨t, rfl⟩ := hy
      rw [diameterCircleCoordinate_apply_isometry hD hσ,
        diameterCircleCoordinate_apply_isometry hD hσ, hσ.dist_eq]
      apply AddCircle.dist_coe_eq_abs_of_le_half_period h2D
      rw [show 2 * D / 2 = D by ring]
      exact abs_le.mpr ⟨by linarith [s.property.1, t.property.2],
        by linarith [s.property.2, t.property.1]⟩
    · exact hmixed y hy s
  · by_cases hy : y ∈ range σ
    · obtain ⟨t, rfl⟩ := hy
      simpa only [dist_comm] using hmixed x hx t
    · have hbound : |(-dist x p) - (-dist y p)| ≤ (2 * D) / 2 := by
        rw [show 2 * D / 2 = D by ring]
        apply abs_le.mpr
        constructor <;> linarith [hdiam x p, hdiam y p,
          dist_nonneg (x := x) (y := p), dist_nonneg (x := y) (y := p)]
      rw [diameterCircleCoordinate, ite_eq_right hx, diameterCircleCoordinate, ite_eq_right hy,
        AddCircle.dist_coe_eq_abs_of_le_half_period h2D hbound, neg_sub_neg, abs_sub_comm]
      exact (dist_eq_abs_sub_of_outside_diameter_segment hκ hcomp hsegments hD.le hσ ho hdiam hx hy).symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
