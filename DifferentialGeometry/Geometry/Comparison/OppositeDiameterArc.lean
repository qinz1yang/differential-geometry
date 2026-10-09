import DifferentialGeometry.Geometry.Comparison.DiameterSegment
import DifferentialGeometry.Topology.MetricSpace.OppositeSegment
import DifferentialGeometry.Topology.MetricSpace.SegmentThroughPoint

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem mem_range_or_mem_range_of_opposite_diameter_arcs
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ τ : Icc (0 : ℝ) D → X} (hσ : Isometry σ) (hτ : Isometry τ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D)
    (hzero : τ ⟨0, le_rfl, hD⟩ = σ ⟨0, le_rfl, hD⟩)
    (hout : ∀ t : Icc (0 : ℝ) D, 0 < (t : ℝ) → (t : ℝ) < D → τ t ∉ range σ)
    (x : X) : x ∈ range σ ∨ x ∈ range τ := by
  by_cases hx : x ∈ range σ
  · exact Or.inl hx
  let p := σ ⟨0, le_rfl, hD⟩
  let q := σ ⟨D, hD, le_rfl⟩
  have hxp : x ≠ p := fun h => hx ⟨⟨0, le_rfl, hD⟩, h.symm⟩
  have hxq : x ≠ q := fun h => hx ⟨⟨D, hD, le_rfl⟩, h.symm⟩
  have hsum := dist_add_dist_eq_of_outside_diameter_segment hsegments hD hσ ho hdiam hx
  change dist x p + dist x q = D at hsum
  have hA : 0 < dist x p := dist_pos.mpr hxp
  have hAD : dist x p < D := by linarith [dist_pos.mpr hxq]
  let t : Icc (0 : ℝ) D := ⟨dist x p, hA.le, hAD.le⟩
  have htp : dist (τ t) p = dist x p := by
    calc
      dist (τ t) p = dist (τ t) (τ ⟨0, le_rfl, hD⟩) :=
        congrArg (dist (τ t)) hzero.symm
      _ = dist t ⟨0, le_rfl, hD⟩ := hτ.dist_eq _ _
      _ = dist x p := by
        change |dist x p - 0| = dist x p
        rw [sub_zero, abs_of_pos hA]
  have hd := dist_eq_abs_sub_of_outside_diameter_segment hκ hcomp hsegments hD hσ ho hdiam
    hx (hout t hA hAD)
  change dist x (τ t) = |dist x p - dist (τ t) p| at hd
  rw [htp, sub_self, abs_zero] at hd
  exact Or.inr ⟨t, (dist_eq_zero.mp hd).symm⟩

theorem exists_opposite_diameter_arc_of_point_outside
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D) {x : X} (hx : x ∉ range σ) :
    ∃ τ : Icc (0 : ℝ) D → X, Isometry τ ∧
      τ ⟨0, le_rfl, hD⟩ = σ ⟨0, le_rfl, hD⟩ ∧
      τ ⟨D, hD, le_rfl⟩ = σ ⟨D, hD, le_rfl⟩ ∧ x ∈ range τ ∧
      (∀ t : Icc (0 : ℝ) D, 0 < (t : ℝ) → (t : ℝ) < D → τ t ∉ range σ) ∧
      ∀ y : X, y ∈ range σ ∨ y ∈ range τ := by
  let p := σ ⟨0, le_rfl, hD⟩
  let q := σ ⟨D, hD, le_rfl⟩
  have hpq : dist p q = D := by
    rw [hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hD]
  have hsum : dist p x + dist x q = dist p q := by
    rw [hpq, dist_comm p x]
    exact dist_add_dist_eq_of_outside_diameter_segment hsegments hD hσ ho hdiam hx
  obtain ⟨β, hβ, hβ0, hβD, hβx⟩ := exists_isometric_segment_through_of_dist_add_eq hsegments hsum
  let τ : Icc (0 : ℝ) D → X := fun t => β ⟨t, t.property.1, by rw [hpq]; exact t.property.2⟩
  have hτ : Isometry τ := Isometry.of_dist_eq (fun s t => hβ.dist_eq _ _)
  have hτ0 : τ ⟨0, le_rfl, hD⟩ = p := hβ0
  have hτD : τ ⟨D, hD, le_rfl⟩ = q := by
    change β ⟨D, hD, hpq.ge⟩ = q
    exact (congrArg β (Subtype.ext hpq.symm)).trans hβD
  have hAD : dist p x ≤ D := hdiam p x
  let w : Icc (0 : ℝ) D := ⟨dist p x, dist_nonneg, hAD⟩
  have hτx : τ w = x := hβx
  have hout := segment_interior_outside_of_point_outside hD hσ hτ ho hτ0 hτD
    (show τ w ∉ range σ from hτx ▸ hx)
  exact ⟨τ, hτ, hτ0, hτD, ⟨w, hτx⟩, hout,
    mem_range_or_mem_range_of_opposite_diameter_arcs hκ hcomp hsegments hD hσ hτ ho hdiam hτ0 hout⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
