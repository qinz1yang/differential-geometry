import DifferentialGeometry.Geometry.Comparison.DiameterCircleCoordinate
import DifferentialGeometry.Geometry.Comparison.OppositeDiameterArc

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem diameterCircleCoordinate_on_opposite_arc
    {D : ℝ} (hD : 0 < D) {σ τ : Icc (0 : ℝ) D → X} (hσ : Isometry σ) (hτ : Isometry τ)
    (hzero : τ ⟨0, le_rfl, hD.le⟩ = σ ⟨0, le_rfl, hD.le⟩)
    (hend : τ ⟨D, hD.le, le_rfl⟩ = σ ⟨D, hD.le, le_rfl⟩)
    (hout : ∀ t : Icc (0 : ℝ) D, 0 < (t : ℝ) → (t : ℝ) < D → τ t ∉ range σ)
    (t : Icc (0 : ℝ) D) :
    diameterCircleCoordinate hD σ (τ t) = ((-(t : ℝ) : ℝ) : AddCircle (2 * D)) := by
  classical
  by_cases ht0 : (t : ℝ) = 0
  · have ht : t = ⟨0, le_rfl, hD.le⟩ := Subtype.ext ht0
    rw [ht, hzero, diameterCircleCoordinate_apply_isometry hD hσ]
    simp only [neg_zero]
  by_cases htD : (t : ℝ) = D
  · have ht : t = ⟨D, hD.le, le_rfl⟩ := Subtype.ext htD
    rw [ht, hend, diameterCircleCoordinate_apply_isometry hD hσ]
    change (D : AddCircle (2 * D)) = ((-D : ℝ) : AddCircle (2 * D))
    rw [show (-D : ℝ) = D - 2 * D by ring, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
  have htin : 0 < (t : ℝ) ∧ (t : ℝ) < D :=
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htD⟩
  rw [diameterCircleCoordinate, ite_eq_right (hout t htin.1 htin.2)]
  have hd : dist (τ t) (σ ⟨0, le_rfl, hD.le⟩) = (t : ℝ) := by
    rw [← hzero, hτ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.property.1]
  rw [hd]

theorem exists_circle_isometry_of_opposite_diameter_arcs
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 < D) {σ τ : Icc (0 : ℝ) D → X} (hσ : Isometry σ) (hτ : Isometry τ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D)
    (hzero : τ ⟨0, le_rfl, hD.le⟩ = σ ⟨0, le_rfl, hD.le⟩)
    (hend : τ ⟨D, hD.le, le_rfl⟩ = σ ⟨D, hD.le, le_rfl⟩)
    (hout : ∀ t : Icc (0 : ℝ) D, 0 < (t : ℝ) → (t : ℝ) < D → τ t ∉ range σ) :
    ∃ e : X ≃ᵢ AddCircle (2 * D),
      (∀ t, e (σ t) = ((t : ℝ) : AddCircle (2 * D))) ∧
      (∀ t, e (τ t) = ((-(t : ℝ) : ℝ) : AddCircle (2 * D))) := by
  have hiso := isometry_diameterCircleCoordinate hκ hcomp hsegments hD hσ ho hdiam
  let : Fact (0 < 2 * D) := ⟨by linarith⟩
  have hsurj : Function.Surjective (diameterCircleCoordinate hD σ) := by
    intro y
    have hy : y ∈ ((↑) : ℝ → AddCircle (2 * D)) '' Icc (-D) (-D + 2 * D) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact mem_univ y
    obtain ⟨a, ha, hay⟩ := hy
    have haD : a ≤ D := by linarith [ha.2]
    by_cases ha0 : 0 ≤ a
    · exact ⟨σ ⟨a, ha0, haD⟩, (diameterCircleCoordinate_apply_isometry hD hσ _).trans hay⟩
    · let t : Icc (0 : ℝ) D := ⟨-a, by linarith, by linarith [ha.1]⟩
      refine ⟨τ t, ?_⟩
      rw [diameterCircleCoordinate_on_opposite_arc hD hσ hτ hzero hend hout]
      change ((- -a : ℝ) : AddCircle (2 * D)) = y
      rw [neg_neg]
      exact hay
  let e : X ≃ᵢ AddCircle (2 * D) :=
    ⟨Equiv.ofBijective (diameterCircleCoordinate hD σ) ⟨hiso.injective, hsurj⟩, hiso⟩
  exact ⟨e, diameterCircleCoordinate_apply_isometry hD hσ,
    diameterCircleCoordinate_on_opposite_arc hD hσ hτ hzero hend hout⟩

theorem exists_circle_isometry_of_outside_diameter_segment
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 < D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D) {x : X} (hx : x ∉ range σ) :
    ∃ e : X ≃ᵢ AddCircle (2 * D), ∀ t, e (σ t) = ((t : ℝ) : AddCircle (2 * D)) := by
  obtain ⟨τ, hτ, hzero, hend, _, hout, _⟩ :=
    exists_opposite_diameter_arc_of_point_outside hκ hcomp hsegments hD.le hσ ho hdiam hx
  obtain ⟨e, hσe, _⟩ := exists_circle_isometry_of_opposite_diameter_arcs
    hκ hcomp hsegments hD hσ hτ ho hdiam hzero hend hout
  exact ⟨e, hσe⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
