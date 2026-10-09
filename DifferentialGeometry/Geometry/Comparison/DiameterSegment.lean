import DifferentialGeometry.Topology.MetricSpace.SegmentExteriorDistance
import DifferentialGeometry.Geometry.Comparison.CommonOpposite

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem dist_add_dist_eq_of_outside_diameter_segment
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D) {x : X} (hx : x ∉ range σ) :
    dist x (σ ⟨0, le_rfl, hD⟩) + dist x (σ ⟨D, hD, le_rfl⟩) = D := by
  let p := σ ⟨0, le_rfl, hD⟩
  let q := σ ⟨D, hD, le_rfl⟩
  let A := dist x p
  let B := dist x q
  have hA : 0 ≤ A := dist_nonneg
  have hB : 0 ≤ B := dist_nonneg
  have hAD : A ≤ D := hdiam x p
  have hBD : B ≤ D := hdiam x q
  let t : Icc (0 : ℝ) D := ⟨(B + D - A) / 2, by constructor <;> linarith⟩
  have hd := dist_to_segment_of_not_mem_range hsegments hD hσ ho hx t
  change dist x (σ t) = min (A + (B + D - A) / 2) (B + (D - (B + D - A) / 2)) at hd
  have halg : A + (B + D - A) / 2 = B + (D - (B + D - A) / 2) := by ring
  rw [← halg, min_self] at hd
  have hbound := hdiam x (σ t)
  have hpq : dist p q = D := by
    rw [hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hD]
  have htri := dist_triangle p x q
  rw [hpq, dist_comm p x] at htri
  change D ≤ A + B at htri
  change A + B = D
  linarith

end Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem dist_eq_abs_sub_of_outside_diameter_segment
    {κ : ℝ} (hκ : 0 ≤ κ) (hcomp : fourPointComparison κ (univ : Set X))
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 ≤ D) {σ : Icc (0 : ℝ) D → X} (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hdiam : ∀ x y : X, dist x y ≤ D) {x y : X}
    (hx : x ∉ range σ) (hy : y ∉ range σ) :
    dist x y = |dist x (σ ⟨0, le_rfl, hD⟩) - dist y (σ ⟨0, le_rfl, hD⟩)| := by
  let p := σ ⟨0, le_rfl, hD⟩
  let q := σ ⟨D, hD, le_rfl⟩
  let A := dist x p
  let B := dist y p
  have hxsum := dist_add_dist_eq_of_outside_diameter_segment hsegments hD hσ ho hdiam hx
  have hysum := dist_add_dist_eq_of_outside_diameter_segment hsegments hD hσ ho hdiam hy
  change A + dist x q = D at hxsum
  change B + dist y q = D at hysum
  have hxq : x ≠ q := fun h => hx ⟨⟨D, hD, le_rfl⟩, h.symm⟩
  have hyq : y ≠ q := fun h => hy ⟨⟨D, hD, le_rfl⟩, h.symm⟩
  have hAD : A < D := by linarith [dist_pos.mpr hxq]
  have hBD : B < D := by linarith [dist_pos.mpr hyq]
  let a := min (D - A) (D - B) / 2
  have ha : 0 < a := half_pos (lt_min (sub_pos.mpr hAD) (sub_pos.mpr hBD))
  have haA : a ≤ D - A := by
    have hm := min_le_left (D - A) (D - B)
    dsimp [a]
    linarith
  have haB : a ≤ D - B := by
    have hm := min_le_right (D - A) (D - B)
    dsimp [a]
    linarith
  have haD : a ≤ D := by linarith [show 0 ≤ A from dist_nonneg]
  let t : Icc (0 : ℝ) D := ⟨a, ha.le, haD⟩
  let z := σ t
  have hpz : dist p z = a := by
    rw [hσ.dist_eq]
    simp only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg]
    exact abs_of_pos ha
  have hzp : z ≠ p := by
    intro heq
    have hz := hpz
    rw [heq, dist_self] at hz
    linarith
  have hxz : dist x z = dist x p + dist p z := by
    rw [hpz]
    have hd := dist_to_segment_of_not_mem_range hsegments hD hσ ho hx t
    change dist x z = min (A + a) (dist x q + (D - a)) at hd
    rw [min_eq_left (by linarith)] at hd
    exact hd
  have hyz : dist y z = dist y p + dist p z := by
    rw [hpz]
    have hd := dist_to_segment_of_not_mem_range hsegments hD hσ ho hy t
    change dist y z = min (B + a) (dist y q + (D - a)) at hd
    rw [min_eq_left (by linarith)] at hd
    exact hd
  exact dist_eq_abs_sub_of_common_opposite hκ hcomp
    (mem_univ p) (mem_univ x) (mem_univ y) (mem_univ z) hzp hxz hyz

end DifferentialGeometry.Geometry.Comparison.Toponogov
