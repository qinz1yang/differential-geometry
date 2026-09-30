import DifferentialGeometry.Geometry.Comparison.OneDimensionalSegments
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Topology.MetricSpace.IntervalRecognition

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_pointed_interval_or_half_interval_of_dimH_le_one [Nontrivial X]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hcomplete : ∀ z : X, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hdim : dimH (univ : Set X) ≤ 1) (p : X) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : X) = p) ∨
      (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : X) = p) := by
  apply exists_pointed_interval_or_half_interval_of_isOpen_segments hsegments
  exact isOpen_segment_image_of_dimH_le_one
    (arbitrarily_short_curves_of_metric_segments hsegments) hcomp hcomplete hdim

theorem ball_eq_segment_image_of_dimH_le_one
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hcomplete : ∀ z : X, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hdim : dimH (univ : Set X) ≤ 1)
    {l u : ℝ} {σ : Icc l u → X} (hσ : Isometry σ)
    (p : Icc l u) {r : ℝ} (hr : r ≤ min ((p : ℝ) - l) (u - p)) :
    ball (σ p) r = σ '' {t | dist t p < r} :=
  ball_eq_segment_image_of_isOpen hsegments hσ
    (isOpen_segment_image_of_dimH_le_one (arbitrarily_short_curves_of_metric_segments hsegments)
      hcomp hcomplete hdim l u σ hσ) p hr

theorem singleton_or_pointed_interval_charts_of_dimH_le_one [Nonempty X] [CompleteSpace X]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hdim : dimH (univ : Set X) ≤ 1) :
    Nonempty (X ≃ᵢ PUnit) ∨ ∀ p : X, ∃ r : ℝ, ∃ hr : 0 < r,
      (∃ e : Ioo (-r) r ≃ᵢ ball p r, (e ⟨0, by constructor <;> linarith⟩ : X) = p) ∨
      (∃ e : Ico (0 : ℝ) r ≃ᵢ ball p r, (e ⟨0, le_rfl, hr⟩ : X) = p) := by
  classical
  cases subsingleton_or_nontrivial X with
  | inl hsub =>
    let := hsub
    let : Unique X := { default := Classical.choice inferInstance, uniq := fun x => Subsingleton.elim x _ }
    apply Or.inl
    exact ⟨{ Equiv.equivPUnit X with
      isometry_toFun := Isometry.of_dist_eq (fun x y => by simp [Subsingleton.elim x y]) }⟩
  | inr hnon =>
    let := hnon
    exact Or.inr (exists_pointed_interval_or_half_interval_of_dimH_le_one hsegments hcomp
      (fun z => ⟨1, by norm_num, isClosed_closedBall.isComplete⟩) hdim)

end DifferentialGeometry.Geometry.Comparison.Toponogov
