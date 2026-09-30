import DifferentialGeometry.Geometry.Comparison.CanonicalLocalAngle
import DifferentialGeometry.Geometry.Comparison.ModelSide

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

def endpointHingeComparison {X : Type*} [MetricSpace X] (κ : ℝ) (p : X) (r : ℝ) : Prop :=
  ∀ (x : X) (R S : ℝ) (γ β : ℝ → X), 0 < R → 0 < S → R + S < r → γ R = p →
    (∀ s ∈ Ioc (0 : ℝ) R, dist x (γ s) = s) →
    (∀ t ∈ Ioc (0 : ℝ) S, dist x (β t) = t) →
    (∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R, dist (γ s) (γ t) = |s - t|) →
    (∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S, dist (β s) (β t) = |s - t|) →
    comparisonAngleNegCurvature κ R S (dist p (β S)) ≤ germComparisonAngle κ γ β

theorem endpointHingeComparison.mono {X : Type*} [MetricSpace X] {κ r s : ℝ} {p : X}
    (h : endpointHingeComparison κ p s) (hrs : r ≤ s) : endpointHingeComparison κ p r := by
  intro x R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  exact h x R S γ β hR hS (hsum.trans_le hrs) hend hγrad hβrad hγmin hβmin

theorem exists_uniform_endpointHingeComparison
    {X : Type*} [MetricSpace X] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ ball p a, endpointHingeComparison κ q a := by
  obtain ⟨a, ha, h⟩ := exists_uniform_hinge_germComparisonAngle_bound hκ hΩ hcomp hp
  refine ⟨a, ha, ?_⟩
  intro q hq x R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  rw [← hend]
  exact h x R S γ β hR hS hsum (by rwa [hend]) hγrad hβrad hγmin hβmin

theorem endpointHingeComparison.modelSide_ge_dist
    {X : Type*} [MetricSpace X] {κ r R S : ℝ} (hκ : 0 ≤ κ) {p x : X}
    (h : endpointHingeComparison κ p r) {γ β : ℝ → X}
    (hR : 0 < R) (hS : 0 < S) (hsum : R + S < r) (hend : γ R = p)
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist x (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist x (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|) :
    dist p (β S) ≤ modelSideNegCurvature κ R S (germComparisonAngle κ γ β) := by
  have ha : dist x p = R := by simpa only [hend] using hγrad R ⟨hR, le_rfl⟩
  have hb : dist x (β S) = S := hβrad S ⟨hS, le_rfl⟩
  have ht₁ := dist_triangle p x (β S)
  rw [dist_comm p x, ha, hb] at ht₁
  have ht₂ := dist_triangle x p (β S)
  rw [ha, hb] at ht₂
  have ht₃ := dist_triangle x (β S) p
  rw [ha, hb, dist_comm (β S) p] at ht₃
  have heq := modelSideNegCurvature_comparisonAngle hκ hR hS
    (abs_le.mpr ⟨by linarith, by linarith⟩) ht₁
  rw [← heq]
  exact modelSideNegCurvature_mono_angle hκ hR.le hS.le
    (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
    (germComparisonAngle_mem_Icc _ _ _).2
    (h x R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin)

end DifferentialGeometry.Geometry.Comparison.Toponogov
