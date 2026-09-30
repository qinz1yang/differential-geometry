import DifferentialGeometry.Geometry.Comparison.SegmentGermAngle
import DifferentialGeometry.Geometry.Comparison.ModelSideExtension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem modelSideNegCurvature_le_of_segment_germ_comparisons
    {X : Type*} [MetricSpace X] {κ a b h c : ℝ} (hκ : 0 ≤ κ)
    (ha : 0 < a) (hh : 0 < h) (hhb : h < b) (hc : 0 < c)
    {σ : Icc (0 : ℝ) b → X} (hσ : Isometry σ)
    {γ β : ℝ → X} {Ω : Set X} (hΩ : IsOpen Ω)
    (hcomp : fourPointComparison κ Ω)
    (hp : σ ⟨h, ⟨hh.le, hhb.le⟩⟩ ∈ Ω)
    (hβrad : ∀ s ∈ Ioc (0 : ℝ) c,
      dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) (β s) = s)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) c, ∀ t ∈ Ioc (0 : ℝ) c,
      dist (β s) (β t) = |s - t|)
    (hlower : |a - h| ≤ c) (hupper : c ≤ a + h)
    (hfirst : comparisonAngleNegCurvature κ a h c ≤
      germComparisonAngle κ γ (IccExtend (hh.le.trans hhb.le) σ))
    (hsecond : comparisonAngleNegCurvature κ c h a ≤
      germComparisonAngle κ β (fun t => IccExtend (hh.le.trans hhb.le) σ (h - t))) :
    modelSideNegCurvature κ c (b - h)
      (germComparisonAngle κ β (fun t => IccExtend (hh.le.trans hhb.le) σ (h + t))) ≤
    modelSideNegCurvature κ a b
      (germComparisonAngle κ γ (IccExtend (hh.le.trans hhb.le) σ)) := by
  have hadj := germComparisonAngle_IccExtend_adjacent_sum_le_pi
    hκ hh hhb hc hσ hΩ hcomp hp hβrad hβmin
  apply modelSideNegCurvature_le_of_adjacent_comparisons hκ ha hh hc hhb hlower hupper
    (germComparisonAngle_mem_Icc _ _ _) (germComparisonAngle_mem_Icc _ _ _) hfirst
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem modelSideNegCurvature_cradle_step_le
    {X : Type*} [MetricSpace X] {κ h : ℝ} (hκ : 0 ≤ κ)
    {x u v : X} (ha : 0 < dist x u) (hh : 0 < h) (hhb : h < dist x v)
    (σ : Icc (0 : ℝ) (dist x v) → X) (hσ : Isometry σ)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hσv : σ ⟨dist x v, ⟨dist_nonneg, le_rfl⟩⟩ = v)
    (hc : 0 < dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u)
    {γ β : ℝ → X} {Ω : Set X} (hΩ : IsOpen Ω)
    (hcomp : fourPointComparison κ Ω)
    (hp : σ ⟨h, ⟨hh.le, hhb.le⟩⟩ ∈ Ω)
    (hβrad : ∀ s ∈ Ioc (0 : ℝ) (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u),
      dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) (β s) = s)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u),
      ∀ t ∈ Ioc (0 : ℝ) (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u),
      dist (β s) (β t) = |s - t|)
    (hfirst : comparisonAngleNegCurvature κ (dist x u) h
      (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u) ≤
      germComparisonAngle κ γ (IccExtend dist_nonneg σ))
    (hsecond : comparisonAngleNegCurvature κ
      (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u) h (dist x u) ≤
      germComparisonAngle κ β (fun t => IccExtend dist_nonneg σ (h - t))) :
    modelSideNegCurvature κ (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) u)
      (dist (σ ⟨h, ⟨hh.le, hhb.le⟩⟩) v)
      (germComparisonAngle κ β (fun t => IccExtend dist_nonneg σ (h + t))) ≤
    modelSideNegCurvature κ (dist x u) (dist x v)
      (germComparisonAngle κ γ (IccExtend dist_nonneg σ)) := by
  let z := σ ⟨h, ⟨hh.le, hhb.le⟩⟩
  have hxz : dist x z = h := by
    have he := hσ.dist_eq (⟨0, ⟨le_rfl, dist_nonneg⟩⟩ : Icc (0 : ℝ) (dist x v))
      ⟨h, ⟨hh.le, hhb.le⟩⟩
    rw [hσ0] at he
    simpa only [z, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hh] using he
  have hzv : dist z v = dist x v - h := by
    have he := hσ.dist_eq (⟨h, ⟨hh.le, hhb.le⟩⟩ : Icc (0 : ℝ) (dist x v))
      ⟨dist x v, ⟨dist_nonneg, le_rfl⟩⟩
    rw [hσv] at he
    change dist z v = |h - dist x v| at he
    rw [abs_of_neg (sub_neg.mpr hhb)] at he
    linarith
  have ht₁ := dist_triangle x z u
  have ht₂ := dist_triangle x u z
  have ht₃ := dist_triangle z x u
  rw [hxz] at ht₁ ht₂
  rw [dist_comm u z] at ht₂
  rw [dist_comm z x, hxz] at ht₃
  change modelSideNegCurvature κ (dist z u) (dist z v) _ ≤ _
  rw [hzv]
  exact modelSideNegCurvature_le_of_segment_germ_comparisons hκ ha hh hhb hc hσ
    hΩ hcomp hp hβrad hβmin (abs_le.mpr ⟨by linarith, by linarith⟩)
    (by linarith) hfirst hsecond

theorem dist_le_modelSideNegCurvature_of_between
    {X : Type*} [MetricSpace X] {κ θ : ℝ} (hκ : 0 ≤ κ)
    {x u v : X} (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (hbetween : dist x u + dist u v = dist x v) :
    dist u v ≤ modelSideNegCurvature κ (dist x u) (dist x v) θ := by
  have heq : |dist x u - dist x v| = dist u v := by
    rw [← hbetween, show dist x u - (dist x u + dist u v) = -dist u v by ring,
      abs_neg, abs_of_nonneg dist_nonneg]
  rw [← heq]
  exact (modelSideNegCurvature_mem_Icc hκ dist_nonneg dist_nonneg hθ).1

end DifferentialGeometry.Geometry.Comparison.Toponogov
