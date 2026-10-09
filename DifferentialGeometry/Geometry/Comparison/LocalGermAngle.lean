import DifferentialGeometry.Geometry.Comparison.GermAngle

set_option autoImplicit false

open Set Filter Topology Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_uniform_hinge_angle_limit
    {X : Type*} [MetricSpace X] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω) :
    ∃ a : ℝ, 0 < a ∧ ∀ (q : X) (R S : ℝ) (γ β : ℝ → X),
      0 < R → 0 < S → R + S < a → γ R ∈ ball p a →
      (∀ s ∈ Ioc (0 : ℝ) R, dist q (γ s) = s) →
      (∀ t ∈ Ioc (0 : ℝ) S, dist q (β t) = t) →
      (∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
        dist (γ s) (γ t) = |s - t|) →
      (∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
        dist (β s) (β t) = |s - t|) →
      limitingComparisonAngle κ R S γ β ∈ Icc (0 : ℝ) Real.pi ∧
      comparisonAngleNegCurvature κ R S (dist (γ R) (β S)) ≤
        limitingComparisonAngle κ R S γ β ∧
      Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
        (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
        (𝓝 (limitingComparisonAngle κ R S γ β)) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  refine ⟨ρ / 4, by positivity, ?_⟩
  intro q R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  have hend' : dist (γ R) p < ρ / 4 := hend
  have hqdist : dist q p < ρ / 2 := by
    have ht := dist_triangle q (γ R) p
    rw [hγrad R ⟨hR, le_rfl⟩] at ht
    linarith
  have hq : q ∈ Ω := hball (show dist q p < ρ by linarith)
  have hγmem (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) : γ s ∈ Ω := by
    apply hball
    change dist (γ s) p < ρ
    have ht := dist_triangle (γ s) q p
    rw [dist_comm (γ s) q, hγrad s hs] at ht
    linarith [hs.2]
  have hβmem (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) S) : β s ∈ Ω := by
    apply hball
    change dist (β s) p < ρ
    have ht := dist_triangle (β s) q p
    rw [dist_comm (β s) q, hβrad s hs] at ht
    linarith [hs.2]
  exact ⟨limitingComparisonAngle_mem_Icc γ β hR hS,
    comparisonAngleNegCurvature_le_limitingComparisonAngle γ β ⟨hR, le_rfl⟩ ⟨hS, le_rfl⟩,
    tendsto_limitingComparisonAngle_of_fourPointComparison hκ hR hS hcomp hq
      hγrad hβrad hγmin hβmin hγmem hβmem⟩

theorem exists_local_comparisonAngle_limit
    {X : Type*} [MetricSpace X] {κ R S : ℝ} (hκ : 0 ≤ κ)
    (hR : 0 < R) (hS : 0 < S) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω)
    {γ β : ℝ → X}
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ t ∈ Ioc (0 : ℝ) S, dist p (β t) = t)
    (hγmin : ∀ s ∈ Ioc (0 : ℝ) R, ∀ t ∈ Ioc (0 : ℝ) R,
      dist (γ s) (γ t) = |s - t|)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) S, ∀ t ∈ Ioc (0 : ℝ) S,
      dist (β s) (β t) = |s - t|) :
    ∃ r ∈ Ioc (0 : ℝ) (min R S),
      limitingComparisonAngle κ r r γ β ∈ Icc (0 : ℝ) Real.pi ∧
      Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
        (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
        (𝓝 (limitingComparisonAngle κ r r γ β)) := by
  obtain ⟨a, ha, hangle⟩ := exists_uniform_hinge_angle_limit hκ hΩ hcomp hp
  let r := min (min R S) (a / 4)
  have hr : 0 < r := lt_min (lt_min hR hS) (by positivity)
  have hrRS : r ≤ min R S := min_le_left _ _
  have hra : r ≤ a / 4 := min_le_right _ _
  have hsubR : Ioc (0 : ℝ) r ⊆ Ioc (0 : ℝ) R :=
    Ioc_subset_Ioc_right (hrRS.trans (min_le_left _ _))
  have hsubS : Ioc (0 : ℝ) r ⊆ Ioc (0 : ℝ) S :=
    Ioc_subset_Ioc_right (hrRS.trans (min_le_right _ _))
  have hend : γ r ∈ ball p a := by
    rw [mem_ball, dist_comm (γ r) p, hγrad r (hsubR ⟨hr, le_rfl⟩)]
    linarith
  have h := hangle p r r γ β hr hr (by linarith) hend
    (fun s hs => hγrad s (hsubR hs)) (fun t ht => hβrad t (hsubS ht))
    (fun s hs t ht => hγmin s (hsubR hs) t (hsubR ht))
    (fun s hs t ht => hβmin s (hsubS hs) t (hsubS ht))
  exact ⟨r, ⟨hr, hrRS⟩, h.1, h.2.2⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
