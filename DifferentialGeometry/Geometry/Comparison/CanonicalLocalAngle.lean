import DifferentialGeometry.Geometry.Comparison.CanonicalGermAngle

set_option autoImplicit false

open Set Filter Topology Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_germComparisonAngle_of_local_fourPointComparison
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
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (germComparisonAngle κ γ β)) := by
  obtain ⟨r, hr, hb, ht⟩ := exists_local_comparisonAngle_limit hκ hR hS hΩ hcomp hp
    hγrad hβrad hγmin hβmin
  rwa [germComparisonAngle_eq_of_tendsto ht]

theorem germComparisonAngle_sum_le_two_pi_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {ι : Type*} {κ : ℝ} (hκ : 0 ≤ κ)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω)
    {γ : ι → ℝ → X}
    (hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist p (γ i s) = s)
    (hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t|) (i j k : ι) :
    germComparisonAngle κ (γ i) (γ j) + germComparisonAngle κ (γ j) (γ k) +
      germComparisonAngle κ (γ k) (γ i) ≤ 2 * Real.pi := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ p hp
  let l := fun i => min (L i) (ρ / 2)
  have hl (i : ι) : 0 < l i := lt_min (hL i) (by positivity)
  have hsub (i : ι) : Ioc (0 : ℝ) (l i) ⊆ Ioc (0 : ℝ) (L i) :=
    Ioc_subset_Ioc_right (min_le_left _ _)
  have hrad' (i : ι) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (l i)) :
      dist p (γ i s) = s := hrad i s (hsub i hs)
  have hmin' (i : ι) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (l i))
      (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) (l i)) :
      dist (γ i s) (γ i t) = |s - t| := hmin i s (hsub i hs) t (hsub i ht)
  have hmem (i : ι) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (l i)) : γ i s ∈ Ω := by
    apply hball
    rw [mem_ball, dist_comm, hrad' i s hs]
    have hle : l i ≤ ρ / 2 := min_le_right _ _
    linarith [hs.2]
  have heq (i j : ι) : germComparisonAngle κ (γ i) (γ j) =
      limitingComparisonAngle κ (l i) (l j) (γ i) (γ j) :=
    germComparisonAngle_eq_limitingComparisonAngle hκ (hl i) (hl j) hcomp hp
      (hrad' i) (hrad' j) (hmin' i) (hmin' j) (hmem i) (hmem j)
  rw [heq i j, heq j k, heq k i]
  exact limitingComparisonAngle_sum_le_two_pi hκ hl hcomp hp hrad' hmin' hmem i j k

theorem germComparisonAngle_adjacent_sum_le_pi_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {ι : Type*} {κ : ℝ} (hκ : 0 ≤ κ)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω)
    {γ : ι → ℝ → X}
    (hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist p (γ i s) = s)
    (hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t|) (i j k : ι)
    (hopp : ∀ s ∈ Ioc (0 : ℝ) (L k), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ k s) (γ i t) = s + t) :
    germComparisonAngle κ (γ i) (γ j) + germComparisonAngle κ (γ j) (γ k) ≤ Real.pi := by
  have h := germComparisonAngle_sum_le_two_pi_of_local_fourPointComparison
    hκ hL hΩ hcomp hp hrad hmin i j k
  rw [germComparisonAngle_opposite hκ (hL k) (hL i) hopp] at h
  linarith

theorem exists_uniform_hinge_germComparisonAngle_bound
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
      comparisonAngleNegCurvature κ R S (dist (γ R) (β S)) ≤
        germComparisonAngle κ γ β := by
  obtain ⟨a, ha, h⟩ := exists_uniform_hinge_angle_limit hκ hΩ hcomp hp
  refine ⟨a, ha, ?_⟩
  intro q R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  have ht := h q R S γ β hR hS hsum hend hγrad hβrad hγmin hβmin
  rw [germComparisonAngle_eq_of_tendsto ht.2.2]
  exact ht.2.1

end DifferentialGeometry.Geometry.Comparison.Toponogov
