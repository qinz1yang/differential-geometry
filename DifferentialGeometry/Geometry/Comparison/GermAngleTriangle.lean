import DifferentialGeometry.Geometry.Comparison.CanonicalLocalAngle
import DifferentialGeometry.Geometry.Comparison.GermDistanceAsymptotic
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.AngleTriangle

set_option autoImplicit false

open Set Filter Topology Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem angle_triangle_of_joint_comparisonAngle
    {X : Type*} [MetricSpace X] {κ R S T a b c : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 < R) (hS : 0 < S) (hT : 0 < T)
    (p : X) (γ β δ : ℝ → X)
    (hγrad : ∀ s ∈ Ioc (0 : ℝ) R, dist p (γ s) = s)
    (hβrad : ∀ s ∈ Ioc (0 : ℝ) S, dist p (β s) = s)
    (hδrad : ∀ s ∈ Ioc (0 : ℝ) T, dist p (δ s) = s)
    (hγβ : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (γ z.1) (β z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 a))
    (hβδ : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (β z.1) (δ z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 b))
    (hγδ : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (γ z.1) (δ z.2))) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 c)) :
    c ≤ a + b := by
  have ha : a ∈ Icc (0 : ℝ) Real.pi := by
    rw [← germComparisonAngle_eq_of_tendsto hγβ]
    exact germComparisonAngle_mem_Icc κ γ β
  have hb : b ∈ Icc (0 : ℝ) Real.pi := by
    rw [← germComparisonAngle_eq_of_tendsto hβδ]
    exact germComparisonAngle_mem_Icc κ β δ
  have hc : c ∈ Icc (0 : ℝ) Real.pi := by
    rw [← germComparisonAngle_eq_of_tendsto hγδ]
    exact germComparisonAngle_mem_Icc κ γ δ
  apply Real.angle_triangle_of_cosine_distance_triangle ha hb hc
  intro u v w hu hv hw
  have h1 := dist_div_tendsto_of_joint_comparisonAngle hκ hR hS p γ β
    hγrad hβrad hγβ hu hv
  have h2 := dist_div_tendsto_of_joint_comparisonAngle hκ hS hT p β δ
    hβrad hδrad hβδ hv hw
  have h3 := dist_div_tendsto_of_joint_comparisonAngle hκ hR hT p γ δ
    hγrad hδrad hγδ hu hw
  apply le_of_tendsto_of_tendsto h3 (h1.add h2)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (div_le_div_of_nonneg_right (dist_triangle (γ (u * t)) (β (v * t))
    (δ (w * t))) ht.le).trans_eq (add_div _ _ _)

theorem germComparisonAngle_triangle_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {ι : Type*} {κ : ℝ} (hκ : 0 ≤ κ)
    {L : ι → ℝ} (hL : ∀ i, 0 < L i) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) {p : X} (hp : p ∈ Ω)
    {γ : ι → ℝ → X}
    (hrad : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), dist p (γ i s) = s)
    (hmin : ∀ i, ∀ s ∈ Ioc (0 : ℝ) (L i), ∀ t ∈ Ioc (0 : ℝ) (L i),
      dist (γ i s) (γ i t) = |s - t|) (i j k : ι) :
    germComparisonAngle κ (γ i) (γ k) ≤
      germComparisonAngle κ (γ i) (γ j) + germComparisonAngle κ (γ j) (γ k) := by
  exact angle_triangle_of_joint_comparisonAngle hκ (hL i) (hL j) (hL k)
    p (γ i) (γ j) (γ k) (hrad i) (hrad j) (hrad k)
    (tendsto_germComparisonAngle_of_local_fourPointComparison hκ (hL i) (hL j)
      hΩ hcomp hp (hrad i) (hrad j) (hmin i) (hmin j))
    (tendsto_germComparisonAngle_of_local_fourPointComparison hκ (hL j) (hL k)
      hΩ hcomp hp (hrad j) (hrad k) (hmin j) (hmin k))
    (tendsto_germComparisonAngle_of_local_fourPointComparison hκ (hL i) (hL k)
      hΩ hcomp hp (hrad i) (hrad k) (hmin i) (hmin k))

end DifferentialGeometry.Geometry.Comparison.Toponogov
