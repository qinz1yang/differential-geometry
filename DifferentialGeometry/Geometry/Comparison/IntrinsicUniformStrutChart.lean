import DifferentialGeometry.Geometry.Comparison.IntrinsicEightHingeComparison
import DifferentialGeometry.Geometry.Comparison.UniformStrutChart

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric Filter
open scoped Topology NNReal

theorem exists_uniform_strut_chart_of_intrinsic_8_buffer
    {X : Type*} {T : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p q : X} {R η : ℝ} (hR : 0 < R) (hq : dist q p < R / 2) (hη : 0 < η)
    [LocallyCompactSpace (ball p (8 * R))]
    (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
      @IsOpen (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p (8 * R))
        (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)
    (ξ : T → {v : EuclideanSpace ℝ (Fin m) // ‖v‖ = 1})
    (γ : T → ℝ → X) (r : T → ℝ)
    (hr : ∀ t, 0 < r t)
    (hradial : ∀ t, ∀ s ∈ Ioc (0 : ℝ) (r t), dist q (γ t s) = s)
    (hdense : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ t, InnerProductGeometry.angle v (ξ t).val < ε)
    (hangle : ∀ t u, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (γ t s) (γ u s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (ξ t).val (ξ u).val)))
    (D : ball p R → Type*) [∀ x, MetricSpace (D x)]
    (direction : ∀ x y : ball p R, x.val ≠ y.val → D x)
    (hangular : ∀ x : ball p R, dist x.val q < η →
      AngularObstruction (D x) m (8 * (n : ℝ))⁻¹)
    (hhinges : ∀ x a y : ball p R, ∀ ha : x.val ≠ a.val, ∀ hy : x.val ≠ y.val,
      ∃ H : MinimizingHinge a.val y.val,
        H.center = x.val ∧ H.germAngle 1 = dist (direction x y hy) (direction x a ha)) :
    ∃ (d : Fin (m + 1) → T) (s ρ : ℝ), 0 < s ∧ s < R / 8 ∧
      (∀ i, s ≤ r (d i)) ∧ (∀ i, dist q (γ (d i) s) = s) ∧
      ∃ hρ : 0 < ρ, ρ < s / 8 ∧ ρ < η ∧
      (∀ i, γ (d i) s ∈ ball p R) ∧ ball q ρ ⊆ ball p R ∧
      1 ≤ strutChartDistortion n ∧
      ∃ (E : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (F : ball q ρ → EuclideanSpace ℝ (Fin n)),
        (∀ x, F x = E (distanceCoordinates 2 (fun j : Fin m => γ (d j.succ) s) x.val -
          distanceCoordinates 2 (fun j : Fin m => γ (d j.succ) s) q)) ∧
        F ⟨q, mem_ball_self hρ⟩ = 0 ∧
        (∀ x y, (strutChartDistortion n)⁻¹ * dist x y ≤ dist (F x) (F y) ∧
          dist (F x) (F y) ≤ strutChartDistortion n * dist x y) ∧
        ∃ e : ball q ρ ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = F x := by
  let δ := min (R / 2) (R / 2 - dist q p)
  have hδ : 0 < δ := lt_min (half_pos hR) (sub_pos.mpr hq)
  have hδR : δ ≤ R / 2 := min_le_left _ _
  have hδgap : δ ≤ R / 2 - dist q p := min_le_right _ _
  have hhalf (x : ball q δ) : x.val ∈ ball p (R / 2) := by
    have ht := dist_triangle x.val q p
    have hx : dist x.val q < δ := x.property
    change dist x.val p < R / 2
    linarith
  have hsub : ball q δ ⊆ ball p R := by
    intro x hx
    have hh : dist x p < R / 2 := hhalf ⟨x, hx⟩
    change dist x p < R
    linarith
  let lift : ball q δ → ball p R := fun x => ⟨x.val, hsub x.property⟩
  let D' := fun (x : ball q δ) => D (lift x)
  let direction' : ∀ x y : ball q δ, x.val ≠ y.val → D' x :=
    fun x y hxy => direction (lift x) (lift y) hxy
  have hang' (x : ball q δ) (hx : dist x.val q < η) :
      AngularObstruction (D' x) m (8 * (n : ℝ))⁻¹ := hangular (lift x) hx
  have hhinges' (x a y : ball q δ) (ha : x.val ≠ a.val) (hy : x.val ≠ y.val) :
      ∃ H : MinimizingHinge a.val y.val,
        H.center = x.val ∧ H.germAngle 1 = dist (direction' x y hy) (direction' x a ha) ∧
          dist a.val y.val ≤ H.modelSide 1 := by
    obtain ⟨H, hc, hangleH⟩ := hhinges (lift x) (lift a) (lift y) ha hy
    refine ⟨H, hc, hangleH, ?_⟩
    exact H.modelSide_ge_dist_of_intrinsic_8_buffer hcurves p (by norm_num) hR hlocal
      (by rw [hc]; exact hhalf x)
      (mem_closedBall.mpr (le_of_lt (show dist a.val p < R from (lift a).property)))
      (mem_closedBall.mpr (le_of_lt (show dist y.val p < R from (lift y).property)))
  obtain ⟨d, s, ρ, hs, hsδ, hsr, hrad, hρ, hρs, hρη, haδ, hsubδ, hL, E, F,
      hF, hzero, hbounds, he⟩ := exists_uniform_strut_chart_of_dense_directions
    hm hmn hδ (by simpa only [dist_self] using half_pos hδ) hη
    ξ γ r hr hradial hdense hangle D' direction' hang' hhinges'
  refine ⟨d, s, ρ, hs, ?_, hsr, hrad, hρ, hρs, hρη,
    (fun i => hsub (haδ i)), hsubδ.trans hsub, hL, E, F, hF, hzero, hbounds, he⟩
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
