import DifferentialGeometry.Geometry.Comparison.IntrinsicUniformStrutChart
import DifferentialGeometry.Geometry.Comparison.EuclideanTangentDirections
import DifferentialGeometry.Geometry.Comparison.GermCurvatureIndependence
import DifferentialGeometry.Geometry.Comparison.ConsistentEndpointDirections
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_uniform_strut_chart_of_euclidean_tangent
    {X : Type*} [MetricSpace X] [CompleteSpace X]
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
    : letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
        (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
        (by change dist q p < 8 * R; linarith)
      ∀ (e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m)), e EuclideanCone.tip = 0 →
      (∀ x : ball p R, dist x.val q < η →
        letI : HasAnglesAt x.val := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
          (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
          (by have hx : dist x.val p < R := x.property; change dist x.val p < 8 * R; linarith)
        AngularObstruction (SpaceOfDirections x.val) m (8 * (n : ℝ))⁻¹) →
    ∃ (d : Fin (m + 1) → GeodesicRepresentative q) (s ρ : ℝ), 0 < s ∧ s < R / 8 ∧
      (∀ i, s ≤ (d i).length) ∧ (∀ i, dist q ((d i).path s) = s) ∧
      ∃ hρ : 0 < ρ, ρ < s / 8 ∧ ρ < η ∧
      (∀ i, (d i).path s ∈ ball p R) ∧ ball q ρ ⊆ ball p R ∧
      1 ≤ strutChartDistortion n ∧
      ∃ (E : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
        (F : ball q ρ → EuclideanSpace ℝ (Fin n)),
        (∀ x, F x = E (distanceCoordinates 2 (fun j : Fin m => (d j.succ).path s) x.val -
          distanceCoordinates 2 (fun j : Fin m => (d j.succ).path s) q)) ∧
        F ⟨q, mem_ball_self hρ⟩ = 0 ∧
        (∀ x y, (strutChartDistortion n)⁻¹ * dist x y ≤ dist (F x) (F y) ∧
          dist (F x) (F y) ≤ strutChartDistortion n * dist x y) ∧
        ∃ e : ball q ρ ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = F x := by
  have hA (x : ball p R) : HasAnglesAt x.val :=
    hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by have hx : dist x.val p < R := x.property; change dist x.val p < 8 * R; linarith)
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; linarith)
  intro e he hangular
  let : ∀ x : ball p R, HasAnglesAt x.val := hA
  obtain ⟨σ, _, hσ⟩ := exists_consistent_endpoint_representatives_of_eight_buffer hcurves p hR
  let D := fun x : ball p R => SpaceOfDirections x.val
  let direction : ∀ x y : ball p R, x.val ≠ y.val → D x :=
    fun x y hxy => (σ x y hxy).direction
  have hhinges (x a y : ball p R) (ha : x.val ≠ a.val) (hy : x.val ≠ y.val) :
      ∃ H : MinimizingHinge a.val y.val,
        H.center = x.val ∧ H.germAngle 1 = dist (direction x y hy) (direction x a ha) := by
    obtain ⟨H, hc, _, _, hang⟩ := hσ x a y ha hy (hA x)
    exact ⟨H, hc, hang 1 (by norm_num)⟩
  have hangle (σ τ : GeodesicRepresentative q) :
      Tendsto (fun s : ℝ => comparisonAngleNegCurvature 1 s s
        (dist (σ.path s) (τ.path s))) (𝓝[>] (0 : ℝ))
        (𝓝 (InnerProductGeometry.angle (TangentCone.unitVector e he σ.direction).val
          (TangentCone.unitVector e he τ.direction).val)) := by
    have hdiff := tendsto_comparisonAngleNegCurvature_sub_curvature_zero_of_radial
      (κ := 1) (by norm_num) σ.length_pos τ.length_pos q σ.path τ.path
      (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
      (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    have hcurv : Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature 1 z.1 z.2
        (dist (σ.path z.1) (τ.path z.2)))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (σ.angle τ)) := by
      simpa only [sub_add_cancel, zero_add] using hdiff.add (HasAnglesAt.tendsto_angle σ τ)
    have heq := (TangentCone.angle_unitVector e he σ.direction τ.direction).trans
      (σ.dist_direction τ)
    rw [heq]
    have hdiag : Tendsto (fun t : ℝ => (t, t)) (𝓝[>] (0 : ℝ))
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) := tendsto_id.prodMk tendsto_id
    simpa only [Function.comp_def] using hcurv.comp hdiag
  exact exists_uniform_strut_chart_of_intrinsic_8_buffer
    (T := GeodesicRepresentative q) hcurves hm hmn hR hq hη hlocal
    (fun σ => TangentCone.unitVector e he σ.direction)
    (fun σ => σ.path) (fun σ => σ.length) (fun σ => σ.length_pos)
    (fun σ _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun v hv ε hε => TangentCone.exists_representative_angle_lt e he v hv hε) hangle
    D direction hangular hhinges

end DifferentialGeometry.Geometry.Comparison.Toponogov
