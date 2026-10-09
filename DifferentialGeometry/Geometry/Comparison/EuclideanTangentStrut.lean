import DifferentialGeometry.Geometry.Comparison.EuclideanTangentDirections
import DifferentialGeometry.Geometry.Comparison.SimplexStrutNeighborhood
import DifferentialGeometry.Geometry.Comparison.GermCurvatureIndependence

set_option autoImplicit false

open Set Metric Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_common_shortening_strut_neighborhood_of_euclidean_tangent
    {X : Type*} [MetricSpace X] {q : X} [HasAnglesAt q]
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (e : TangentCone q ≃ᵢ EuclideanSpace ℝ (Fin m)) (he : e EuclideanCone.tip = 0)
    {S : ℝ} (hS : 0 < S) :
    ∃ (σ : Fin (m + 1) → GeodesicRepresentative q) (s : ℝ), 0 < s ∧ s < S ∧
      (∀ i, s ≤ (σ i).length) ∧ (∀ i, dist q ((σ i).path s) = s) ∧
      (∀ i j, i ≠ j → Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 (dist q ((σ i).path s)) (dist q ((σ j).path s))
          (dist ((σ i).path s) ((σ j).path s))) ∧
      ∀ cap : ℝ, 0 < cap → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s / 8 ∧ ρ < cap ∧
        (∀ x ∈ ball q ρ, ∀ i, s / 2 < dist x ((σ i).path s)) ∧
        ∀ x ∈ ball q ρ, ∀ i j, i ≠ j → Real.pi / 2 + 4 * (8 * (n : ℝ))⁻¹ <
          comparisonAngleNegCurvature 1 (dist x ((σ i).path s)) (dist x ((σ j).path s))
            (dist ((σ i).path s) ((σ j).path s)) := by
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
  exact exists_common_shortening_strut_neighborhood (D := GeodesicRepresentative q) hm hmn q
    (fun σ => TangentCone.unitVector e he σ.direction)
    (fun σ => σ.path) (fun σ => σ.length) (fun σ => σ.length_pos)
    (fun σ _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun v hv ε hε => TangentCone.exists_representative_angle_lt e he v hv hε) hangle hS

end DifferentialGeometry.Geometry.Comparison.Toponogov
