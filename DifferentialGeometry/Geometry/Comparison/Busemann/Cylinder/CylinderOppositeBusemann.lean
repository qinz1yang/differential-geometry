import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderBusemannSupport
import DifferentialGeometry.Analysis.Elliptic.Barrier.StrongMinimumUpperSupport

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := Sphere3 × ℝ
private abbrev ICyl3 := (𝓡 2).prod 𝓘(ℝ)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_opposite_busemann_functions_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3)
    (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : Cyl3, ∀ v : TangentSpace ICyl3 y, 0 ≤ ricciTensor g y v v) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧ IsGeodesic g gamma ∧
      (gamma 0).2 = 0 ∧
      (∀ s t : ℝ,
        riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma t)).toReal - t
      let bminus : Cyl3 → ℝ := fun x ↦
        ⨅ t : ℝ, (riemannianEDistOf g x (gamma (-t))).toReal - t
      Continuous bplus ∧ Continuous bminus ∧
      (∀ s : ℝ, bplus (gamma s) = -s ∧ bminus (gamma s) = s) ∧
      (∀ x : Cyl3, bplus x + bminus x = 0) := by
  have hsphereConnected : IsConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  obtain ⟨gamma, hsmooth, hgeo, hheight, hline, hdata⟩ :=
    exists_opposite_busemann_sum_upper_supports_on_cylinder g hcomplete hRic
  rcases hdata with ⟨hplusCont, hminusCont, hsigned, huCont, hnonneg, hzero, hsupport⟩
  refine ⟨gamma, hsmooth, hgeo, hheight, hline, hplusCont, hminusCont, hsigned, ?_⟩
  exact DifferentialGeometry.Analysis.eq_zero_of_laplacian_upper_supports g _
    huCont hnonneg hsupport (gamma 0) (hzero 0)

end DifferentialGeometry.Geometry.Metric

end
