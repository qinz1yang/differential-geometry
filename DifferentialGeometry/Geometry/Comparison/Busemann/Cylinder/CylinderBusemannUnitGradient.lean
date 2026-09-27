import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUnitGradient
import DifferentialGeometry.Geometry.Comparison.Busemann.Cylinder.CylinderOppositeBusemann

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

private abbrev Sphere3 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Cyl3 := Sphere3 × ℝ
private abbrev ICyl3 := (𝓡 2).prod 𝓘(ℝ)

private local instance : NeZero
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_opposite_busemann_unit_gradients_on_cylinder
    (g : SmoothRiemannianMetric ICyl3 Cyl3)
    (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : Cyl3, ∀ v : TangentSpace ICyl3 y, 0 ≤ ricciTensor g y v v) :
    ∃ gamma : ℝ → Cyl3,
      ContMDiff 𝓘(ℝ, ℝ) ICyl3 ∞ gamma ∧ IsGeodesic g gamma ∧
      (gamma 0).2 = 0 ∧
      (∀ s t : ℝ,
        riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|) ∧
      let bplus : Cyl3 → ℝ := fun y ↦ ⨅ t : ℝ,
        (riemannianEDistOf g y (gamma t)).toReal - t
      let bminus : Cyl3 → ℝ := fun y ↦ ⨅ t : ℝ,
        (riemannianEDistOf g y (gamma (-t))).toReal - t
      Continuous bplus ∧ Continuous bminus ∧
      (∀ s : ℝ, bplus (gamma s) = -s ∧ bminus (gamma s) = s) ∧
      (∀ y : Cyl3, bplus y + bminus y = 0) ∧
      MDifferentiable ICyl3 𝓘(ℝ, ℝ) bplus ∧ MDifferentiable ICyl3 𝓘(ℝ, ℝ) bminus ∧
      ∀ x : Cyl3,
        g.inner x (gradientFun g bplus x) (gradientFun g bplus x) = 1 ∧
        g.inner x (gradientFun g bminus x) (gradientFun g bminus x) = 1 := by
  have hsphereConnected : IsConnected
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  let : ConnectedSpace Sphere3 := Subtype.connectedSpace hsphereConnected
  let : ConnectedSpace Cyl3 := inferInstance
  obtain ⟨gamma, hsmooth, hgeo, hheight, hline, hplusCont, hminusCont, hsigned, hsum⟩ :=
    exists_opposite_busemann_functions_on_cylinder g hcomplete hRic
  obtain ⟨hplusDiff, hminusDiff, hunit⟩ :=
    intrinsic_busemann_unit_gradients_of_opposite_sum_zero g hcomplete hRic gamma hline hsum
  exact ⟨gamma, hsmooth, hgeo, hheight, hline, hplusCont, hminusCont,
    hsigned, hsum, hplusDiff, hminusDiff, hunit⟩

end DifferentialGeometry.Geometry.Metric

end
