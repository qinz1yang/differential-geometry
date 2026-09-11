import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_metricFamilySectionPairing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {τ : X → ℝ} {U : X → M} {s : Set X} {x : X}
    (hτ : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ τ s x)
    (hU : ContMDiffWithinAt J 𝓘(ℝ, E) ∞ U s x)
    (ht : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s x)
    (hZ : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s x) :
    ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ (fun q => (G (τ q)).inner (U q) (W q) (Z q)) s x := by
  have hmetric := (hG.metricCLMSmoothAt ht).comp_contMDiffWithinAt x (hτ.prodMk hU)
  have hpair : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        ((G (τ q)).inner (U q) (W q) (Z q))) s x :=
    ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hmetric hW hZ
  exact (contMDiffWithinAt_totalSpace.mp hpair).2

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffAt_metricFamilySectionPairing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {τ : X → ℝ} {U : X → M} {x : X}
    (hτ : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ τ x) (hU : ContMDiffAt J 𝓘(ℝ, E) ∞ U x)
    (ht : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) x)
    (hZ : ContMDiffAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) x) :
    ContMDiffAt J 𝓘(ℝ, ℝ) ∞ (fun q => (G (τ q)).inner (U q) (W q) (Z q)) x := by
  have hmetric := (hG.metricCLMSmoothAt ht).comp x (hτ.prodMk hU)
  have hpair : ContMDiffAt J (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (U q)
        ((G (τ q)).inner (U q) (W q) (Z q))) x :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hmetric hW hZ
  exact (contMDiffAt_totalSpace.mp hpair).2

end DifferentialGeometry.Geometry
