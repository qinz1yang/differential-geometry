import DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import DifferentialGeometry.Geometry.Metric.ParameterTangentMap
import DifferentialGeometry.Geometry.Metric.Pullback.Basic



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_parameterPullbackPairing
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ} (hT : IsOpen T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    {τ : X → ℝ} {U : X → M} {s : Set X} {x : X}
    (hτ : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ τ s x)
    (hU : ContMDiffWithinAt J 𝓘(ℝ, E) ∞ U s x)
    (ht : τ x ∈ T) (hreg : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s x)
    (hZ : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s x) :
    ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞
      (fun q => (Diffeomorph.pullbackMetric (G (τ q)) (Φ (τ q))).inner (U q) (W q) (Z q)) s x := by
  have hbase := ((hΦ _ ⟨ht, mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hU)
  have htan := contMDiffOn_parameter_tangentMap hT hΦ
  have hw := ((htan (τ x, TotalSpace.mk' E (U x) (W x)) ⟨ht, mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hW)
  have hz := ((htan (τ x, TotalSpace.mk' E (U x) (Z x)) ⟨ht, mem_univ _⟩).contMDiffAt
    ((hT.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).comp_contMDiffWithinAt x (hτ.prodMk hZ)
  have h := contMDiffWithinAt_metricFamilySectionPairing hG hτ hbase hreg hw hz
  convert h using 1
  ext q
  exact Diffeomorph.pullbackMetric_inner (G (τ q)) (Φ (τ q)) (U q) (W q) (Z q)

end DifferentialGeometry.Geometry

end

section

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiffWithinAt_parameterPullbackPairing_of_uniqueDiffOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : Type*} [TopologicalSpace B] {J : ModelWithCorners ℝ F B}
    {X : Type*} [TopologicalSpace X] [ChartedSpace B X]
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ} (hT : UniqueDiffOn ℝ T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    {τ : X → ℝ} {U : X → M} {s : Set X} {x : X}
    (hτ : ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞ τ s x)
    (hU : ContMDiffWithinAt J 𝓘(ℝ, E) ∞ U s x)
    (ht : τ x ∈ T) (hτT : MapsTo τ s T) (hreg : D.regular ∈ 𝓝 (τ x))
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)}
    (hW : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (W q)) s x)
    (hZ : ContMDiffWithinAt J (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q => TotalSpace.mk' E (U q) (Z q)) s x) :
    ContMDiffWithinAt J 𝓘(ℝ, ℝ) ∞
      (fun q => (Diffeomorph.pullbackMetric (G (τ q)) (Φ (τ q))).inner (U q) (W q) (Z q)) s x := by
  have hbase := (hΦ _ ⟨ht, mem_univ _⟩).comp x (hτ.prodMk hU)
    (fun q hq => ⟨hτT hq, trivial⟩)
  have htan := contMDiffOn_parameter_tangentMap_of_uniqueDiffOn hT hΦ
  have hw := (htan (τ x, TotalSpace.mk' E (U x) (W x)) ⟨ht, mem_univ _⟩).comp
    (f := fun q => (τ q, TotalSpace.mk' E (U q) (W q))) x
    (hτ.prodMk hW) (fun q hq => ⟨hτT hq, mem_univ _⟩)
  have hz := (htan (τ x, TotalSpace.mk' E (U x) (Z x)) ⟨ht, mem_univ _⟩).comp
    (f := fun q => (τ q, TotalSpace.mk' E (U q) (Z q))) x
    (hτ.prodMk hZ) (fun q hq => ⟨hτT hq, mem_univ _⟩)
  have h := contMDiffWithinAt_metricFamilySectionPairing hG hτ hbase hreg hw hz
  convert h using 1
  ext q
  exact Diffeomorph.pullbackMetric_inner (G (τ q)) (Φ (τ q)) (U q) (W q) (Z q)

end DifferentialGeometry.Geometry

end

end
