import DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz
import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianLoopEDist_ne_top (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : (⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ)) ≠ ⊤ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  change (⨆ θ, edist (γ₀ θ) (γ₁ θ)) ≠ ⊤
  rw [← ContinuousMap.edist_eq_iSup]
  exact edist_ne_top _ _


def riemannianLoopDistance (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : ℝ≥0 := (⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toNNReal

theorem riemannianLoopDistance_coe (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) :
    (riemannianLoopDistance g γ₀ γ₁ : ℝ≥0∞) = ⨆ θ, riemannianEDistOf g (γ₀ θ) (γ₁ θ) :=
  ENNReal.coe_toNNReal (riemannianLoopEDist_ne_top g γ₀ γ₁)

theorem riemannianEDist_le_loopDistance (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) (θ : loopCircle) :
    riemannianEDistOf g (γ₀ θ) (γ₁ θ) ≤ (riemannianLoopDistance g γ₀ γ₁ : ℝ≥0∞) := by
  rw [riemannianLoopDistance_coe]
  exact le_iSup (fun t => riemannianEDistOf g (γ₀ t) (γ₁ t)) θ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianLoopDistance_eq_iSup (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) :
    (riemannianLoopDistance g γ₀ γ₁ : ℝ) = ⨆ θ, (riemannianEDistOf g (γ₀ θ) (γ₁ θ)).toReal := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hnn : riemannianLoopDistance g γ₀ γ₁ = nndist γ₀ γ₁ := by
    unfold riemannianLoopDistance
    change (⨆ θ, edist (γ₀ θ) (γ₁ θ)).toNNReal = nndist γ₀ γ₁
    rw [← ContinuousMap.edist_eq_iSup, edist_nndist, ENNReal.toNNReal_coe]
  rw [hnn]
  change dist γ₀ γ₁ = ⨆ θ, (edist (γ₀ θ) (γ₁ θ)).toReal
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using!
    (ContinuousMap.dist_eq_iSup (f := γ₀) (g := γ₁))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem riemannianLoopDistance_symm (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : freeLoop M) : riemannianLoopDistance g γ₀ γ₁ = riemannianLoopDistance g γ₁ γ₀ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  unfold riemannianLoopDistance
  congr 1
  apply iSup_congr
  intro θ
  exact edist_comm (γ₀ θ) (γ₁ θ)

end DifferentialGeometry.Geometry
