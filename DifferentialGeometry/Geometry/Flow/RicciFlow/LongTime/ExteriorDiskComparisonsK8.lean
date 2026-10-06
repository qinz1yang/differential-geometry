import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskComparisons
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskComparisonK8

/-!
# IMS08 kernel，G4：`hasExteriorDiskComparisonsAfter` 由显式 transport data 得到（S-A14-KERNEL）

对每个 `t₀ ≥ T`、`ε > 0`，存在 `δ > 0`，使 `T ≤ t`、`|t - t₀| < δ` 时有一对 smooth 映射
`φ : (postStage O t₀).Carrier → (postStage O t).Carrier` 与反向 `ψ`，各满足 G1 + G2 的逐点性质
（相对 `W t₀ / W t`、`γ t₀ / γ t`，metric 常数 `exp ε`）。结论即
`hasExteriorDiskComparisonsAfter O W T γ`（定义见 `ExteriorDiskComparisons.lean`）。
Consumer：`continuousOn_exteriorDiskArea_of_transport_K8`，把结论喂给
`continuousOn_exteriorDiskArea_of_local_comparisons`。
运输数据用显式函数 + 性质参数，不打包新 structure；O-IFACE 冻结形状后另文件 `example` 对齐。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

section Transport

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  (O : ObservationTower P g) (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
  (htransport : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ (t : ℝ) (ht : T ≤ t), |t - t₀| < δ →
      (∃ (φ : (postStage O t₀).Carrier → (postStage O t).Carrier)
          (V : Set (postStage O t₀).Carrier), IsOpen V ∧ W t₀ ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V ∧ InjOn φ (W t₀) ∧
        (∀ p ∈ W t₀, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ p)) ∧
        MapsTo φ (W t₀) (W t) ∧ MapsTo φ (interior (W t₀)) (interior (W t)) ∧
        MapsTo φ (frontier (W t₀)) (frontier (W t)) ∧
        (∀ θ, φ (γ t₀ ht₀ θ) = γ t ht θ) ∧
        ∀ p ∈ W t₀, ∀ w : TangentSpace (𝓡 3) p,
          (postMetric O t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
              (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
            Real.exp ε * (postMetric O t₀).inner p w w) ∧
      (∃ (ψ : (postStage O t).Carrier → (postStage O t₀).Carrier)
          (V : Set (postStage O t).Carrier), IsOpen V ∧ W t ⊆ V ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ V ∧ InjOn ψ (W t) ∧
        (∀ p ∈ W t, Function.Injective (mfderiv (𝓡 3) (𝓡 3) ψ p)) ∧
        MapsTo ψ (W t) (W t₀) ∧ MapsTo ψ (interior (W t)) (interior (W t₀)) ∧
        MapsTo ψ (frontier (W t)) (frontier (W t₀)) ∧
        (∀ θ, ψ (γ t ht θ) = γ t₀ ht₀ θ) ∧
        ∀ p ∈ W t, ∀ w : TangentSpace (𝓡 3) p,
          (postMetric O t₀).inner (ψ p) (mfderiv (𝓡 3) (𝓡 3) ψ p w)
              (mfderiv (𝓡 3) (𝓡 3) ψ p w) ≤
            Real.exp ε * (postMetric O t).inner p w w))

include htransport

/-- G4 主定理：显式 transport data ⇒ `hasExteriorDiskComparisonsAfter`。 -/
theorem hasExteriorDiskComparisonsAfter_of_transport_K8 :
    hasExteriorDiskComparisonsAfter O W T γ := by
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, hd⟩ := htransport t₀ ht₀ ε hε
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  have h := hcomparison_of_transport_K8 (fun t => (postStage O t).Carrier) (postMetric O) W T γ
    t₀ ht₀ ε δ (fun t ht h => (hd t ht h).1) (fun t ht h => (hd t ht h).2) t ht hdist
  simpa only [exteriorDiskArea_eq O W T γ t₀ ht₀, exteriorDiskArea_eq O W T γ t ht] using h

/-- Consumer：minimizers 存在 + 显式 transport data ⇒ `exteriorDiskArea` 在 `Ici T` 上连续。 -/
theorem continuousOn_exteriorDiskArea_of_transport_K8
    (hmin : hasExteriorDiskMinimizersAfter O W T γ) :
    ContinuousOn (exteriorDiskArea O W T γ) (Ici T) :=
  continuousOn_exteriorDiskArea_of_local_comparisons O W T γ hmin
    (hasExteriorDiskComparisonsAfter_of_transport_K8 O W T γ htransport)

end Transport

end GC.LongTime

end
