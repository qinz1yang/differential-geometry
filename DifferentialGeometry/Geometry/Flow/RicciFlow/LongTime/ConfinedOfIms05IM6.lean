import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SurvivorConfinementIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.NeckMiddleSphereNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HtLeftCriterionIM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.DiskDistScaleIM6

/-!
# c5 直接吃 NECK 形 `hIMS05`（任意度量 `g′`）（O-W-IMS06 G8 第 2 部分，后缀 `_IM6`）

G6/G7 现在直接产出 S-W-NECK G4 形的 `hIMS05`（不再经 G1 的 `lam` 形 `hlam`），G8 的缩放引理把它从
`g_post` 搬到 S-W-TOPGLUE 的归一化 slice 度量 `g′ = (r²)⁻¹ g_post`。本文件的 c5 以任意度量 `g′`
陈述：盘 `v` 开盘内光滑、`hIMS05(g′, v)`、逐 neck band 数据（`g′` 下）、`γ` 不进 band 闭包、R3 ⇒
`range v ⊆ K₀`。度量只出现在 IMS06′ 内部；c5 的拓扑部分与度量无关。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X]

/-- **c5（NECK 形 `hIMS05` 版，任意度量 `g′`）**。 -/
theorem confined_of_neck_bands_of_ims05_IM6 (g' : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {v : C(closedDisk, X)} (hv : DiskSmoothInterior (E := E) v)
    (hIMS05 : ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g' v z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g' v z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g' v z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g' (diskExtension v w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))))
    {ι : Type*} (N : ι → Set X) (Z : ι → X → ℝ) (hN : ∀ b, IsOpen (N b))
    (hZ : ∀ b, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (Z b) (N b))
    (hcl : ∀ b, closure {p : X | p ∈ N b ∧ |Z b p| < 20} ⊆ N b)
    (hdz : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (Z b) p w) ^ 2 ≤ 4 * g'.inner p w w)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt g' p)
    {γ : freeLoop X} (htr : DiskWeakJordanTrace γ v)
    (hγband : ∀ b θ, γ θ ∉ closure {p : X | p ∈ N b ∧ |Z b p| < 20})
    {Us V K₀ : Set X} (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ Us) : range v ⊆ K₀ :=
  confined_in_survivor_of_neck_exclusion_IM6 v N Z hUs hV hUV hsep hUK hγ htr fun b =>
    not_mem_middle_sphere_of_stability_bound_NK g' hv (hN b) (hZ b) (hcl b) (hdz b) (hR b)
      (GC.LongTime.CuspP1.diskTrace_not_mem_of_weakTrace_IM6 htr (hγband b)) hIMS05

/-- consumer / 串联：c3 在 `g` 下对一切 `σ > 0` 的 `hIMS05`（G6/G7 的输出形）+ G8 缩放 ⇒ 归一化度量
`g′ = c • g`（TOPGLUE：`c = (r²)⁻¹`）下的 band 数据 + R3 ⇒ `range v ⊆ K₀`。 -/
theorem confined_of_scaled_ims05_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X) (c : ℝ) (hc : 0 < c)
    {v : C(closedDisk, X)} (hv : DiskSmoothInterior (E := E) v)
    (hg : ∀ σ : ℝ, 0 < σ → ∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
        diskEDist_NK g v z₀ z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g v z₀ z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g v z₀ z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, σ ≤ metricScalarAt g (diskExtension v w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * σ)))
    {ι : Type*} (N : ι → Set X) (Z : ι → X → ℝ) (hN : ∀ b, IsOpen (N b))
    (hZ : ∀ b, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 (Z b) (N b))
    (hcl : ∀ b, closure {p : X | p ∈ N b ∧ |Z b p| < 20} ⊆ N b)
    (hdz : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (Z b) p w) ^ 2 ≤
        4 * (scaleMetric c hc g).inner p w w)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt (scaleMetric c hc g) p)
    {γ : freeLoop X} (htr : DiskWeakJordanTrace γ v)
    (hγband : ∀ b θ, γ θ ∉ closure {p : X | p ∈ N b ∧ |Z b p| < 20})
    {Us V K₀ : Set X} (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ Us) : range v ⊆ K₀ :=
  confined_of_neck_bands_of_ims05_IM6 (scaleMetric c hc g) hv
    (ims05_radius_bound_scale_IM6 c hc g hg (σ := 1 / 2) (by norm_num)) N Z hN hZ hcl hdz hR
    htr hγband hUs hV hUV hsep hUK hγ

end GC.LongTime
