import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Ims05RadiusHC2IM6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.SurvivorConfinementIM6

/-!
# c3 ⇒ IMS06′ ⇒ c5：`_HC2` 盘的 survivor confinement（O-W-IMS06 G2 第 2 部分，后缀 `_IM6`）

把 G1（c3，`ims05_radius_bound_HC2_IM6`）、S-W-NECK G4（IMS06′：不碰中间球面）与 G2 的分离引理
（`confined_in_survivor_of_neck_exclusion_IM6`）串起来：开子流形 `U` 上的 Morrey 盘 `q`
（`_HC2` 形：`IsMorreyDisk G γU q` + locality `G = g` near `q`）的 ambient 像 `ι ∘ q`
落在 `K₀` 里。

显式前提（均为尚未到的输入，到后收缩）：
* `hlam`：共形 IMS05′（`lam` 形，σ = 1/2；S-W-STAB/S-W-EIG/O-W-GEO-MIN 合成，见 G1）；
* `hNECK`：逐 neck 的 "IMS05′ 结论（NECK G4 的 `hIMS05` 形状）⇒ 不碰中间球面"，即
  `not_mem_middle_sphere_of_stability_bound_NK` 吃掉 c4（S-W-NECK G5：pre-surgery 时刻的 band 估计
  `hN hZ hcl hdz hR`）与 `htrace` 之后的形状；
* `hsep`、`hUK`、`hγ`：R3 分离事实（S-A14-SURGERY 认领）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.MinimalSurface
open GC.LongTime
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℝ, E) ∞ X] [T2Space X]

/-- **c3 ⇒ IMS06′ ⇒ c5**：`_HC2` 形 Morrey 盘的像 `ι ∘ q` 落在 `K₀`。 -/
theorem confined_of_ims05_HC2_IM6 (g : SmoothRiemannianMetric 𝓘(ℝ, E) X)
    {U : TopologicalSpace.Opens X} (G : SmoothRiemannianMetric 𝓘(ℝ, E) U)
    {γU : freeLoop U} {q : C(closedDisk, U)} (hMor : IsMorreyDisk G γU q)
    (hloc : ∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z), G.inner y = (g.restrictOpen U).inner y)
    (hlam : ∀ (d : ℂ → ℝ≥0∞) (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
      0 < (1 / 2 : ℝ) → d z₀ = 0 →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, d y ≤ d x +
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (diskConformalFactor_IM6 g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) (x + t • (y - x))) *
            ‖y - x‖)) →
      IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ d z ≤ ENNReal.ofReal r} →
      (∃ z ∈ Metric.ball (0 : ℂ) 1, d z = ENNReal.ofReal r) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, d z ≤ ENNReal.ofReal r →
        ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
      r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))))
    {ι : Type*} (N : ι → Set X) (Z : ι → X → ℝ)
    (hNECK : ∀ b, (∀ (z₀ : ℂ) (r : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < r →
        IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧ diskEDist_NK g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z ≤ ENNReal.ofReal r} →
        (∃ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z = ENNReal.ofReal r) →
        (∀ z ∈ Metric.ball (0 : ℂ) 1, diskEDist_NK g
          ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z₀ z ≤ ENNReal.ofReal r →
          ∀ᶠ w in 𝓝 z, 1 / 2 ≤ metricScalarAt g (diskExtension
            ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) w)) →
        r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
      ∀ ζ : closedDisk, ¬ (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ζ ∈ N b ∧
        Z b (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ζ) = 0))
    {Us V K₀ : Set X} {γ : freeLoop X} (hUs : IsOpen Us) (hV : IsOpen V) (hUV : Disjoint Us V)
    (hsep : ∀ x, (∀ b, ¬ (x ∈ N b ∧ Z b x = 0)) → x ∈ Us ∪ V) (hUK : Us ⊆ K₀)
    (hγ : ∀ θ, γ θ ∈ Us)
    (htr : DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q)) :
    range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ K₀ :=
  confined_in_survivor_of_neck_exclusion_IM6 _ N Z hUs hV hUV hsep hUK hγ htr fun b =>
    hNECK b (ims05_radius_bound_HC2_IM6 g G hMor hloc (by norm_num) hlam)

end GC.LongTime.CuspP1
