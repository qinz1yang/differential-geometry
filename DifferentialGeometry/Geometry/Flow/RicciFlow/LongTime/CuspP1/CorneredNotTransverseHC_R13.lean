import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredNotTransverseR13

/-!
# O-MY-R13 G6c consumer：`_HC2` 的 (U, G) 上的 R13（cornered paired source disks 不横截）

`IsMorreyDisk.not_transverse_cornered_of_schoenflies_R13`（`Plateau/CorneredNotTransverseR13`）
在 `_HC2`（`exists_eventual_confined_morrey_disk_HC2` 的 clause）的 target `U = {ρ < a}` 与 metric
`G = canonicalPositiveDomainMetric_P2A …` 上的实例：binder 前缀（`t a ha ρ hρ`，`let U δ hδ hU G`）与
R4B / R4C 的 `_HC2` 文件逐字相同；`dim = 3` 由 `finrank_euclideanSpace_fin` 给出。几何输入的形状按外审
R-MY3 的 R14 几何包：non-cusp cornered Jordan 子盘 `Ω₁ Ω₂`、bi-Lipschitz 边界配对 `b`（`U ∘ b = U`）、选定的
非 corner regular seam 参数 `t₀`；再加 R13-S 的 Schoenflies 映射 `B`（G3–G5 交付后由其给出）。

* **`not_transverse_cornered_of_schoenflies_HC2_R13`**：`q` 是 `γU` 的 `IsMorreyDisk`（在 `G` 下）⇒
  `(dq_{b w}, −dq_w)` 不满射。
* `example`：R13 的矛盾形（横截 ⇒ `False`）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology NNReal ENNReal ComplexConjugate

namespace GC.LongTime.CuspP1

universe u

/-- **R13 在 `_HC2` 的 (U, G) 上（以 R13-S 的 `B` 为输入）。**  `q` 是 `γU` 的 Morrey 盘、`D°` 上 immersed；
`Ω₁ Ω₂ ⊆ D°` 是 cornered Jordan 子盘（允许相交 / 相等），`b : ∂Ω₂ → ∂Ω₁` 双射且 `q̂ ∘ b = q̂`；`t₀` 不是
`Ω₂` 的 corner；`B : Ω₂ → Ω₁` bi-Lipschitz 双射、`B = b` on `∂Ω₂`、在 `w = c₂ t₀` 附近 `Ω₂` 一侧 `C^∞`
且 `fderivWithin` 单射。则 `(dq̂_{b w}, −dq̂_w)` 不满射。 -/
theorem not_transverse_cornered_of_schoenflies_HC2_R13
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ {Uext : ℂ → U}, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Uext →
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) z)) →
    ∀ {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ} {C₁ C₂ : Finset ℝ},
    IsCorneredJordanDisk_R13 Ω₁ c₁ C₁ → IsCorneredJordanDisk_R13 Ω₂ c₂ C₂ →
    Ω₁ ⊆ Metric.ball (0 : ℂ) 1 → Ω₂ ⊆ Metric.ball (0 : ℂ) 1 →
    ∀ {b : ℂ → ℂ}, BijOn b (frontier Ω₂) (frontier Ω₁) →
    (∀ w ∈ frontier Ω₂, diskExtension q (b w) = diskExtension q w) →
    ∀ {t₀ : ℝ}, (∀ s ∈ C₂, ∀ m : ℤ, t₀ ≠ s + m) →
    ∀ {B : ℂ → ℂ}, BilipschitzOn_R13 B Ω₂ → BijOn B Ω₂ Ω₁ → EqOn B b (frontier Ω₂) →
    ∀ {δ' : ℝ}, 0 < δ' → ContDiffOn ℝ ∞ B (Metric.ball (c₂ t₀) δ' ∩ Ω₂) →
    (∀ z ∈ Metric.ball (c₂ t₀) δ' ∩ Ω₂, Function.Injective (fderivWithin ℝ B Ω₂ z)) →
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
        mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) (b (c₂ t₀))).coprod
        (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
          mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) (c₂ t₀)))) := by
  intro U δ hδ hU G γU q hq Uext hUext hiU Ω₁ Ω₂ c₁ c₂ C₁ C₂ h₁ h₂ hsub₁ hsub₂ b hbij hfb t₀
    ht₀ B hB hBK hBb δ' hδ' hBs hBi
  exact hq.not_transverse_cornered_of_schoenflies_R13 hUext hiU finrank_euclideanSpace_fin h₁ h₂
    hsub₁ hsub₂ hbij hfb ht₀ hB hBK hBb hδ' hBs hBi

/-- **Consumer（R13 的矛盾形）。**  同上前提下，若 `(dq̂_{b w}, −dq̂_w)` 满射（`w` 处两切平面横截），则
`False`。直接使用 `not_transverse_cornered_of_schoenflies_HC2_R13`。 -/
example
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)), IsMorreyDisk G γU q →
    ∀ {Uext : ℂ → U}, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Uext →
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) z)) →
    ∀ {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ} {C₁ C₂ : Finset ℝ},
    IsCorneredJordanDisk_R13 Ω₁ c₁ C₁ → IsCorneredJordanDisk_R13 Ω₂ c₂ C₂ →
    Ω₁ ⊆ Metric.ball (0 : ℂ) 1 → Ω₂ ⊆ Metric.ball (0 : ℂ) 1 →
    ∀ {b : ℂ → ℂ}, BijOn b (frontier Ω₂) (frontier Ω₁) →
    (∀ w ∈ frontier Ω₂, diskExtension q (b w) = diskExtension q w) →
    ∀ {t₀ : ℝ}, (∀ s ∈ C₂, ∀ m : ℤ, t₀ ≠ s + m) →
    ∀ {B : ℂ → ℂ}, BilipschitzOn_R13 B Ω₂ → BijOn B Ω₂ Ω₁ → EqOn B b (frontier Ω₂) →
    ∀ {δ' : ℝ}, 0 < δ' → ContDiffOn ℝ ∞ B (Metric.ball (c₂ t₀) δ' ∩ Ω₂) →
    (∀ z ∈ Metric.ball (c₂ t₀) δ' ∩ Ω₂, Function.Injective (fderivWithin ℝ B Ω₂ z)) →
    Function.Surjective
      ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
        mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) (b (c₂ t₀))).coprod
        (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
          mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) (c₂ t₀)))) → False := by
  intro U δ hδ hU G γU q hq Uext hUext hiU Ω₁ Ω₂ c₁ c₂ C₁ C₂ h₁ h₂ hsub₁ hsub₂ b hbij hfb t₀
    ht₀ B hB hBK hBb δ' hδ' hBs hBi htrans
  exact not_transverse_cornered_of_schoenflies_HC2_R13 t a ha ρ hρ γU q hq hUext hiU h₁ h₂
    hsub₁ hsub₂ hbij hfb ht₀ hB hBK hBb hδ' hBs hBi htrans

end GC.LongTime.CuspP1
