import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredSchoenfliesR13
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredNotTransverseR13

/-!
# O-MY-R13 G5 consumer：R13 本体只剩 cornered straightening（G3）

把 G5（`bilipschitz_schoenflies_seam_of_straightening_R13`，由 straightening 数据拼出 `B`）
接到 G6b（`IsMorreyDisk.not_transverse_cornered_of_schoenflies_R13`）：
R13 的前提（MYD2 `not_transverse_cornered_MYD2` 的 `h₁ h₂ hsub hb hbij hbpw hfb ht₀ hbt₀`）
加上两个 cornered 子盘在指定点的 bi-Lipschitz straightening `F₁ F₂`（G3 的输出形，开邻域光滑版）
⇒ `(dU_{b w}, −dU_w)` 不满射。于是 R13 只差 G3（cornered disk 的 bi-Lipschitz straightening，
在指定非 corner 边界点的开邻域上 `C^∞`、`fderiv` 单射）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry Complex
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- **R13（以 straightening 为输入）。**  MYD2 R13 的几何前提（cornered `Ω₁ Ω₂ ⊆ D°`，bi-Lipschitz
边界配对 `b`，`U ∘ b = U`，`b ∘ c₂` 分段光滑且在 `t₀` 光滑，`t₀` 非 corner）加上 straightening：
`F₂ : D̄ → Ω₂` 在 `ξ₂`（`F₂ ξ₂ = c₂ t₀`）的开邻域上光滑、`F₁ : D̄ → Ω₁` 在 `ξ₁`（`F₁ ξ₁ = b (c₂ t₀)`）的
开邻域上光滑（两者 bi-Lipschitz 双射、边界对边界、`fderiv` 单射）⇒ `(dU_{b w}, −dU_w)` 不满射。 -/
theorem IsMorreyDisk.not_transverse_cornered_of_straightening_R13
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (hiU : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hdim : Module.finrank ℝ E = 3)
    {Ω₁ Ω₂ : Set ℂ} {c₁ c₂ : ℝ → ℂ} {C₁ C₂ : Finset ℝ}
    (h₁ : IsCorneredJordanDisk_R13 Ω₁ c₁ C₁) (h₂ : IsCorneredJordanDisk_R13 Ω₂ c₂ C₂)
    (hsub₁ : Ω₁ ⊆ Metric.ball (0 : ℂ) 1) (hsub₂ : Ω₂ ⊆ Metric.ball (0 : ℂ) 1)
    {b : ℂ → ℂ} (hb : BilipschitzOn_R13 b (frontier Ω₂))
    (hbij : BijOn b (frontier Ω₂) (frontier Ω₁))
    (hbpw : ∃ Cb : Finset ℝ, ∀ t, (∀ s ∈ Cb, ∀ m : ℤ, t ≠ s + m) → ContDiffAt ℝ ∞ (b ∘ c₂) t)
    (hfb : ∀ w ∈ frontier Ω₂, diskExtension u (b w) = diskExtension u w)
    {t₀ : ℝ} (ht₀ : ∀ s ∈ C₂, ∀ m : ℤ, t₀ ≠ s + m) (hbt₀ : ContDiffAt ℝ ∞ (b ∘ c₂) t₀)
    {F₁ : ℂ → ℂ} (hF₁ : BilipschitzOn_R13 F₁ (Metric.closedBall 0 1))
    (hF₁b : BijOn F₁ (Metric.closedBall 0 1) Ω₁)
    (hF₁s : BijOn F₁ (Metric.sphere 0 1) (frontier Ω₁))
    {ξ₁ : ℂ} (hξ₁ : ξ₁ ∈ Metric.sphere (0 : ℂ) 1) (hF₁ξ : F₁ ξ₁ = b (c₂ t₀))
    {V₁ : Set ℂ} (hV₁ : IsOpen V₁) (hξV₁ : ξ₁ ∈ V₁) (hF₁sm : ContDiffOn ℝ ∞ F₁ V₁)
    (hF₁i : ∀ z ∈ V₁, Function.Injective (fderiv ℝ F₁ z))
    {F₂ : ℂ → ℂ} (hF₂ : BilipschitzOn_R13 F₂ (Metric.closedBall 0 1))
    (hF₂b : BijOn F₂ (Metric.closedBall 0 1) Ω₂)
    (hF₂s : BijOn F₂ (Metric.sphere 0 1) (frontier Ω₂))
    {ξ₂ : ℂ} (hξ₂ : ξ₂ ∈ Metric.sphere (0 : ℂ) 1) (hF₂ξ : F₂ ξ₂ = c₂ t₀)
    {V₂ : Set ℂ} (hV₂ : IsOpen V₂) (hξV₂ : ξ₂ ∈ V₂) (hF₂sm : ContDiffOn ℝ ∞ F₂ V₂)
    (hF₂i : ∀ z ∈ V₂, Function.Injective (fderiv ℝ F₂ z)) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (b (c₂ t₀))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (c₂ t₀)))) := by
  obtain ⟨B, hB, hBK, hBb, δ, hδ, hBs, hBi⟩ :=
    bilipschitz_schoenflies_seam_of_straightening_R13 h₂ hb hbij hbpw ht₀ hbt₀
      hF₁ hF₁b hF₁s hξ₁ hF₁ξ hV₁ hξV₁ hF₁sm hF₁i hF₂ hF₂b hF₂s hξ₂ hF₂ξ hV₂ hξV₂ hF₂sm hF₂i
  exact hu.not_transverse_cornered_of_schoenflies_R13 hUext hiU hdim h₁ h₂ hsub₁ hsub₂ hbij hfb
    ht₀ hB hBK hBb hδ hBs hBi

end DifferentialGeometry.Geometry
