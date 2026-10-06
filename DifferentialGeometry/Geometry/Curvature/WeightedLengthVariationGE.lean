import DifferentialGeometry.Geometry.Curvature.WeightedLengthSliceGE
import DifferentialGeometry.Analysis.Calculus.ParamVariationGE
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# 平面加权长度的一阶 / 二阶变分（向量场形式；S-W-GEO G2）

`ρ : ℂ → ℝ` 在开集 `W` 上 `C²`，`c : ℝ → ℂ` 是 `C¹` 的正则曲线（`c′ ≠ 0` 在 `[0, L]` 上，`c([0, L]) ⊆ W`），
`c` 在 `W` 内的 `C¹` 曲线类里极小（固定端点）：

`ℓ(c) = ∫₀ᴸ ρ(c) ‖c′‖ ds ≤ ℓ(η)`，`η` 为 `C¹`、`η([0,L]) ⊆ W`、`η(0) = c(0)`、`η(L) = c(L)`。

对任意 `C¹` 向量场 `X : ℝ → ℂ`（`X(0) = X(L) = 0`）：

* `∫₀ᴸ [Dρ(c)(X) ‖c′‖ + ρ(c) ⟪c′, X′⟫/‖c′‖] ds = 0`（一阶变分）；
* `0 ≤ ∫₀ᴸ [D²ρ(c)(X, X) ‖c′‖ + 2 Dρ(c)(X) ⟪c′, X′⟫/‖c′‖ + ρ(c)(‖X′‖² − (⟪c′, X′⟫/‖c′‖)²)/‖c′‖] ds`
  （二阶变分）。

**不需要 `c ∈ C²`，也不需要测地线方程 / 正则性定理**：只对 `ε ↦ ℓ(c + εX)` 做逐点中值估计（
`Analysis/Calculus/ParamVariationGE`）。
-/

set_option autoImplicit false
noncomputable section

open Set intervalIntegral
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Analysis

/-- 变分窗口：存在 `ε₀ > 0`，`|t| ≤ ε₀` 时 `c + tX` 仍在 `W` 内、`c′ + tX′ ≠ 0`（紧致性）。 -/
theorem exists_variation_window_GE {W : Set ℂ} (hW : IsOpen W) {c X : ℝ → ℂ} {L : ℝ}
    (hc : ContDiff ℝ 1 c) (hX : ContDiff ℝ 1 X)
    (hcW : ∀ s ∈ Icc 0 L, c s ∈ W) (hreg : ∀ s ∈ Icc 0 L, deriv c s ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ Icc (-ε₀) ε₀, ∀ s ∈ Icc 0 L,
      c s + t • X s ∈ W ∧ deriv c s + t • deriv X s ≠ 0 := by
  have hcd : Continuous (deriv c) := hc.continuous_deriv le_rfl
  have hXd : Continuous (deriv X) := hX.continuous_deriv le_rfl
  have hq : Continuous fun p : ℝ × ℝ => c p.2 + p.1 • X p.2 :=
    (hc.continuous.comp continuous_snd).add
      (continuous_fst.smul (hX.continuous.comp continuous_snd))
  have hr : Continuous fun p : ℝ × ℝ => deriv c p.2 + p.1 • deriv X p.2 :=
    (hcd.comp continuous_snd).add (continuous_fst.smul (hXd.comp continuous_snd))
  have hN : IsOpen {p : ℝ × ℝ | c p.2 + p.1 • X p.2 ∈ W ∧ deriv c p.2 + p.1 • deriv X p.2 ≠ 0} :=
    (hW.preimage hq).inter (isClosed_singleton.isOpen_compl.preimage hr)
  have hK0 : IsCompact (({0} : Set ℝ) ×ˢ Icc (0 : ℝ) L) := isCompact_singleton.prod isCompact_Icc
  have hsub : ({0} : Set ℝ) ×ˢ Icc (0 : ℝ) L ⊆
      {p : ℝ × ℝ | c p.2 + p.1 • X p.2 ∈ W ∧ deriv c p.2 + p.1 • deriv X p.2 ≠ 0} := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht0 : t = 0 := ht
    subst ht0
    simp only [mem_ofPred_eq, zero_smul, add_zero]
    exact ⟨hcW s hs, hreg s hs⟩
  obtain ⟨δ, hδ, hth⟩ := hK0.exists_thickening_subset_open hN hsub
  refine ⟨δ / 2, by positivity, fun t ht s hs => ?_⟩
  have hmem : (t, s) ∈ Metric.thickening δ (({0} : Set ℝ) ×ˢ Icc (0 : ℝ) L) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(0, s), ⟨rfl, hs⟩, ?_⟩
    rw [Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero, sub_self, abs_zero]
    refine max_lt ?_ hδ
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  exact hth hmem

/-- `wlF / wlG1 / wlG2` 沿 `(ε, s)` 的连续性（窗口 `[−ε₀, ε₀] × [0, L]` 上）。 -/
theorem wl_continuity_GE {W : Set ℂ} (hW : IsOpen W) {ρ : ℂ → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ W) {c X : ℝ → ℂ} {L ε₀ : ℝ}
    (hc : ContDiff ℝ 1 c) (hX : ContDiff ℝ 1 X)
    (hwin : ∀ t ∈ Icc (-ε₀) ε₀, ∀ s ∈ Icc 0 L,
      c s + t • X s ∈ W ∧ deriv c s + t • deriv X s ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => wlG1 ρ (c p.2) (X p.2) (deriv c p.2) (deriv X p.2) p.1)
      (Icc (-ε₀) ε₀ ×ˢ Icc 0 L) ∧
    ContinuousOn (fun p : ℝ × ℝ => wlG2 ρ (c p.2) (X p.2) (deriv c p.2) (deriv X p.2) p.1)
      (Icc (-ε₀) ε₀ ×ˢ Icc 0 L) ∧
    ∀ ε ∈ Icc (-ε₀) ε₀,
      ContinuousOn (fun s => wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε) (Icc 0 L) := by
  have hcd : Continuous (deriv c) := hc.continuous_deriv le_rfl
  have hXd : Continuous (deriv X) := hX.continuous_deriv le_rfl
  have hcc : Continuous c := hc.continuous
  have hXc : Continuous X := hX.continuous
  set K : Set (ℝ × ℝ) := Icc (-ε₀) ε₀ ×ˢ Icc 0 L with hK
  have hΦ : Continuous fun p : ℝ × ℝ => c p.2 + p.1 • X p.2 := by fun_prop
  have hΦW : ∀ p ∈ K, c p.2 + p.1 • X p.2 ∈ W := fun p hp => (hwin p.1 hp.1 p.2 hp.2).1
  have hXs : Continuous fun p : ℝ × ℝ => X p.2 := by fun_prop
  have hB : Continuous fun p : ℝ × ℝ => ‖deriv c p.2 + p.1 • deriv X p.2‖ := by fun_prop
  have hBne : ∀ p ∈ K, ‖deriv c p.2 + p.1 • deriv X p.2‖ ≠ 0 := fun p hp =>
    norm_ne_zero_iff.2 (hwin p.1 hp.1 p.2 hp.2).2
  have hM : Continuous fun p : ℝ × ℝ =>
      inner ℝ (deriv c p.2 + p.1 • deriv X p.2) (deriv X p.2) := by fun_prop
  have hA0 : ContinuousOn (fun p : ℝ × ℝ => ρ (c p.2 + p.1 • X p.2)) K :=
    hρ.continuousOn.comp hΦ.continuousOn hΦW
  have hA1 : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ ρ (c p.2 + p.1 • X p.2) (X p.2)) K :=
    ((hρ.continuousOn_fderiv_of_isOpen hW (by norm_num)).comp hΦ.continuousOn hΦW).clm_apply
      hXs.continuousOn
  have hA2 : ContinuousOn
      (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ ρ) (c p.2 + p.1 • X p.2) (X p.2) (X p.2)) K := by
    have hfd2 : ContinuousOn (fderiv ℝ (fderiv ℝ ρ)) W :=
      (hρ.fderiv_of_isOpen hW (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hW le_rfl
    exact (((hfd2.comp hΦ.continuousOn hΦW).clm_apply hXs.continuousOn).clm_apply
      hXs.continuousOn)
  have hB1 : ContinuousOn (fun p : ℝ × ℝ =>
      inner ℝ (deriv c p.2 + p.1 • deriv X p.2) (deriv X p.2) /
        ‖deriv c p.2 + p.1 • deriv X p.2‖) K :=
    hM.continuousOn.div hB.continuousOn hBne
  have hN2 : Continuous fun p : ℝ × ℝ => ‖deriv X p.2‖ ^ 2 := by fun_prop
  have hB2 : ContinuousOn (fun p : ℝ × ℝ =>
      (‖deriv X p.2‖ ^ 2 - (inner ℝ (deriv c p.2 + p.1 • deriv X p.2) (deriv X p.2) /
        ‖deriv c p.2 + p.1 • deriv X p.2‖) ^ 2) / ‖deriv c p.2 + p.1 • deriv X p.2‖) K :=
    (hN2.continuousOn.sub (hB1.pow 2)).div hB.continuousOn hBne
  refine ⟨?_, ?_, ?_⟩
  · exact (hA1.mul hB.continuousOn).add (hA0.mul hB1)
  · exact ((hA2.mul hB.continuousOn).add ((continuousOn_const.mul hA1).mul hB1)).add
      (hA0.mul hB2)
  · intro ε hε
    have hmaps : ∀ s ∈ Icc 0 L, c s + ε • X s ∈ W := fun s hs => (hwin ε hε s hs).1
    have hηc : Continuous fun s => c s + ε • X s := by fun_prop
    have h0 : ContinuousOn (fun s => ρ (c s + ε • X s)) (Icc 0 L) :=
      hρ.continuousOn.comp hηc.continuousOn hmaps
    have hn : Continuous fun s => ‖deriv c s + ε • deriv X s‖ := by fun_prop
    exact h0.mul hn.continuousOn

/-- 极小性转写：`c` 在 `W` 内 `C¹` 曲线类里极小 ⇒ `ε ↦ ∫ wlF` 在 `ε = 0` 处极小。 -/
theorem wl_minimality_GE {W : Set ℂ} {ρ : ℂ → ℝ} {c X : ℝ → ℂ} {L ε₀ : ℝ}
    (hc : ContDiff ℝ 1 c) (hX : ContDiff ℝ 1 X) (hX0 : X 0 = 0) (hXL : X L = 0)
    (hwin : ∀ t ∈ Icc (-ε₀) ε₀, ∀ s ∈ Icc 0 L,
      c s + t • X s ∈ W ∧ deriv c s + t • deriv X s ≠ 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ W) → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖) :
    ∀ ε ∈ Icc (-ε₀) ε₀, ∫ s in (0 : ℝ)..L, wlF ρ (c s) (X s) (deriv c s) (deriv X s) 0 ≤
      ∫ s in (0 : ℝ)..L, wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε := by
  have hdη : ∀ ε : ℝ, ∀ s, deriv (fun s => c s + ε • X s) s = deriv c s + ε • deriv X s := by
    intro ε s
    exact (((hc.differentiable one_ne_zero) s).hasDerivAt.add
      (((hX.differentiable one_ne_zero) s).hasDerivAt.const_smul ε)).deriv
  have hFeq : ∀ ε : ℝ, (∫ s in (0 : ℝ)..L, wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε) =
      ∫ s in (0 : ℝ)..L, ρ (c s + ε • X s) * ‖deriv (fun s => c s + ε • X s) s‖ := by
    intro ε
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [wlF, hdη ε s]
  intro ε hε
  rw [hFeq 0, hFeq ε]
  have hηd : ContDiff ℝ 1 fun s => c s + ε • X s := by fun_prop
  have := hmin (fun s => c s + ε • X s) hηd
    (fun s hs => (hwin ε hε s hs).1) (by simp [hX0]) (by simp [hXL])
  simpa using this

/-- 逐点的导数数据：`wlF' = wlG1`，`wlG1' = wlG2`（窗口内）。 -/
theorem wl_slice_derivs_GE {W : Set ℂ} (hW : IsOpen W) {ρ : ℂ → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ W) {c X : ℝ → ℂ} {L ε₀ : ℝ}
    (hwin : ∀ t ∈ Icc (-ε₀) ε₀, ∀ s ∈ Icc 0 L,
      c s + t • X s ∈ W ∧ deriv c s + t • deriv X s ≠ 0) :
    (∀ s ∈ Icc 0 L, ∀ t ∈ Icc (-ε₀) ε₀,
      HasDerivAt (fun ε => wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε)
        (wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) t) t) ∧
    (∀ s ∈ Icc 0 L, ∀ t ∈ Icc (-ε₀) ε₀,
      HasDerivAt (fun ε => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) ε)
        (wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) t) t) := by
  have hρ1 : ∀ z ∈ W, DifferentiableAt ℝ ρ z := fun z hz =>
    (hρ.contDiffAt (hW.mem_nhds hz)).differentiableAt (by norm_num)
  have hρ2 : ∀ z ∈ W, DifferentiableAt ℝ (fderiv ℝ ρ) z := fun z hz =>
    ((hρ.fderiv_of_isOpen hW (m := 1) (by norm_num)).contDiffAt (hW.mem_nhds hz)).differentiableAt
      (by norm_num)
  exact ⟨fun s hs t ht => hasDerivAt_wlF_GE (hρ1 _ (hwin t ht s hs).1) (hwin t ht s hs).2,
    fun s hs t ht => hasDerivAt_wlG1_GE (hρ1 _ (hwin t ht s hs).1) (hρ2 _ (hwin t ht s hs).1)
      (hwin t ht s hs).2⟩

/-- 联合连续的 `G(ε, s)` 在 `ε = 0` 处对 `s` 连续。 -/
theorem continuousOn_slice_zero_GE {G : ℝ → ℝ → ℝ} {L ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Icc (-ε₀) ε₀ ×ˢ Icc 0 L)) :
    ContinuousOn (fun s => G 0 s) (Icc 0 L) := by
  have h00 : ∀ s ∈ Icc 0 L, ((0 : ℝ), s) ∈ Icc (-ε₀) ε₀ ×ˢ Icc 0 L := fun s hs =>
    ⟨⟨by linarith, hε₀.le⟩, hs⟩
  have hpair : ContinuousOn (fun s : ℝ => ((0 : ℝ), s)) (Icc 0 L) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have := ContinuousOn.comp (g := fun p : ℝ × ℝ => G p.1 p.2) (f := fun s : ℝ => ((0 : ℝ), s))
    hG hpair h00
  exact this

/-- 向量场形式的一阶 / 二阶变分，`wlG1 / wlG2` 在 `ε = 0` 的写法。 -/
theorem weightedLength_variation_wl_GE {W : Set ℂ} (hW : IsOpen W) {ρ : ℂ → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ W) {c X : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ContDiff ℝ 1 c) (hX : ContDiff ℝ 1 X)
    (hcW : ∀ s ∈ Icc 0 L, c s ∈ W) (hreg : ∀ s ∈ Icc 0 L, deriv c s ≠ 0)
    (hX0 : X 0 = 0) (hXL : X L = 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ W) → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖) :
    IntervalIntegrable (fun s => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) 0)
        MeasureTheory.volume 0 L ∧
    IntervalIntegrable (fun s => wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) 0)
        MeasureTheory.volume 0 L ∧
    (∫ s in (0 : ℝ)..L, wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) 0) = 0 ∧
    0 ≤ ∫ s in (0 : ℝ)..L, wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) 0 := by
  obtain ⟨ε₀, hε₀, hwin⟩ := exists_variation_window_GE hW hc hX hcW hreg
  obtain ⟨hG1c, hG2c, hFc⟩ := wl_continuity_GE hW hρ hc hX hwin
  have hmin' := wl_minimality_GE hc hX hX0 hXL hwin hmin
  obtain ⟨h1, h2⟩ := wl_slice_derivs_GE hW hρ hwin
  have hc1 : ContinuousOn (fun s => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) 0) (Icc 0 L) :=
    continuousOn_slice_zero_GE
      (G := fun ε s => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) ε) hε₀ hG1c
  have hc2 : ContinuousOn (fun s => wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) 0) (Icc 0 L) :=
    continuousOn_slice_zero_GE
      (G := fun ε s => wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) ε) hε₀ hG2c
  refine ⟨hc1.intervalIntegrable_of_Icc hL, hc2.intervalIntegrable_of_Icc hL, ?_, ?_⟩
  · exact integral_first_eq_zero_GE
      (F := fun ε s => wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε)
      (G1 := fun ε s => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) ε) hL hε₀ h1 hG1c hFc hmin'
  · exact integral_second_nonneg_GE
      (F := fun ε s => wlF ρ (c s) (X s) (deriv c s) (deriv X s) ε)
      (G1 := fun ε s => wlG1 ρ (c s) (X s) (deriv c s) (deriv X s) ε)
      (G2 := fun ε s => wlG2 ρ (c s) (X s) (deriv c s) (deriv X s) ε) hL hε₀ h1 h2 hG2c hFc hmin'

/-- 向量场形式的一阶 / 二阶变分（见文件头；显式被积函数）。 -/
theorem weightedLength_variation_GE {W : Set ℂ} (hW : IsOpen W) {ρ : ℂ → ℝ}
    (hρ : ContDiffOn ℝ 2 ρ W) {c X : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hc : ContDiff ℝ 1 c) (hX : ContDiff ℝ 1 X)
    (hcW : ∀ s ∈ Icc 0 L, c s ∈ W) (hreg : ∀ s ∈ Icc 0 L, deriv c s ≠ 0)
    (hX0 : X 0 = 0) (hXL : X L = 0)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ W) → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρ (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρ (η s) * ‖deriv η s‖) :
    IntervalIntegrable (fun s => fderiv ℝ ρ (c s) (X s) * ‖deriv c s‖ +
        ρ (c s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖)) MeasureTheory.volume 0 L ∧
    IntervalIntegrable (fun s => fderiv ℝ (fderiv ℝ ρ) (c s) (X s) (X s) * ‖deriv c s‖ +
        2 * fderiv ℝ ρ (c s) (X s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) +
        ρ (c s) * ((‖deriv X s‖ ^ 2 - (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) ^ 2) /
          ‖deriv c s‖)) MeasureTheory.volume 0 L ∧
    (∫ s in (0 : ℝ)..L, (fderiv ℝ ρ (c s) (X s) * ‖deriv c s‖ +
        ρ (c s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖))) = 0 ∧
    0 ≤ ∫ s in (0 : ℝ)..L, (fderiv ℝ (fderiv ℝ ρ) (c s) (X s) (X s) * ‖deriv c s‖ +
        2 * fderiv ℝ ρ (c s) (X s) * (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) +
        ρ (c s) * ((‖deriv X s‖ ^ 2 - (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) ^ 2) /
          ‖deriv c s‖)) := by
  obtain ⟨h1, h2, h3, h4⟩ := weightedLength_variation_wl_GE hW hρ hL hc hX hcW hreg hX0 hXL hmin
  simp only [wlG1, wlG2, zero_smul, add_zero] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end DifferentialGeometry.Geometry
