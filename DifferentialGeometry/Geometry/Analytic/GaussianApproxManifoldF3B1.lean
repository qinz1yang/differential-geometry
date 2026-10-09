import DifferentialGeometry.Analysis.Analytic.GaussianTensorApproxF3B1
import DifferentialGeometry.Geometry.Analytic.ExtensionDataF3A
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic

/-!
# F3-b 的流形版接口：与 `AnalyticExtensionData_F3A` 对齐（S-MY-F3B1 G4，后缀 `_F3B1`）

R6b 骨架（design-F3-analytic §3）：`D : AnalyticExtensionData_F3A G P V`（`V` 有限维实内积空间）给出
analytic `embed : M → V` 与光滑延拓 `ext : V → V →L V →L ℝ`（`G = embed^* ext` 于 `P`）。本文件把
Euclidean 核心 `exists_analytic_approx_bilinear_F3B1` 接到这个数据上：

- `symmCLM_F3B1`、`AnalyticExtensionData_F3A.symmetrize_F3B1`：`ext` 在 `V` 上不一定对称（只在
  `embed(P)` 的切向上对称），`D.symmetrize_F3B1` 把 `ext` 换成 `(ext + ext^flip)/2`，数据不变（`G` 对称）
  而 `ext` 处处对称——F3-b (b4) 拼 `SmoothRiemannianMetric` 要用；
- **G4 `exists_analytic_ext_approx_F3B1`**：对任意紧 `K ⊆ V`，存在整函数列 `Hn : ℕ → V → V →L V →L ℝ`，
  `AnalyticOnNhd ℝ (Hn n) univ`（于是 `∀ x ∈ P, AnalyticAt ℝ (Hn n) (D.embed x)`，即
  `D.isAnalyticMetricOn_of_coeff_eq` 的 `hH`）、处处对称、`Hn n → sym(D.ext)` 的每阶 `iteratedFDeriv` 在 `K` 上
  一致、`D.ext` 正定于 `K` ⇒ eventually `Hn n` 正定于 `K`；
- `mapCInfConvergenceOnCompacts_of_tendstoUniformlyOn_F3B1`：把 `TendstoUniformlyOn`（逐阶）桥接成
  树里 `MapCInfConvergenceOnCompacts (interior K)`，供 (b3) 用
  `MapCInfConvergenceOnCompacts.tendstoUniformlyOn_iteratedFDeriv_comp_moving` 做拉回 `C^k` 收敛；
- consumer `isAnalyticMetricOn_of_approx_F3B1`：`Hn n` 经 `D.isAnalyticMetricOn_of_coeff_eq` 得
  `IsAnalyticMetricOn_F3A D.atlas P G'`。

剩余（F3A / R6b 总装，不在本文件）：(b3) `pullbackCoeff_F3A D.embed (Hn n)` 在 chart 的紧集上 `C^k` 收敛
到 `metricCoeff_F3A G`；(b4) `G_n = χ·(embed^* Hn) + (1-χ)·G`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Analysis.Analytic

namespace DifferentialGeometry.Geometry.Analytic

section Symmetrize

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- 对称化 `B ↦ (B + B^flip)/2`（`V →L V →L ℝ` 上的连续线性映射）。 -/
def symmCLM_F3B1 : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ (V →L[ℝ] V →L[ℝ] ℝ) +
    (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

variable {V}

theorem symmCLM_F3B1_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    symmCLM_F3B1 V B v w = (B v w + B w v) / 2 := by
  simp [symmCLM_F3B1, ContinuousLinearMap.flip_apply]
  ring

theorem symmCLM_F3B1_symm (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    symmCLM_F3B1 V B v w = symmCLM_F3B1 V B w v := by
  rw [symmCLM_F3B1_apply, symmCLM_F3B1_apply, add_comm]

theorem symmCLM_F3B1_self (B : V →L[ℝ] V →L[ℝ] ℝ) (v : V) :
    symmCLM_F3B1 V B v v = B v v := by
  rw [symmCLM_F3B1_apply]
  ring

end Symmetrize

section Data

variable {E M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **`ext` 的对称化**：`G` 对称 ⇒ 把 `D.ext` 换成 `(D.ext + D.ext^flip)/2`，其余数据不变，
`metricCoeff_eq` 仍成立（`pullbackCoeff` 对 `(ξ, η)` 对称化后等于 `metricCoeff` 的对称化 = 自身）。 -/
def AnalyticExtensionData_F3A.symmetrize_F3B1 {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {P : Set M}
    (D : AnalyticExtensionData_F3A G P V) : AnalyticExtensionData_F3A G P V where
  atlas := D.atlas
  isAnalyticCompatibleAtlas := D.isAnalyticCompatibleAtlas
  embed := D.embed
  isAnalyticFunOn_embed := D.isAnalyticFunOn_embed
  ext := fun x => symmCLM_F3B1 V (D.ext x)
  contDiff_ext := (symmCLM_F3B1 V).contDiff.comp D.contDiff_ext
  metricCoeff_eq := by
    intro e he y hy ξ η
    have h1 := D.metricCoeff_eq e he y hy ξ η
    have h2 := D.metricCoeff_eq e he y hy η ξ
    have hsymm : metricCoeff_F3A G e η ξ y = metricCoeff_F3A G e ξ η y := by
      unfold metricCoeff_F3A
      exact G.symm _ _ _
    simp only [pullbackCoeff_F3A] at h1 h2 ⊢
    rw [symmCLM_F3B1_apply]
    rw [hsymm] at h2
    linarith

theorem AnalyticExtensionData_F3A.symmetrize_F3B1_ext {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {P : Set M} (D : AnalyticExtensionData_F3A G P V) (x : V) :
    D.symmetrize_F3B1.ext x = symmCLM_F3B1 V (D.ext x) := rfl

end Data

section Bridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **桥接到树里的 `MapCInfConvergenceOnCompacts`**：逐阶 `TendstoUniformlyOn` on `K`（`Hn`、`H` 光滑）⇒
`MapCInfConvergenceOnCompacts (interior K) Hn H`。 -/
theorem mapCInfConvergenceOnCompacts_of_tendstoUniformlyOn_F3B1 {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] {Hn : ℕ → W → V →L[ℝ] V →L[ℝ] ℝ}
    {H : W → V →L[ℝ] V →L[ℝ] ℝ} {K : Set W} (hHn : ∀ n, ContDiff ℝ ∞ (Hn n))
    (hH : ContDiff ℝ ∞ H)
    (h : ∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (Hn n))
      (iteratedFDeriv ℝ k H) atTop K) :
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts (interior K) Hn H := by
  intro C hC hCK p ε hε
  have hCK' : C ⊆ K := hCK.trans interior_subset
  have hev : ∀ r ∈ Finset.range (p + 1), ∀ᶠ n in atTop, ∀ x ∈ C,
      dist (iteratedFDeriv ℝ r H x) (iteratedFDeriv ℝ r (Hn n) x) < ε :=
    fun r _ => (Metric.tendstoUniformlyOn_iff.1 ((h r).mono hCK')) ε hε
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((Filter.eventually_all_finset _).2 hev)
  refine ⟨k0, fun k hk r hr x hx => ?_⟩
  have := hk0 k hk r (Finset.mem_range.2 (Nat.lt_succ_of_le hr)) x hx
  unfold CheegerGromovCompactness.mapDerivNorm
  rw [show (fun y => Hn k y - H y) = Hn k - H from rfl,
    iteratedFDeriv_sub_apply ((hHn k).contDiffAt.of_le (by exact_mod_cast le_top))
      (hH.contDiffAt.of_le (by exact_mod_cast le_top)), ← dist_eq_norm, dist_comm]
  exact this.le

end Bridge

section Approx

variable {E M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **G4：F3-b 的 Euclidean 核心接到 `AnalyticExtensionData_F3A`。**
`D.ext` 在 `V` 上光滑；对紧 `K ⊆ V`，整函数列 `Hn`：处处解析（所以在 `embed(P)` 上解析，可直接喂
`D.isAnalyticMetricOn_of_coeff_eq`）、处处对称、每阶 `iteratedFDeriv` 在 `K` 上一致收敛到
`sym(D.ext)`，`D.ext` 正定于 `K` ⇒ eventually `Hn n` 正定于 `K`。 -/
theorem exists_analytic_ext_approx_F3B1 {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {P : Set M}
    (D : AnalyticExtensionData_F3A G P V) {K : Set V} (hK : IsCompact K) :
    ∃ Hn : ℕ → V → V →L[ℝ] V →L[ℝ] ℝ, (∀ n, AnalyticOnNhd ℝ (Hn n) univ) ∧
      (∀ n, ∀ x ∈ P, AnalyticAt ℝ (Hn n) (D.embed x)) ∧ (∀ n, ContDiff ℝ ∞ (Hn n)) ∧
      (∀ k : ℕ, TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (Hn n))
        (iteratedFDeriv ℝ k D.symmetrize_F3B1.ext) atTop K) ∧
      (∀ n x (v w : V), Hn n x v w = Hn n x w v) ∧
      ((∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < D.ext x v v) →
        ∀ᶠ n in atTop, ∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < Hn n x v v) := by
  have hg : ContDiff ℝ ∞ D.symmetrize_F3B1.ext := D.symmetrize_F3B1.contDiff_ext
  obtain ⟨Hn, hA, hC, hS, hP⟩ := exists_analytic_approx_bilinear_F3B1 isOpen_univ hK
    (subset_univ K) hg.contDiffOn
  refine ⟨Hn, hA, fun n x _ => hA n _ (mem_univ _), fun n => ?_, hC,
    hS (fun x _ v w => symmCLM_F3B1_symm (D.ext x) v w), fun hpos => hP fun x hx v hv => ?_⟩
  · exact contDiffOn_univ.1 ((hA n).contDiffOn uniqueDiffOn_univ)
  · rw [D.symmetrize_F3B1_ext, symmCLM_F3B1_self]
    exact hpos x hx v hv

/-- **consumer**：`Hn n` 的整函数性质经 `D.isAnalyticMetricOn_of_coeff_eq` 变成
`IsAnalyticMetricOn_F3A D.atlas P G'`（`G'` 是系数等于 `embed^* (Hn n)` 的度量）。 -/
theorem isAnalyticMetricOn_of_approx_F3B1 {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {P : Set M}
    (D : AnalyticExtensionData_F3A G P V) (hP : IsOpen P) {K : Set V} (hK : IsCompact K) :
    ∃ Hn : ℕ → V → V →L[ℝ] V →L[ℝ] ℝ, ∀ n, ∀ G' : SmoothRiemannianMetric 𝓘(ℝ, E) M,
      (∀ e ∈ D.atlas, ∀ y ∈ e '' (P ∩ e.source), ∀ ξ η : E,
        metricCoeff_F3A G' e ξ η y = pullbackCoeff_F3A D.embed (Hn n) e ξ η y) →
      IsAnalyticMetricOn_F3A D.atlas P G' := by
  obtain ⟨Hn, -, hHn, -⟩ := exists_analytic_ext_approx_F3B1 D hK
  exact ⟨Hn, fun n G' hG' => D.isAnalyticMetricOn_of_coeff_eq hP (hHn n) hG'⟩

end Approx

end DifferentialGeometry.Geometry.Analytic
