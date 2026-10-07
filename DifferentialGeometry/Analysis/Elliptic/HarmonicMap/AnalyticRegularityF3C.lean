import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3CChart
import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3CInduction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8

/-!
# R8-AR：analytic 度量下 Morrey 盘的内部实解析（O-MY-F3C G5，后缀 `_F3C`）

合同（`design-MY-route-rev2` R8-AR，`MYD2/R06to08.lean:139` 的 `morrey_disk_analytic_MYD2`；谓词按
F3A §2 逐字换成 `_F3A`）：`P` 开、`𝒜` 是 `P` 上的 analytic compatible atlas、`G` 在 `P` 上对 `𝒜` 解析、
`u` 是 `G`-Morrey 盘 ⇒ `∀ e ∈ 𝒜`，`z ↦ e (diskExtension u z)` 在
`ball 0 1 ∩ (diskExtension u)⁻¹' (e.source ∩ P)` 上 `AnalyticOn ℝ`。只用 `smoothInterior` + `harmonic`。
装配：G1 chart 方程（选项 α，`e` 任意 maximal-atlas chart）+ F3A Γ analytic + G4 Euclidean 核心
（G2 gradient、G3 majorant、depth-weighted 归纳、Taylor criterion）。
consumer：S-MY-R8 的二次 trim `vₙ = affineSubdisk (uₙ) 0 s`（`second_trim_regular_collar_R8` 的输出）
在 analytic 度量 `Gₙ` 下 eventually 实解析。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Elliptic.HarmonicMap

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Analytic
  DifferentialGeometry.Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **R8-AR**（`morrey_disk_analytic_MYD2` 的 `_F3A` 版）：analytic 度量下的 Morrey 盘在内部对
analytic atlas 的每个 chart 实解析。 -/
theorem morrey_disk_analytic_F3C {P : Set M} (hP : IsOpen P)
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hG : IsAnalyticMetricOn_F3A 𝒜 P G)
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk G γ u) :
    ∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (diskExtension u z))
      (Metric.ball (0 : ℂ) 1 ∩ diskExtension u ⁻¹' (e.source ∩ P)) := by
  intro e he
  have hemax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := h𝒜.mem_maximalAtlas e he
  set b := Module.finBasis ℝ E with hb
  set Ω := Metric.ball (0 : ℂ) 1 ∩ diskExtension u ⁻¹' (e.source ∩ P) with hΩdef
  have hcont : ContinuousOn (diskExtension u) (Metric.ball (0 : ℂ) 1) :=
    hu.smoothInterior.continuousOn
  have hΩ : IsOpen Ω := hcont.isOpen_inter_preimage Metric.isOpen_ball (e.open_source.inter hP)
  set V := e '' (P ∩ e.source) with hVdef
  have hV : IsOpen V := e.isOpen_image_of_subset_source (hP.inter e.open_source) inter_subset_right
  have hΓ : AnalyticOnNhd ℝ (christoffelBilin_F3C G e b) V :=
    analyticOnNhd_christoffelBilin_F3C hG hP h𝒜.mem_maximalAtlas he b
  have hv : ContDiffOn ℝ ∞ (e ∘ diskExtension u) Ω := by
    intro z hz
    have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) z :=
      hu.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hz.1)
    have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e (diskExtension u z) :=
      contMDiffAt_of_mem_maximalAtlas hemax hz.2.1
    exact (he'.comp z hU).contDiffAt.contDiffWithinAt
  have hvV : MapsTo (e ∘ diskExtension u) Ω V := fun z hz =>
    ⟨diskExtension u z, ⟨hz.2.2, hz.2.1⟩, rfl⟩
  have heq : ∀ z ∈ Ω, Laplacian.laplacian (e ∘ diskExtension u) z =
      -(christoffelBilin_F3C G e b ((e ∘ diskExtension u) z)
          (fderiv ℝ (e ∘ diskExtension u) z 1) (fderiv ℝ (e ∘ diskExtension u) z 1) +
        christoffelBilin_F3C G e b ((e ∘ diskExtension u) z)
          (fderiv ℝ (e ∘ diskExtension u) z Complex.I)
          (fderiv ℝ (e ∘ diskExtension u) z Complex.I)) :=
    fun z hz => laplacian_chart_eq_of_isMorreyDisk_F3C hu hemax b hz.1 hz.2.1
  exact (analyticOnNhd_of_laplacian_eq_F3C hΩ hV hΓ hv hvV heq).analyticOn

/-! ## consumer（G5）：S-MY-R8 二次 trim 的 `vₙ` 在 analytic `Gₙ` 下 eventually 实解析 -/

/-- `second_trim_regular_collar_R8` 的输出（rank、collar、trace 光滑嵌入、对自身 trace 的
`Gₙ`-Morrey 极小）再加 **R8-AR**：若每个 `Gₙ` 在 `P` 上对同一 analytic atlas `𝒜` 解析，则
eventually `vₙ = affineSubdisk (uₙ) 0 s` 对 `𝒜` 的每个 chart 在内部实解析。 -/
theorem second_trim_analytic_F3C [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q)
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc)
    {P : Set M} (hP : IsOpen P) {𝒜 : Set (OpenPartialHomeomorph M E)}
    (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜) (hGn : ∀ n, IsAnalyticMetricOn_F3A 𝒜 P (Gn n)) :
    ∃ μ : ℝ, μ < 1 ∧ ∀ᶠ n in atTop,
      IsMorreyDisk (Gn n) (diskTrace (affineSubdisk (u n) 0 s)) (affineSubdisk (u n) 0 s) ∧
      ∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (diskExtension (affineSubdisk (u n) 0 s) z))
        (Metric.ball (0 : ℂ) 1 ∩ diskExtension (affineSubdisk (u n) 0 s) ⁻¹' (e.source ∩ P)) := by
  obtain ⟨μ, hμ, hev⟩ := second_trim_regular_collar_R8 hΓ hd hq hqrank hρ₁ hρ₁s hs hqcol hu hC0
    hCk
  refine ⟨μ, hμ, ?_⟩
  filter_upwards [hev] with n hn
  exact ⟨hn.2.2.2, morrey_disk_analytic_F3C hP h𝒜 (hGn n) hn.2.2.2⟩

end DifferentialGeometry.Analysis.Elliptic.HarmonicMap
