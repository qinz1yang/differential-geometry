import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorR4B
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SourceChartReplacement

/-!
# S-MY-R4C G1：外审 R4 的 general-seam / chart 版

`FoldCompetitorR4B` 的 G1 `exists_better_competitor_of_fold_R4B` 里 seam 是源坐标实轴上的线段
（sheet 是原极小盘的**坐标**半盘，所以 conformal harmonic 假设直接挂在 `diskExtension u` 上）。
R12 / R13 的实际 seam 是 `D°` 里的任意光滑弧（例如 `∂Ω₂` 的 regular open subarc），源坐标不是
conformal 的。本文件把 R4B G1 搬到 IMS03 的 `sourceChart` 框架（`PartialDiffeomorph χ`，
`closedBall 0 1 ⊆ χ.source`，`χ '' closedBall 0 1 ⊆ ball 0 1`）下：

* seam = `χ '' [p - R, p + R]`（`χ` 是 `∞` 微分同胚，故 seam 是光滑 regular 弧）；
* 两侧 sheet = `diskExtension u ∘ χ` 与 `diskExtension u ∘ χ ∘ conj` 在 `closedHalfDisk p R` 上
  （`conj` 把 seam 另一侧翻回来）；
* sheet 的几何极小性**不**要求 conformal 坐标：它们是 conformal harmonic 的 `U₀`（原极小盘）的
  reparametrization `U₀ ∘ ψ₁`、`U₀ ∘ ψ₂`（`ψᵢ` 光滑、导数处处双射、落在 `ball 0 1`），即 IMS03
  `exists_supported_flow_of_reparametrized_nonzero_fold` 的形状（R13：`ψ₁ = χ`、`ψ₂ = B ∘ χ ∘ conj`）。

本文件（只新增，不改 verbatim 文件）：
* `fold_mfderivWithin_congr_R4C`、`fold_conormal_congr_R4C`：IMS03 `ReplacementFold` 里 private 的
  同名引理的逐字重证（private 不能引用）。
* **`exists_better_competitor_of_fold_seam_R4C`**（G1 主定理）：结论与 R4B G1 同形——
  ∃ metric-Lipschitz `v`、∃ 紧集 `S ⊆ D°`（`S = χ '' closedBall p r`，`0 < r ≤ R`，是 seam 的
  regular open subarc `χ '' (p - r, p + r)` 的邻域）使 `S` 外（含 `∂D`）`v = u`、
  `diskTrace v = diskTrace u`、`range v ⊆ W`、`A(v) < A(u)`。
* `fold_seam_conormal_sum_eq_zero_of_minimal_R4C`：面积极小 ⇒ seam 点处 `η₊ + η₋ = 0`（反证）。

证明 = 把 `d := diskThroughSourceChart u χ`（chart 坐标下的 literal 盘）交给 reparametrized flow
（`exists_supported_flow_of_reparametrized_nonzero_fold`）与 R4B 的 local 面积引理（暴露 patch 外
`d' = d`），再用 `exists_sourceChart_disk_replacement`（暴露 `z ∉ interior K → v z = u z`）
和 `riemannianDiskArea_diskThroughSourceChart` 把 chart 里的改进贴回 `u`。competitor 是 map，
不要求 embedded；不依赖 analytic。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] in
/-- `ReplacementFold.replacement_fold_mfderivWithin_congr`（private）的重证：`EqOn` 的两个映射在
`H` 内一点的 `mfderivWithin` 相同。 -/
private theorem fold_mfderivWithin_congr_R4C {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F H z) =
      (show ℂ →L[ℝ] E from mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) G H z) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) heq hz
  ext w
  simpa only [ContinuousLinearMap.comp_apply] using!
    congrArg (fun D : ℂ →L[ℝ] E => D w) hd

omit [FiniteDimensional ℝ E] [T3Space M] in
/-- `ReplacementFold.replacement_fold_conormal_congr`（private）的重证：`EqOn` 的两个映射在
`H` 内一点的 inward conormal 相同。 -/
private theorem fold_conormal_congr_R4C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {F G : ℂ → M} {H : Set ℂ}
    (heq : EqOn F G H) {z : ℂ} (hz : z ∈ H) :
    (inwardConormalWithin g F H z : E) = (inwardConormalWithin g G H z : E) := by
  let Q : M → (ℂ →L[ℝ] E) → E := fun q D =>
    (Real.sqrt (g.inner q (D 1) (D 1)) *
      tangentTwoJacobian g (x := q) (D 1) (D Complex.I))⁻¹ •
      (g.inner q (D 1) (D 1) • D Complex.I - g.inner q (D 1) (D Complex.I) • D 1)
  have h := congrArg₂ Q (heq hz) (fold_mfderivWithin_congr_R4C heq hz)
  simpa only [Q, inwardConormalWithin, gramWithin, densityWithin, partialWithin] using! h

/-- **外审 R4（G1 主定理，general-seam / chart 版）。**  `u : closedDisk → M` metric-Lipschitz；
`χ` 是 IMS03 `sourceChart`（`∞` 局部微分同胚，`closedBall 0 1 ⊆ χ.source`，像落在 `ball 0 1`），
seam 是 `χ '' [p - R, p + R]`；两侧 sheet `u ∘ χ|_{上半盘}`、`u ∘ χ ∘ conj|_{上半盘}` 在
`closedHalfDisk p R` 上 `C¹`、内部 `C^∞`（后者由 reparametrization 给出）、differential 单射，
且是 conformal harmonic 盘 `U₀`（原极小盘）的 reparametrization `U₀ ∘ ψ₁`、`U₀ ∘ ψ₂`
（`ψᵢ` 在开半盘上光滑、导数双射、落在 `ball 0 1`）；seam 点 `χ p` 处两个 inward conormal 的和
`≠ 0`（`η₊ + η₋ ≠ 0`，在 chart 坐标下量，第二个经 `tangentSpaceCast` 搬到同一切空间），
`u (χ p) ∈ interior W`。结论：∃ metric-Lipschitz `v`、∃ 紧集 `S ⊆ D°`（`S = χ '' closedBall p r`，
`0 < r ≤ R`，是 seam 的 regular open subarc `χ '' (p - r, p + r)` 邻域内的 patch）使得
* `S` 外 `v = u`（因此 `∂D` 上相同）；
* `diskTrace v = diskTrace u`、`range v ⊆ W`（支撑在 target interior）；
* `riemannianDiskArea g v < riemannianDiskArea g u`。
competitor 是 map，不要求 embedded、不要求 seam 外无其它自交。 -/
theorem exists_better_competitor_of_fold_seam_R4C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {W : Set M} (huW : Set.range u ⊆ W)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (U₀ : ℂ → M) (ψ₁ ψ₂ : ℂ → ℂ)
    (hU₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1))
    (hconf₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z)
    (htension₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0)
    {p R : ℝ} (hR : 0 < R) (hpR : ‖(p : ℂ)‖ + R < 1)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ χ) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R) z))
    (hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R))
    (hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R))
    (hmaps₁ : MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hmaps₂ : MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hbij₁ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z))
    (hbij₂ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z))
    (heq₁ : EqOn (diskExtension u ∘ χ) (U₀ ∘ ψ₁) (openHalfDisk p R))
    (heq₂ : EqOn (diskExtension u ∘ χ ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R))
    (hpW : diskExtension u (χ (p : ℂ)) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u ∘ χ) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) (p : ℂ))
        ((diskExtension u ∘ χ) (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0) (S : Set ℂ),
      IsCompact S ∧ S ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∃ r : ℝ, 0 < r ∧ r ≤ R ∧ S = χ '' Metric.closedBall (p : ℂ) r) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ S → v z = u z) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → v z = u z) ∧
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  -- chart 坐标下的 literal 盘 `d`：`diskExtension d = diskExtension u ∘ χ` 在 `closedBall 0 1` 上
  let d : C(closedDisk, M) := diskThroughSourceChart u χ hsrc
  obtain ⟨C, hdLip⟩ := diskThroughSourceChart_lipschitz g u huLip χ (by simp) hsrc
  have hdW : Set.range d ⊆ W := diskThroughSourceChart_range u χ hsrc huW
  have hHB : ∀ z ∈ Metric.closedBall (p : ℂ) R, z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hn : ‖z‖ ≤ dist z (p : ℂ) + ‖(p : ℂ)‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    have hd := Metric.mem_closedBall.mp hz
    linarith
  have hconjB : ∀ z ∈ Metric.closedBall (p : ℂ) R, conj z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    apply hHB
    rw [Metric.mem_closedBall, Complex.dist_conj_comm, Complex.conj_ofReal]
    exact Metric.mem_closedBall.mp hz
  have hdeq₁ : EqOn (diskExtension d) (diskExtension u ∘ χ) (closedHalfDisk p R) :=
    fun z hz => diskExtension_coe d ⟨z, hHB z hz.2⟩
  have hdeq₂ : EqOn (diskExtension d ∘ conj) (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R) :=
    fun z hz => diskExtension_coe d ⟨conj z, hconjB z hz.2⟩
  have hpmem : (p : ℂ) ∈ closedHalfDisk p R :=
    ⟨(show 0 ≤ ((p : ℝ) : ℂ).im by simp), Metric.mem_closedBall_self hR.le⟩
  have hopenClosed : (openHalfDisk p R : Set ℂ) ⊆ closedHalfDisk p R :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  -- 把 R4C 的 chart 形假设搬到 `d`
  have hU_d : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension d) (closedHalfDisk p R) :=
    hU.congr fun z hz => hdeq₁ hz
  have hUr_d : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension d ∘ conj) (closedHalfDisk p R) :=
    hUr.congr fun z hz => hdeq₂ hz
  have hi_d : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) (closedHalfDisk p R) z) := by
    intro z hz a b hab
    have hD := fold_mfderivWithin_congr_R4C (E := E) hdeq₁ hz
    apply hi z hz
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) hD).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) hD))
  have hir_d : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) (closedHalfDisk p R) z) := by
    intro z hz a b hab
    have hD := fold_mfderivWithin_congr_R4C (E := E) hdeq₂ hz
    apply hir z hz
    exact (congrArg (fun D : ℂ →L[ℝ] E => D a) hD).symm.trans
      (hab.trans (congrArg (fun D : ℂ →L[ℝ] E => D b) hD))
  have heq₁_d : EqOn (diskExtension d) (U₀ ∘ ψ₁) (openHalfDisk p R) :=
    fun z hz => (hdeq₁ (hopenClosed hz)).trans (heq₁ hz)
  have heq₂_d : EqOn (diskExtension d ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R) :=
    fun z hz => (hdeq₂ (hopenClosed hz)).trans (heq₂ hz)
  have hpW_d : diskExtension d (p : ℂ) ∈ interior W := by
    rw [hdeq₁ hpmem]
    exact hpW
  have hfold_d : inwardConormalWithin g (diskExtension d) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension d ∘ conj) (p : ℂ)) (diskExtension d (p : ℂ))
        (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0 := by
    change (fun a b : E => a + b)
      (inwardConormalWithin g (diskExtension d) (closedHalfDisk p R) (p : ℂ))
      (inwardConormalWithin g (diskExtension d ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0
    rw [fold_conormal_congr_R4C g hdeq₁ hpmem, fold_conormal_congr_R4C g hdeq₂ hpmem]
    exact hfold
  -- chart 坐标下的 reparametrized fold flow
  obtain ⟨r, Y, Φ, hr0, hrR, hY, -, -, hΦ, hΦzero, hvelocity, hfix, hΦW, hneg⟩ :=
    exists_supported_flow_of_reparametrized_nonzero_fold g d U₀ ψ₁ ψ₂ hU₀ hconf₀ htension₀ hR
      hU_d hUr_d hi_d hir_d hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁_d heq₂_d hpW_d hfold_d
  have hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d) (openHalfDisk p R) :=
    (hU₀.comp hψ₁ hmaps₁).congr fun z hz => heq₁_d hz
  have hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension d ∘ conj) (openHalfDisk p R) :=
    (hU₀.comp hψ₂ hmaps₂).congr fun z hz => heq₂_d hz
  have hopen : Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆ (openHalfDisk p R : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrR⟩
  have hnhds (z : ℂ) (hz : z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk p R ∈ 𝓝 z :=
    Filter.mem_of_superset ((openHalfDisk p R).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hi' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hi_d z (mem_of_mem_nhds (hnhds z hz))
  have hir' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension d ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hir_d z (mem_of_mem_nhds (hnhds z hz))
  have hpr : ‖(p : ℂ)‖ + r < 1 := by linarith
  -- R4B 的 local 面积引理（暴露 patch 外 `d' = d`），作用在 chart 盘 `d` 上
  obtain ⟨d', K', hd'Lip, hd'trace, hd'W, hd'out, hd'area⟩ :=
    exists_disk_area_lt_of_fold_divergence_neg_local_R4B g d hdLip Φ hΦ hΦzero Y hY hvelocity
      p r hpr hfix hdW hΦW (hUi.mono hopen) (hUri.mono hopen) hi' hir' hneg
  have hrB : Metric.closedBall (p : ℂ) r ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun z hz => hHB z (Metric.closedBall_subset_closedBall hrR hz)
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension d' z = diskExtension u (χ z) := by
    intro z hz
    let q : closedDisk := ⟨z, Metric.sphere_subset_closedBall hz⟩
    have hz1 : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hdist : r ≤ dist (q : ℂ) (p : ℂ) := by
      have h1 : ‖z‖ - ‖(p : ℂ)‖ ≤ ‖z - (p : ℂ)‖ := norm_sub_norm_le z (p : ℂ)
      change r ≤ dist z (p : ℂ)
      rw [dist_eq_norm]
      linarith
    exact (diskExtension_coe d' q).trans (hd'out q hdist)
  -- 把 chart 里的改进贴回 `u`
  obtain ⟨v, A, hvLip, hvtrace, hvW, hvinner, hvouter, hvarea⟩ :=
    exists_sourceChart_disk_replacement g u d' huLip hd'Lip χ (by simp) hsrc hinside hboundary
      huW hd'W
  have hdarea := riemannianDiskArea_diskThroughSourceChart g u huLip χ (by simp) hsrc
  have hSc : IsCompact (χ '' Metric.closedBall (p : ℂ) r) :=
    (isCompact_closedBall (p : ℂ) r).image_of_continuousOn
      (χ.contMDiffOn_toFun.continuousOn.mono fun z hz => hsrc (hrB hz))
  have hSD : χ '' Metric.closedBall (p : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 :=
    fun x ⟨w, hw, hx⟩ => hinside ⟨w, hrB hw, hx⟩
  have hoff : ∀ z : closedDisk, (z : ℂ) ∉ χ '' Metric.closedBall (p : ℂ) r → v z = u z := by
    intro z hz
    by_cases hzK : (z : ℂ) ∈ χ '' Metric.closedBall (0 : ℂ) 1
    · rw [hvinner z hzK]
      obtain ⟨w, hw, hwz⟩ := hzK
      have hsymm : χ.symm (z : ℂ) = w := by
        rw [← hwz]
        exact χ.toPartialEquiv.left_inv (hsrc hw)
      have hwr : r ≤ dist w (p : ℂ) := by
        by_contra hlt
        exact hz ⟨w, Metric.mem_closedBall.mpr (not_le.mp hlt).le, hwz⟩
      rw [hsymm]
      calc diskExtension d' w = d' ⟨w, hw⟩ := diskExtension_coe d' ⟨w, hw⟩
        _ = d ⟨w, hw⟩ := hd'out ⟨w, hw⟩ hwr
        _ = diskExtension u (χ w) := rfl
        _ = u z := by rw [hwz]; exact diskExtension_coe u z
    · exact hvouter z fun hi => hzK (interior_subset hi)
  refine ⟨v, A, χ '' Metric.closedBall (p : ℂ) r, hSc, hSD, ⟨r, hr0, hrR, rfl⟩, hoff,
    fun z hz => hoff z fun hzS => ?_, hvLip, hvtrace, hvW, ?_⟩
  · have hlt := Metric.mem_ball.mp (hSD hzS)
    rw [dist_zero_right] at hlt
    exact absurd hz hlt.ne
  · rw [hvarea]
    linarith

/-- **面积极小 ⇒ seam 处 `η₊ + η₋ = 0`（chart 版）。**  `u` 对同 `diskTrace`、`range ⊆ W` 的
metric-Lipschitz competitor 面积极小（`hmin`）时，`exists_better_competitor_of_fold_seam_R4C`
的 reparametrized seam 假设下，`χ p` 处两个 inward conormal 的和为 `0`。证明：否则 G1 给出面积严格
更小的 admissible competitor，与 `hmin` 矛盾。 -/
theorem fold_seam_conormal_sum_eq_zero_of_minimal_R4C
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {W : Set M} (huW : Set.range u ⊆ W)
    (hmin : ∀ v : C(closedDisk, M), diskTrace v = diskTrace u → Set.range v ⊆ W →
      (∃ K : ℝ≥0, ∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) →
        riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hinside : χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (U₀ : ℂ → M) (ψ₁ ψ₂ : ℂ → ℂ)
    (hU₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₀ (Metric.ball (0 : ℂ) 1))
    (hconf₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g U₀ z)
    (htension₀ : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g U₀ z = 0)
    {p R : ℝ} (hR : 0 < R) (hpR : ‖(p : ℂ)‖ + R < 1)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ χ) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R) z))
    (hψ₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₁ (openHalfDisk p R))
    (hψ₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ψ₂ (openHalfDisk p R))
    (hmaps₁ : MapsTo ψ₁ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hmaps₂ : MapsTo ψ₂ (openHalfDisk p R) (Metric.ball (0 : ℂ) 1))
    (hbij₁ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₁ z))
    (hbij₂ : ∀ z ∈ (openHalfDisk p R : Set ℂ), Function.Bijective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ₂ z))
    (heq₁ : EqOn (diskExtension u ∘ χ) (U₀ ∘ ψ₁) (openHalfDisk p R))
    (heq₂ : EqOn (diskExtension u ∘ χ ∘ conj) (U₀ ∘ ψ₂) (openHalfDisk p R))
    (hpW : diskExtension u (χ (p : ℂ)) ∈ interior W) :
    inwardConormalWithin g (diskExtension u ∘ χ) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ χ ∘ conj) (p : ℂ))
        ((diskExtension u ∘ χ) (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ χ ∘ conj) (closedHalfDisk p R) (p : ℂ)) = 0 := by
  by_contra hfold
  obtain ⟨v, K, -, -, -, -, -, -, hvLip, hvtrace, hvW, hvarea⟩ :=
    exists_better_competitor_of_fold_seam_R4C g u huLip huW χ hsrc hinside U₀ ψ₁ ψ₂ hU₀ hconf₀
      htension₀ hR hpR hU hUr hi hir hψ₁ hψ₂ hmaps₁ hmaps₂ hbij₁ hbij₂ heq₁ heq₂ hpW hfold
  exact absurd (hmin v hvtrace hvW ⟨K, hvLip⟩) (not_le.mpr hvarea)

end DifferentialGeometry.Geometry
