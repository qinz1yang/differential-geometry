import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldShortening
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow

/-!
# S-MY-R4B G1：外审 R4 `a_fold_gives_a_strictly_better_Lipschitz_competitor` 的 ADAPTER 完整形

IMS03 搬入的 `exists_supported_flow_of_nonzero_fold`（`Variation/NonzeroFoldFlow`）与
`exists_disk_area_lt_of_fold_divergence_neg`（`Plateau/FoldShortening`）的复合。已有的
`ShapeAdaptersMYS` example 4 缺外审 R4 的一半：**competitor 与 `f` 在 patch 外相同**。
`exists_disk_area_lt_of_fold_divergence_neg` 的结论只暴露 `trace`、`range ⊆ W`、面积不等式；
patch 外 `v = u` 在它的 proof 里（`exists_disk_replacement_of_smooth_map` 的 `houter`）被丢掉。

本文件（只新增，不改 verbatim 文件）：
* `riemannianDiskArea_replacement_eq_R4B`：`FoldShortening` 里 private 的面积换元恒等式的
  逐字重证（private 不能引用）。
* `exists_disk_area_lt_of_fold_divergence_neg_local_R4B`：与 IMS03 同前提（flow 形），结论多一条
  `∀ z, r ≤ dist z p → v z = u z`。
* **`exists_better_competitor_of_fold_R4B`**（G1 主定理）：两个闭半盘 sheet 是 conformal harmonic
  （原极小盘的片，R12/R13 的实际用法），seam 点 `p` 处 outward conormal 和 `≠ 0`，`u p` 在 `W`
  的内部 ⇒ ∃ metric-Lipschitz `v`、∃ 紧集 `S ⊆ D°`（`S` 是 seam 点 `p` 处半径 `r ≤ R` 的闭 patch
  圆盘，即 seam 的 regular open subarc `(p - r, p + r)` 的邻域），`S` 外 `v = u`（于是 `∂D`
  上 `v = u`，trace 相同）、`range v ⊆ W`、`A(v) < A(u)`。competitor 是 map，不要求 embedded；
  不依赖 analytic。
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

/-- `FoldShortening.riemannianDiskArea_replacement_eq`（private）的重证：patch 内换成 `v`、
patch 外保持 `u` 的 Lipschitz 盘 `w`，其面积 = `A(u) - A_u(ball) + A_v(ball)`。 -/
private theorem riemannianDiskArea_replacement_eq_R4B
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u w : C(closedDisk, M)) {K L : ℝ≥0}
    (hu : ∀ z z', riemannianEDistOf g (u z) (u z') ≤
      (K : ℝ≥0∞) * edist z z')
    (hw : ∀ z z', riemannianEDistOf g (w z) (w z') ≤
      (L : ℝ≥0∞) * edist z z')
    {v : ℂ → M} {p : ℂ} {r : ℝ}
    (hball : Metric.closedBall p r ⊆ Metric.ball (0 : ℂ) 1)
    (hinner : ∀ z : closedDisk, dist (z : ℂ) p ≤ r → w z = v z)
    (houter : ∀ z : closedDisk, r ≤ dist (z : ℂ) p → w z = u z) :
    riemannianDiskArea g w = riemannianDiskArea g u -
      riemannianArea g (diskExtension u) (Metric.closedBall p r) +
      riemannianArea g v (Metric.closedBall p r) := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : ℂ) 1)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) 1).measure_lt_top.ne
  have hiu : IntegrableOn (riemannianAreaDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hu) _
  have hiw : IntegrableOn (riemannianAreaDensity g (diskExtension w))
      (Metric.closedBall (0 : ℂ) 1) :=
    integrableOn_riemannianAreaDensity_of_lipschitz g
      (diskExtension_riemannian_lipschitz g hw) _
  have hsub : Metric.closedBall p r ⊆ Metric.closedBall (0 : ℂ) 1 :=
    hball.trans Metric.ball_subset_closedBall
  have hinside : riemannianArea g (diskExtension w) (Metric.closedBall p r) =
      riemannianArea g v (Metric.closedBall p r) := by
    apply riemannianArea_congr_on_closedBall g
    intro z hz
    exact (diskExtension_coe w ⟨z, hsub hz⟩).trans
      (hinner ⟨z, hsub hz⟩ (Metric.mem_closedBall.mp hz))
  have houtside :
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall p r,
        riemannianAreaDensity g (diskExtension w) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall p r,
        riemannianAreaDensity g (diskExtension u) z := by
    have hzint : ∀ᵐ z ∂volume.restrict
        (Metric.closedBall (0 : ℂ) 1 \ Metric.closedBall p r),
        z ∈ Metric.ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint, ae_restrict_mem
      (Metric.isClosed_closedBall.measurableSet.diff
        Metric.isClosed_closedBall.measurableSet)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(Metric.isOpen_ball.inter
      Metric.isClosed_closedBall.isOpen_compl).mem_nhds ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, Metric.ball_subset_closedBall hy.1⟩
    have hdist : r ≤ dist y p :=
      (not_le.mp (show ¬ dist y p ≤ r from hy.2)).le
    exact (diskExtension_coe w q).trans
      ((houter q hdist).trans (diskExtension_coe u q).symm)
  have hsu := setIntegral_sdiff Metric.isClosed_closedBall.measurableSet hiu hsub
  have hsw := setIntegral_sdiff Metric.isClosed_closedBall.measurableSet hiw hsub
  change (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension u) z) -
      (∫ z in Metric.closedBall p r, riemannianAreaDensity g (diskExtension u) z) +
        ∫ z in Metric.closedBall p r, riemannianAreaDensity g v z
  change (∫ z in Metric.closedBall p r, riemannianAreaDensity g (diskExtension w) z) =
    (∫ z in Metric.closedBall p r, riemannianAreaDensity g v z) at hinside
  rw [houtside, hinside, hsu] at hsw
  linarith

/-- IMS03 `exists_disk_area_lt_of_fold_divergence_neg` 的**局部支撑版**：前提逐字相同
（flow `Φ`、速度场 `Y`、patch 圆 `sphere p r` 固定、两 sheet 的 ambient divergence 积分之和
`< 0`），结论多暴露「patch 圆盘外 `v = u`」：`∀ z, r ≤ dist z p → v z = u z`（包括 `∂D`）。
证明 = 原定理的 proof（面积换元 + `exists_disk_replacement_of_smooth_map` 的 `houter`），
只是不丢 `houter`。 -/
theorem exists_disk_area_lt_of_fold_divergence_neg_local_R4B
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΦzero : ∀ x, Φ 0 x = x)
    (Y : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hY : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (Y x)))
    (hvelocity : ∀ x, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => Φ t x) 0 1 = Y x)
    (p r : ℝ)
    (hpr : ‖(p : ℂ)‖ + r < 1)
    (hfix : ∀ t z, z ∈ Metric.sphere (p : ℂ) r →
      Φ t (diskExtension u z) = diskExtension u z)
    {W : Set M} (huW : Set.range u ⊆ W)
    (hΦW : ∀ t, MapsTo (Φ t) W W)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj)
      (Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}))
    (hi : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hir : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z))
    (hnegative :
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension u) (closedHalfDisk p r) Y z) +
      (∫ z in Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
        ambientDivergenceWithin g (diskExtension u ∘ conj) (closedHalfDisk p r) Y z) < 0) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, r ≤ dist (z : ℂ) (p : ℂ) → v z = u z) ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  have hdecrease : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      riemannianArea g ((Φ t) ∘ diskExtension u) (Metric.closedBall (p : ℂ) r) <
        riemannianArea g (diskExtension u) (Metric.closedBall (p : ℂ) r) := by
    obtain ⟨_, _, hd⟩ := hasDerivAt_riemannianArea_isotopy_of_fold
      g u huLip Φ hΦ hΦzero Y hY hvelocity p r hU hUr hi hir
    have hs := hd.tendsto_slope_zero_right.eventually_lt_const hnegative
    filter_upwards [hs, self_mem_nhdsWithin] with t ht hpos
    have hinitial : (Φ 0) ∘ diskExtension u = diskExtension u := by
      funext z
      exact hΦzero _
    simp only [zero_add, smul_eq_mul, hinitial] at ht
    rcases mul_neg_iff.mp ht with ⟨_, hdiff⟩ | ⟨hneg, _⟩
    · exact sub_neg.mp hdiff
    · exact ((not_lt_of_ge (inv_pos.mpr hpos).le) hneg).elim
  obtain ⟨t, ht⟩ := hdecrease.exists
  obtain ⟨v, K, hvLip, hvtrace, hvW, hinner, houter⟩ :=
    exists_disk_replacement_of_smooth_map g u huLip ((Φ t).contMDiff.of_le (by simp))
      hpr (hfix t) huW (hΦW t)
  have hball : Metric.closedBall (p : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ dist z (p : ℂ) + ‖(p : ℂ)‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    exact hn.trans_lt (by have hd := Metric.mem_closedBall.mp hz; linarith)
  have hin : ∀ z : closedDisk, dist (z : ℂ) (p : ℂ) ≤ r →
      v z = ((Φ t) ∘ diskExtension u) z := by
    intro z hz
    exact (hinner z hz).trans (congrArg (Φ t) (diskExtension_coe u z).symm)
  have harea := riemannianDiskArea_replacement_eq_R4B g u v huLip hvLip hball hin houter
  refine ⟨v, K, hvLip, hvtrace, hvW, houter, ?_⟩
  linarith

/-- **外审 R4（G1 主定理）**。`u : closedDisk → M` metric-Lipschitz；seam 是源坐标实轴上的线段，
两侧 sheet `u|_{上半盘}`、`u∘conj|_{上半盘}` 在 `closedHalfDisk p R` 上 `C¹`、内部 `C^∞`、
conformal harmonic（= 原极小盘的片）、differential 单射；seam 点 `p` 处两个 inward conormal 的
和 `≠ 0`（`η₊ + η₋ ≠ 0`，第二个经 `tangentSpaceCast` 搬到同一切空间），`u p ∈ interior W`。
结论：∃ metric-Lipschitz `v`、∃ 紧集 `S ⊆ D°`（`S = closedBall p r`，`0 < r ≤ R`，是 seam 的
regular open subarc `(p - r, p + r)` 邻域内的 patch 圆盘）使得
* `S` 外 `v = u`（因此 `∂D` 上相同）；
* `diskTrace v = diskTrace u`、`range v ⊆ W`（支撑在 target interior）；
* `riemannianDiskArea g v < riemannianDiskArea g u`。
competitor 是 map，不要求 embedded、不要求 seam 外无其它自交。 -/
theorem exists_better_competitor_of_fold_R4B
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {W : Set M} (huW : Set.range u ⊆ W) {p R : ℝ} (hR : 0 < R) (hpR : ‖(p : ℂ)‖ + R < 1)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R))
    (hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R))
    (hconf : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u) z)
    (hconfr : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u ∘ conj) z)
    (htension : ∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension g (diskExtension u) z = 0)
    (htensionr : ∀ z ∈ (openHalfDisk p R : Set ℂ),
      diskMapTension g (diskExtension u ∘ conj) z = 0)
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0) (S : Set ℂ),
      IsCompact S ∧ S ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∃ r : ℝ, 0 < r ∧ r ≤ R ∧ S = Metric.closedBall (p : ℂ) r) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ S → v z = u z) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → v z = u z) ∧
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  obtain ⟨r, Y, Φ, hr0, hrR, hY, -, -, hΦ, hΦzero, hvelocity, hfix, hΦW, hneg⟩ :=
    exists_supported_flow_of_nonzero_fold g u hR hU hUr hi hir hUi hUri hconf hconfr htension
      htensionr hpW hfold
  have hopen : Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆ (openHalfDisk p R : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrR⟩
  have hopenClosed : (openHalfDisk p R : Set ℂ) ⊆ closedHalfDisk p R :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hnhds (z : ℂ) (hz : z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk p R ∈ 𝓝 z :=
    Filter.mem_of_superset ((openHalfDisk p R).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hi' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hi z (mem_of_mem_nhds (hnhds z hz))
  have hir' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hir z (mem_of_mem_nhds (hnhds z hz))
  have hpr : ‖(p : ℂ)‖ + r < 1 := by
    have : ‖(p : ℂ)‖ + r ≤ ‖(p : ℂ)‖ + R := by linarith
    linarith
  obtain ⟨v, K, hvLip, hvtrace, hvW, hvouter, hvarea⟩ :=
    exists_disk_area_lt_of_fold_divergence_neg_local_R4B g u huLip Φ hΦ hΦzero Y hY hvelocity
      p r hpr hfix huW hΦW (hUi.mono hopen) (hUri.mono hopen) hi' hir' hneg
  have hball : Metric.closedBall (p : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ dist z (p : ℂ) + ‖(p : ℂ)‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using norm_add_le (z - (p : ℂ)) (p : ℂ)
    exact hn.trans_lt (by have hd := Metric.mem_closedBall.mp hz; linarith)
  have hoff : ∀ z : closedDisk, (z : ℂ) ∉ Metric.closedBall (p : ℂ) r → v z = u z :=
    fun z hz => hvouter z (not_le.mp (Metric.mem_closedBall.not.mp hz)).le
  refine ⟨v, K, Metric.closedBall (p : ℂ) r, isCompact_closedBall _ _, hball,
    ⟨r, hr0, hrR, rfl⟩, hoff, fun z hz => hoff z fun hzS => ?_, hvLip, hvtrace, hvW, hvarea⟩
  have hlt := Metric.mem_ball.mp (hball hzS)
  rw [dist_zero_right] at hlt
  exact absurd hz hlt.ne

end DifferentialGeometry.Geometry
