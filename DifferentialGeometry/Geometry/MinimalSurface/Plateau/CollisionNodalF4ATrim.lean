import DifferentialGeometry.Analysis.Elliptic.HarmonicMap.AnalyticRegularityF3C

/-!
# F4-a（`_F4A`）G4：二次 trim 的 analytic adapter（D-R-AN1-1）

`second_trim_analytic_F3C` 给的是 `vₙ = affineSubdisk (u n) 0 s` 在**开盘内部**对 `𝒜` 逐 chart 解析；
R9 producer 要
`hFa`：在闭盘的**开邻域**上解析且像 ⊂ `P`。本模块只对缩放映射 `F z = diskExtension u (s • z)` 证
（`F3C` 的 `morrey_disk_analytic_F3C` 复合解析线性映射，`V = {z ∈ ball 0 (1/s) | F z ∈ P}`
是开集，紧性 + `P` 开 ⇒ 含闭盘），**不**把任意 `SmoothDiskExtension` 升级为解析延拓；并证 `F` 与
`diskExtension (affineSubdisk u 0 s)` 在闭盘上相等。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Analytic DifferentialGeometry.Topology
  DifferentialGeometry.Analysis.Elliptic.HarmonicMap

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 子盘的 `diskExtension` 在闭盘上就是缩放后的原 `diskExtension`。 -/
theorem diskExtension_affineSubdisk_eq_F4A (u : C(closedDisk, M)) (s : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    diskExtension (affineSubdisk u 0 s) z = diskExtension u ((s : ℂ) * z) := by
  have h := diskExtension_coe (affineSubdisk u 0 s) ⟨z, hz⟩
  change diskExtension (affineSubdisk u 0 s) z = _ at h
  rw [h]
  change diskExtension u (0 + s • z) = _
  rw [zero_add, Complex.real_smul]

/-- 值域条件的等价写法：`range (affineSubdisk u 0 s) ⊆ P` ⇒ 缩放闭盘 `closedBall 0 s` 的像在 `P`。 -/
theorem diskExtension_mem_of_range_affineSubdisk_F4A (u : C(closedDisk, M)) {s : ℝ}
    (hs : 0 < s) {P : Set M} (hP : Set.range (affineSubdisk u 0 s) ⊆ P) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) s) : diskExtension u z ∈ P := by
  have hz' : ((s : ℂ)⁻¹ * z) ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hs.le, inv_mul_le_iff₀ hs, mul_one]
    exact mem_closedBall_zero_iff.mp hz
  refine hP ⟨⟨(s : ℂ)⁻¹ * z, hz'⟩, ?_⟩
  change diskExtension u (0 + s • ((s : ℂ)⁻¹ * z)) = diskExtension u z
  rw [zero_add, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs.ne'),
    one_mul]

/-- **G4（D-R-AN1-1 adapter）**：原盘 `u`（analytic 度量下的 Morrey 盘）内部解析（F3C）+ 缩放子盘的像在 `P` ⇒
`F z = diskExtension u (s • z)` 在新闭盘 `closedBall 0 1` 的**开邻域** `V` 上对 `𝒜` 的每个 chart 解析，且
`F '' V ⊆ P`。只对这个缩放映射证，不把任意 `SmoothDiskExtension` 当解析延拓（`F` 与
`diskExtension (affineSubdisk u 0 s)` 在闭盘上相等，见 `diskExtension_affineSubdisk_eq_F4A`）。 -/
theorem second_trim_analytic_near_closedDisk_F4A {P : Set M} (hPo : IsOpen P)
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hG : IsAnalyticMetricOn_F3A 𝒜 P G)
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk G γ u) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hP : Set.range (affineSubdisk u 0 s) ⊆ P) :
    ∃ V : Set ℂ, IsOpen V ∧ closedBall (0 : ℂ) 1 ⊆ V ∧
      (∀ z ∈ V, diskExtension u ((s : ℂ) * z) ∈ P) ∧
      ∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (diskExtension u ((s : ℂ) * z)))
        (V ∩ (fun z => diskExtension u ((s : ℂ) * z)) ⁻¹' (e.source ∩ P)) := by
  have hFc : Continuous fun z : ℂ => diskExtension u ((s : ℂ) * z) :=
    (u.continuous.comp diskRetraction_lipschitz.continuous).comp
      (continuous_const.mul continuous_id)
  have hscale : ∀ z ∈ ball (0 : ℂ) (1 / s), (s : ℂ) * z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
    rw [mem_ball_zero_iff, lt_div_iff₀ hs0] at hz
    linarith
  refine ⟨ball (0 : ℂ) (1 / s) ∩ (fun z : ℂ => diskExtension u ((s : ℂ) * z)) ⁻¹' P,
    isOpen_ball.inter (hPo.preimage hFc), ?_, fun z hz => hz.2, ?_⟩
  · intro z hz
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, lt_div_iff₀ hs0]
      have : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      nlinarith
    · refine diskExtension_mem_of_range_affineSubdisk_F4A u hs0 hP ?_
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      have : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
      nlinarith
  · intro e he
    have hmain := morrey_disk_analytic_F3C hPo h𝒜 hG hu e he
    have hlin : AnalyticOnNhd ℝ (fun z : ℂ => (s : ℂ) * z) univ := fun z _ =>
      (analyticAt_const (v := (s : ℂ))).mul analyticAt_id
    refine hmain.comp (hlin.analyticOn.mono (subset_univ _)) ?_
    intro z hz
    exact ⟨hscale z hz.1.1, hz.2⟩

/-- consumer：R9 producer 合同的 `hFa` 形（`∃ V` 开、`closedBall 0 1 ⊆ V`、逐 chart 解析），并且
`F` 在闭盘上就是二次 trim 的子盘 `affineSubdisk u 0 s` 的 `diskExtension`。 -/
theorem second_trim_hFa_F4A {P : Set M} (hPo : IsOpen P)
    {𝒜 : Set (OpenPartialHomeomorph M E)} (h𝒜 : IsAnalyticCompatibleAtlas_F3A P 𝒜)
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hG : IsAnalyticMetricOn_F3A 𝒜 P G)
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk G γ u) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) (hP : Set.range (affineSubdisk u 0 s) ⊆ P) :
    ∃ V : Set ℂ, IsOpen V ∧ closedBall (0 : ℂ) 1 ⊆ V ∧
      (∀ e ∈ 𝒜, AnalyticOn ℝ (fun z => e (diskExtension u ((s : ℂ) * z)))
        (V ∩ (fun z => diskExtension u ((s : ℂ) * z)) ⁻¹' (e.source ∩ P))) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1,
        diskExtension u ((s : ℂ) * z) = diskExtension (affineSubdisk u 0 s) z := by
  obtain ⟨V, hVo, hV, -, hVa⟩ := second_trim_analytic_near_closedDisk_F4A hPo h𝒜 hG hu hs0 hs1 hP
  exact ⟨V, hVo, hV, hVa, fun z hz => (diskExtension_affineSubdisk_eq_F4A u s hz).symm⟩

end DifferentialGeometry.Geometry
