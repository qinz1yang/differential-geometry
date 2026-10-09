import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.SheetLocalFactorR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.BranchAreaR5
import DifferentialGeometry.Geometry.HarmonicMap.ConformalRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.SheetCoincidenceDiskR3B

/-!
# O-MY-R5：R5-B(i) 的 Morrey 版局部零件（正则点集、局部因子、partner 唯一）

`U := diskExtension u`（Morrey 盘，可有孤立内部 branch points）、`V := diskExtension q`（开盘内 rank 2）。
* 正则点集 `R := {z ∈ D° | mfderiv U z 单射}`：开、补集可数
  （`IsMorreyDisk.finite_not_injective_mfderiv_of_isCompact`）、
  预连通（`isPreconnected_ball_diff_countable_R5`）、与任何非空开集相交。
* `exists_morrey_local_factor_R5`：germ `≤` ⇒ 光滑局部因子 `Φ`；在 `U` 的正则点上 germ 相等、`dΦ` 单射、
  `Φ` 是 `ConformalAt`。**起点可以是 branch point**（只用 `V` 的 rank）。
* `eq_of_map_nhds_eq_of_coincidentGermPairs_R5`：R3b（`coincidentGermPairs q = ∅`）⇒ 同一个 `U`-germ 的
  `V`-partner 唯一——这就是"无 monodromy"：partner 全局唯一，不需要路径延拓。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- branch points 在每个紧子盘 `closedBall 0 ρ`（`ρ < 1`）上有限 ⇒ 正则点集开。 -/
theorem isOpen_morrey_regular_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) :
    IsOpen {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzB, hzi⟩
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzB
  set ρ : ℝ := (‖z‖ + 1) / 2 with hρ
  have hzρ : ‖z‖ < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hK : closedBall (0 : ℂ) ρ ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball hρ1
  have hfin := hu.finite_not_injective_mfderiv_of_isCompact hΓ (isCompact_closedBall 0 ρ) hK
  have hzF : z ∉ {w ∈ closedBall (0 : ℂ) ρ | ¬ Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w)} := fun h => h.2 hzi
  have hcl : IsClosed {w ∈ closedBall (0 : ℂ) ρ | ¬ Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w)} := hfin.isClosed
  have h1 : {w ∈ closedBall (0 : ℂ) ρ | ¬ Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w)}ᶜ ∈ 𝓝 z := hcl.isOpen_compl.mem_nhds hzF
  have h2 : ball (0 : ℂ) ρ ∈ 𝓝 z := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hzρ)
  filter_upwards [h1, h2] with w hw1 hw2
  refine ⟨ball_subset_ball hρ1.le hw2, ?_⟩
  by_contra hni
  exact hw1 ⟨ball_subset_closedBall hw2, hni⟩

/-- branch set 可数。 -/
theorem countable_morrey_branch_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) :
    (ball (0 : ℂ) 1 \ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)}).Countable := by
  have hcover : ball (0 : ℂ) 1 \ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} ⊆
      ⋃ n : ℕ, {w ∈ closedBall (0 : ℂ) (1 - 1 / ((n : ℝ) + 2)) | ¬ Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w)} := by
    rintro z ⟨hzB, hzR⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hzB
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - ‖z‖))
    refine mem_iUnion.mpr ⟨n, ?_, fun hi => hzR ⟨hzB, hi⟩⟩
    rw [mem_closedBall_zero_iff]
    have hpos : 0 < 1 - ‖z‖ := by linarith
    have h1 : 1 / ((n : ℝ) + 2) ≤ 1 - ‖z‖ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hn
      nlinarith
    linarith
  refine Countable.mono hcover (countable_iUnion fun n => ?_)
  have hρ1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  exact (hu.finite_not_injective_mfderiv_of_isCompact hΓ (isCompact_closedBall _ _)
    (closedBall_subset_ball hρ1)).countable

/-- 正则点集预连通。 -/
theorem isPreconnected_morrey_regular_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) :
    IsPreconnected {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} := by
  have h := isPreconnected_ball_diff_countable_R5 (c := 0) (r := 1)
    (countable_morrey_branch_R5 hu hΓ)
  convert h using 1
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, fun h' => h'.2 hz⟩
  · rintro ⟨hzB, hzn⟩
    by_contra hz
    exact hzn ⟨hzB, hz⟩

/-- 正则点在 `D°` 中稠密：任何含于 `D°` 的非空开集都含正则点。 -/
theorem nonempty_inter_morrey_regular_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {O : Set ℂ} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOB : O ⊆ ball (0 : ℂ) 1) :
    (O ∩ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)}).Nonempty := by
  have hdense := (countable_morrey_branch_R5 hu hΓ).dense_compl ℝ
  obtain ⟨z, hzO, hzc⟩ := hdense.inter_open_nonempty O hO hOne
  refine ⟨z, hzO, ?_⟩
  by_contra hz
  exact hzc ⟨hOB hzO, hz⟩

/-- **Morrey 版局部因子**：`U = diskExtension u`、`V = diskExtension q`，`V` 在 `W ∈ D°` 处 rank 2，
`U z = V W`、`map U (𝓝 z) ≤ map V (𝓝 W)`（`z` 可以是 branch point）⇒ 光滑局部因子 `Φ`，且在 `U` 的
每个正则点上 germ 相等、`dΦ` 单射、`Φ` 是 `ConformalAt`。 -/
theorem exists_morrey_local_factor_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    {z W : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hW : W ∈ ball (0 : ℂ) 1)
    (hval : diskExtension u z = diskExtension q W)
    (hgerm : Filter.map (diskExtension u) (𝓝 z) ≤ Filter.map (diskExtension q) (𝓝 W))
    {O : Set ℂ} (hO : O ∈ 𝓝 W) :
    ∃ (N : Set ℂ) (Φ : ℂ → ℂ), IsOpen N ∧ z ∈ N ∧ N ⊆ ball (0 : ℂ) 1 ∧
      ContDiffOn ℝ ∞ Φ N ∧ Φ z = W ∧ MapsTo Φ N (O ∩ ball (0 : ℂ) 1) ∧
      (∀ z' ∈ N, diskExtension u z' = diskExtension q (Φ z')) ∧
      ∀ z' ∈ N, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z') →
        Filter.map (diskExtension u) (𝓝 z') = Filter.map (diskExtension q) (𝓝 (Φ z')) ∧
        Injective (fderiv ℝ Φ z') ∧ ConformalAt Φ z' := by
  obtain ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, hΦmaps, hfac⟩ :=
    exists_local_factor_R5 isOpen_ball isOpen_ball hu.smoothInterior hq.smoothInterior hz hW
      (hVrank W hW) hval hgerm hO
  refine ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, hΦmaps, hfac, ?_⟩
  intro z' hz' hzi
  have hΦB : Φ z' ∈ ball (0 : ℂ) 1 := (hΦmaps hz').2
  have hVd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (Φ z') :=
    (hq.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds hΦB)).mdifferentiableAt (by simp)
  have hdinj : Injective (fderiv ℝ Φ z') :=
    injective_fderiv_of_local_factor_R5 hNo hz' hΦ hfac hVd hzi
  refine ⟨map_nhds_eq_of_local_factor_R5 hNo hz' hΦ hfac hdinj, hdinj, ?_⟩
  exact conformalAt_of_local_factor_R5 g hNo hz' hΦ hfac hVd hzi (hVrank _ hΦB)
    (hu.conformal z' (hNB hz')) (hq.conformal _ hΦB)

/-- **partner 唯一（无 monodromy）**：`coincidentGermPairs q = ∅`（R3b）⇒ `V` 在 `D°` 中两个 germ 相同、
值相同的点必相等。 -/
theorem eq_of_map_nhds_eq_of_coincidentGermPairs_R5 {q : C(closedDisk, M)}
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅) {W W' : ℂ}
    (hW : W ∈ ball (0 : ℂ) 1) (hW' : W' ∈ ball (0 : ℂ) 1)
    (hval : diskExtension q W = diskExtension q W')
    (hgerm : Filter.map (diskExtension q) (𝓝 W) = Filter.map (diskExtension q) (𝓝 W')) :
    W = W' := by
  by_contra hne
  let x : closedDisk := ⟨W, ball_subset_closedBall hW⟩
  let y : closedDisk := ⟨W', ball_subset_closedBall hW'⟩
  have hmem : (x, y) ∈ coincidentGermPairs (q : closedDisk → M) := by
    refine ⟨fun h => hne (congrArg Subtype.val h), ?_, ?_⟩
    · have h1 := diskExtension_coe (q : closedDisk → M) x
      have h2 := diskExtension_coe (q : closedDisk → M) y
      rw [← h1, ← h2]
      exact hval
    · rw [map_nhds_closedDisk_eq_diskExtension_R3B (q : closedDisk → M) x hW,
        map_nhds_closedDisk_eq_diskExtension_R3B (q : closedDisk → M) y hW']
      exact hgerm
  rw [hcoin] at hmem
  exact hmem

end DifferentialGeometry.Geometry
