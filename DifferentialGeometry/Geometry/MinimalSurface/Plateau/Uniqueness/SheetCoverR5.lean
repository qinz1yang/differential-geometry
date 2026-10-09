import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.SheetPartnerR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.NormalizedUniquenessR5
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# O-MY-R5：R5-B(i) 的覆盖与可去性零件

* `image_mem_nhds_of_contDiffAt_R5`：`C^∞` 且导数单射 ⇒ 开映射（局部）。
* `punctured_subset_morrey_regular_R5`：branch points 孤立（每点有去心球含于正则点集）。
* `exists_differentiableOn_extension_R5`：开盘中去掉孤立点的有界全纯函数可去（D-3 的 single-valued
  removability：此时函数已单值）。
* `partner_of_tendsto_R5`：沿给定序列的 germ 闭性（`image_germs_eq_of_regular_interior_limit`）。
* `sheetPartner_image_cover_R5`：`φ(Ω_in) ⊇ D_r \ C`，`C := closedBall 0 1 ∩ V⁻¹(U(B))` 可数——
  properness（`u(∂D) ⊆ Γ`、`q⁻¹(Γ) ⊆ rS¹` ⇒ 极限不落在 `∂D`）+ 闭性 + 连通性。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- `C^∞` 且导数单射 ⇒ 邻域的像是邻域。 -/
theorem image_mem_nhds_of_contDiffAt_R5 {Φ : ℂ → ℂ} {z : ℂ} (hΦ : ContDiffAt ℝ ∞ Φ z)
    (hinj : Injective (fderiv ℝ Φ z)) {N : Set ℂ} (hN : N ∈ 𝓝 z) : Φ '' N ∈ 𝓝 (Φ z) := by
  have hbij : Bijective (fderiv ℝ Φ z) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  let D : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ Φ z).toLinearMap hbij).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt Φ (D : ℂ →L[ℝ] ℂ) z := by
    have h := hΦ.hasStrictFDerivAt (by simp)
    convert h using 1
    exact ContinuousLinearMap.ext fun v => rfl
  rw [← hstrict.map_nhds_eq_of_equiv]
  exact image_mem_map hN

/-- 开盘中去掉一个"每点有去心球含于 `R`"的集合后的有界全纯函数可延拓为全纯函数。 -/
theorem exists_differentiableOn_extension_R5 {f : ℂ → ℂ} {R : Set ℂ} (hRo : IsOpen R)
    (hdisc : ∀ b ∈ ball (0 : ℂ) 1, ∃ ε > 0, ball b ε ⊆ ball (0 : ℂ) 1 ∧
      ∀ z ∈ ball b ε, z ≠ b → z ∈ R)
    (hd : DifferentiableOn ℂ f R) {C : ℝ} (hb : ∀ z ∈ R, ‖f z‖ ≤ C) :
    ∃ f' : ℂ → ℂ, DifferentiableOn ℂ f' (ball (0 : ℂ) 1) ∧ ∀ z ∈ R, f' z = f z := by
  classical
  let f' : ℂ → ℂ := fun z => if z ∈ R then f z else limUnder (𝓝[≠] z) f
  refine ⟨f', fun b hbB => ?_, fun z hz => ite_eq_left hz⟩
  apply DifferentiableAt.differentiableWithinAt
  by_cases hbR : b ∈ R
  · have heq : f' =ᶠ[𝓝 b] f := by
      filter_upwards [hRo.mem_nhds hbR] with z hz
      exact ite_eq_left hz
    exact (hd.differentiableAt (hRo.mem_nhds hbR)).congr_of_eventuallyEq heq
  · obtain ⟨ε, hε, -, hpunct⟩ := hdisc b hbB
    have hs : ball b ε ∈ 𝓝 b := isOpen_ball.mem_nhds (mem_ball_self hε)
    have hdiff : DifferentiableOn ℂ f (ball b ε \ {b}) :=
      hd.mono fun z hz => hpunct z hz.1 hz.2
    have hbdd : BddAbove (norm ∘ f '' (ball b ε \ {b})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact hb z (hpunct z hz.1 hz.2)
    have hupd := Complex.differentiableOn_update_limUnder_of_bddAbove hs hdiff hbdd
    have heq : f' =ᶠ[𝓝 b] update f b (limUnder (𝓝[≠] b) f) := by
      filter_upwards [hs] with z hz
      by_cases hzb : z = b
      · subst hzb
        simp [f', hbR]
      · have hzR := hpunct z hz hzb
        simp [f', hzR, hzb]
    exact (hupd.differentiableAt hs).congr_of_eventuallyEq heq

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- branch points 孤立：每个 `b ∈ D°` 有含于 `D°` 的球，去掉 `b` 后全是正则点。 -/
theorem punctured_subset_morrey_regular_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) {b : ℂ} (hb : b ∈ ball (0 : ℂ) 1) :
    ∃ ε > 0, ball b ε ⊆ ball (0 : ℂ) 1 ∧ ∀ z ∈ ball b ε, z ≠ b →
      z ∈ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} := by
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.mp hb
  set ρ : ℝ := (‖b‖ + 1) / 2 with hρ
  have hbρ : ‖b‖ < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hfin := hu.finite_not_injective_mfderiv_of_isCompact hΓ (isCompact_closedBall 0 ρ)
    (closedBall_subset_ball hρ1)
  set F : Set ℂ := {w ∈ closedBall (0 : ℂ) ρ | ¬ Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) w)} \ {b} with hF
  have hFcl : IsClosed F := (hfin.subset sdiff_subset).isClosed
  have hbF : b ∉ F := fun h => h.2 rfl
  have h1 : Fᶜ ∈ 𝓝 b := hFcl.isOpen_compl.mem_nhds hbF
  have h2 : ball (0 : ℂ) ρ ∈ 𝓝 b := isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hbρ)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h1 h2)
  refine ⟨ε, hε, fun z hz => ball_subset_ball hρ1.le (hεsub hz).2, fun z hz hzb => ?_⟩
  have hzρ := (hεsub hz).2
  refine ⟨ball_subset_ball hρ1.le hzρ, ?_⟩
  by_contra hni
  exact (hεsub hz).1 ⟨⟨ball_subset_closedBall hzρ, hni⟩, hzb⟩

/-- 沿给定序列的 germ 闭性：`x n → z`（`z` 正则）、`W n → w ∈ D°`、每项 germ 相等 ⇒ 极限处值与 germ 相等。 -/
theorem partner_of_tendsto_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q) (hd3 : Module.finrank ℝ E = 3)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    {z w : ℂ} (hzB : z ∈ ball (0 : ℂ) 1) (hwB : w ∈ ball (0 : ℂ) 1)
    (hzi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    {x W : ℕ → ℂ} (hx : Tendsto x atTop (𝓝 z)) (hW : Tendsto W atTop (𝓝 w))
    (hval : ∀ n, diskExtension u (x n) = diskExtension q (W n))
    (hgerm : ∀ n, Filter.map (diskExtension u) (𝓝 (x n)) =
      Filter.map (diskExtension q) (𝓝 (W n))) :
    diskExtension u z = diskExtension q w ∧
      Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 w) := by
  have hUc : Continuous (diskExtension u) := u.continuous.comp diskRetraction_lipschitz.continuous
  have hVc : Continuous (diskExtension q) := q.continuous.comp diskRetraction_lipschitz.continuous
  have hv : diskExtension u z = diskExtension q w :=
    tendsto_nhds_unique (((hUc.tendsto z).comp hx).congr hval) ((hVc.tendsto w).comp hW)
  exact ⟨hv, IsMorreyDisk.image_germs_eq_of_regular_interior_limit hu hq hd3 hzB hwB hv hzi
    (hVrank w hwB) hx hW (Filter.Eventually.of_forall hgerm)⟩

/-- `u` 的边界点落在 trace loop 的像里。 -/
theorem diskExtension_mem_range_of_norm_eq_one_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) {z : ℂ} (hz : ‖z‖ = 1) :
    diskExtension u z ∈ range Γ := by
  obtain ⟨θ, hθ⟩ := exists_diskBoundary_coe_eq_R5 hz
  obtain ⟨σ, -, htr⟩ := hu.trace
  have hmem : z ∈ closedDisk := by simpa [Metric.mem_closedBall, dist_zero_right] using hz.le
  have hpt : (⟨z, hmem⟩ : closedDisk) = diskBoundary θ := Subtype.ext hθ.symm
  refine ⟨σ θ, ?_⟩
  have h1 : diskExtension u z = u (diskBoundary θ) := by
    rw [← hpt]
    exact diskExtension_coe u ⟨z, hmem⟩
  have h2 : diskTrace u θ = Γ (σ θ) := by rw [htr]; rfl
  rw [h1]
  exact h2.symm

/-- **覆盖**：`φ(Ω_in) ⊇ D_r \ C`，`C := closedBall 0 1 ∩ V⁻¹(U(B))`（可数，作为假设给出）。 -/
theorem sheetPartner_image_cover_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q) (hd3 : Module.finrank ℝ E = 3)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅) {r : ℝ} (hr1 : r < 1)
    (hfiber : ∀ w ∈ closedBall (0 : ℂ) 1, diskExtension q w ∈ range Γ → ‖w‖ = r)
    (hRo : IsOpen {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)})
    (hCc : (closedBall (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (diskExtension u ''
      (ball (0 : ℂ) 1 \ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)}))).Countable)
    (hne : ({z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
        Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)}).Nonempty) :
    ball (0 : ℂ) r \ (closedBall (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (diskExtension u ''
      (ball (0 : ℂ) 1 \ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)}))) ⊆
      sheetPartner_R5 u q '' {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
        Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
        ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
          Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)} := by
  set R : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} with hR
  set Ω : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
        Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)} with hΩ
  set C : Set ℂ := closedBall (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (diskExtension u ''
      (ball (0 : ℂ) 1 \ R)) with hC
  set φ := sheetPartner_R5 u q with hφ
  have hr1' : r ≤ 1 := hr1.le
  -- `Ω` 上的性质
  have hprops := fun z (hz : z ∈ Ω) =>
    sheetInside_props_R5 hu hq hVrank hcoin hr1' hRo hz
  have hφΩ : ∀ z ∈ Ω, ‖φ z‖ < r ∧ diskExtension u z = diskExtension q (φ z) ∧
      Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 (φ z)) := by
    intro z hz
    obtain ⟨hzB, hzi, W, hWr, hval, hgerm⟩ := hz
    have hWB : W ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_lt_of_le hWr hr1')
    have hpW : φ z = W := sheetPartner_eq_R5 hcoin hWB hval hgerm
    rw [hpW]
    exact ⟨hWr, hval, hgerm⟩
  -- `S := φ '' Ω` 开
  have hSo : IsOpen (φ '' Ω) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨N, hN, hNΩ, Φ, hΦ, -, hΦi, hφΦ, -, -⟩ := hprops z hz
    have him := image_mem_nhds_of_contDiffAt_R5 hΦ hΦi hN
    have heqim : Φ '' N = φ '' N := by
      apply image_congr
      intro z' hz'
      exact (hφΦ z' hz').symm
    have hzΦ : φ z = Φ z := hφΦ z (mem_of_mem_nhds hN)
    rw [hzΦ]
    refine Filter.mem_of_superset him ?_
    rw [heqim]
    exact image_mono hNΩ
  have hSr : φ '' Ω ⊆ ball (0 : ℂ) r := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr (hφΩ z hz).1
  -- 连通性
  have hYc : IsPreconnected (ball (0 : ℂ) r \ C) := isPreconnected_ball_diff_countable_R5 hCc
  have hYS : ((ball (0 : ℂ) r \ C) ∩ φ '' Ω).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    have hSne : (φ '' Ω).Nonempty := ⟨φ z, z, hz, rfl⟩
    obtain ⟨w, hwS, hwC⟩ := (hCc.dense_compl ℝ).inter_open_nonempty _ hSo hSne
    exact ⟨w, ⟨hSr hwS, hwC⟩, hwS⟩
  refine hYc.subset_of_closure_inter_subset hSo hYS ?_
  rintro w ⟨hwcl, hwr, hwC⟩
  have hwB : w ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr (lt_of_lt_of_le (mem_ball_zero_iff.mp hwr) hr1')
  obtain ⟨y, hyS, hylim⟩ := mem_closure_iff_seq_limit.mp hwcl
  choose x hxΩ hxy using hyS
  have hxK : ∀ n, x n ∈ closedBall (0 : ℂ) 1 := fun n => ball_subset_closedBall (hxΩ n).1
  obtain ⟨z, hzK, k, hk, hxlim⟩ := (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hxK
  have hylim' : Tendsto (fun n => φ (x (k n))) atTop (𝓝 w) := by
    have := hylim.comp hk.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hxy (k n)).symm
  have hUc : Continuous (diskExtension u) := u.continuous.comp diskRetraction_lipschitz.continuous
  have hVc : Continuous (diskExtension q) := q.continuous.comp diskRetraction_lipschitz.continuous
  have hval : diskExtension u z = diskExtension q w :=
    tendsto_nhds_unique (((hUc.tendsto z).comp hxlim).congr fun n => (hφΩ _ (hxΩ (k n))).2.1)
      ((hVc.tendsto w).comp hylim')
  have hwK : w ∈ closedBall (0 : ℂ) 1 := ball_subset_closedBall hwB
  rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hzK) with hz1 | hz1
  · -- 极限落在 `∂D`：`V w ∈ Γ` ⇒ `‖w‖ = r`，矛盾
    exfalso
    have hmem := diskExtension_mem_range_of_norm_eq_one_R5 hu hz1
    rw [hval] at hmem
    have := hfiber w hwK hmem
    exact (ne_of_lt (mem_ball_zero_iff.mp hwr)) this
  · have hzB : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz1
    by_cases hzR : z ∈ R
    · obtain ⟨hv, hg⟩ := partner_of_tendsto_R5 hu hq hd3 hVrank hzB hwB hzR.2 hxlim hylim'
        (fun n => (hφΩ _ (hxΩ (k n))).2.1) (fun n => (hφΩ _ (hxΩ (k n))).2.2)
      have hzΩ : z ∈ Ω := ⟨hzB, hzR.2, w, mem_ball_zero_iff.mp hwr, hv, hg⟩
      exact ⟨z, hzΩ, sheetPartner_eq_R5 hcoin hwB hv hg⟩
    · exfalso
      exact hwC ⟨hwK, z, ⟨hzB, hzR⟩, hval⟩

end DifferentialGeometry.Geometry
