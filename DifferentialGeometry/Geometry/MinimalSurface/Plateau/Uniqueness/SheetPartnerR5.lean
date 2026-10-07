import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.SheetContinuationLocalR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.TwoMapGermClosure
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PiecewiseAreaConsumerAREA

/-!
# O-MY-R5：R5-B(i) 的单值 partner 函数 `sheetPartner_R5`

`sheetPartner_R5 u q z`：若 `z` 处存在 `W ∈ D°` 使 `U z = V W` 且 image germ 相等，则取之（R3b 下唯一，
`sheetPartner_eq_R5`），否则取 0。在"内部 partner 集"
`Ω_in := {z ∈ D° | U 在 z 处 rank 2 ∧ ∃ W, ‖W‖ < r ∧ U z = V W ∧ germ 相等}` 上：
* `isOpen_sheetInside_R5`：`Ω_in` 开（局部因子 + germ 传播）；
* `sheetInside_props_R5`：`φ := sheetPartner_R5 u q` 在 `Ω_in` 上 `C^∞`、`ConformalAt`、`‖φ‖ < r`、
  `U = V ∘ φ`、
  `dφ` 单射；`sheetPartner_localBiLip_R5`：局部 bi-Lipschitz；
* `exists_partner_of_mem_closure_R5`：`U` 的正则点若在 `Ω_in` 的闭包中，则有 partner `W ∈ closedBall 0 r`
  （`IsMorreyDisk.image_germs_eq_of_regular_interior_limit` 的闭性 + 紧性；`r < 1` ⇒ 不逃逸到 `∂D`）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- R5-B(i) 的单值 partner 函数。 -/
def sheetPartner_R5 (u q : C(closedDisk, M)) (z : ℂ) : ℂ := by
  classical
  exact if h : ∃ W : ℂ, W ∈ ball (0 : ℂ) 1 ∧ diskExtension u z = diskExtension q W ∧
      Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W) then h.choose
    else 0

/-- partner 唯一 ⇒ `sheetPartner_R5` 取到它。 -/
theorem sheetPartner_eq_R5 {u q : C(closedDisk, M)}
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅) {z W : ℂ}
    (hW : W ∈ ball (0 : ℂ) 1) (hval : diskExtension u z = diskExtension q W)
    (hgerm : Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)) :
    sheetPartner_R5 u q z = W := by
  classical
  have h : ∃ W : ℂ, W ∈ ball (0 : ℂ) 1 ∧ diskExtension u z = diskExtension q W ∧
      Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W) :=
    ⟨W, hW, hval, hgerm⟩
  unfold sheetPartner_R5
  rw [dite_eq_left h]
  obtain ⟨h1, h2, h3⟩ := h.choose_spec
  exact eq_of_map_nhds_eq_of_coincidentGermPairs_R5 hcoin h1 hW (h2.symm.trans hval)
    (h3.symm.trans hgerm)

/-- 局部因子与 `sheetPartner_R5` 在正则点上一致。 -/
theorem sheetPartner_local_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅)
    {z W : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hW : W ∈ ball (0 : ℂ) 1)
    (hval : diskExtension u z = diskExtension q W)
    (hgerm : Filter.map (diskExtension u) (𝓝 z) ≤ Filter.map (diskExtension q) (𝓝 W))
    {O : Set ℂ} (hO : O ∈ 𝓝 W) :
    ∃ (N : Set ℂ) (Φ : ℂ → ℂ), IsOpen N ∧ z ∈ N ∧ N ⊆ ball (0 : ℂ) 1 ∧
      ContDiffOn ℝ ∞ Φ N ∧ Φ z = W ∧ MapsTo Φ N (O ∩ ball (0 : ℂ) 1) ∧
      (∀ z' ∈ N, diskExtension u z' = diskExtension q (Φ z')) ∧
      ∀ z' ∈ N, Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z') →
        sheetPartner_R5 u q z' = Φ z' ∧
        Filter.map (diskExtension u) (𝓝 z') = Filter.map (diskExtension q) (𝓝 (Φ z')) ∧
        Injective (fderiv ℝ Φ z') ∧ ConformalAt Φ z' := by
  obtain ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, hΦmaps, hfac, hreg⟩ :=
    exists_morrey_local_factor_R5 hu hq hVrank hz hW hval hgerm hO
  refine ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, hΦmaps, hfac, fun z' hz' hzi => ?_⟩
  obtain ⟨hg', hd', hc'⟩ := hreg z' hz' hzi
  exact ⟨sheetPartner_eq_R5 hcoin (hΦmaps hz').2 (hfac z' hz') hg', hg', hd', hc'⟩

/-- 内部 partner 集 `Ω_in` 开，且 `sheetPartner_R5` 在其上光滑、共形、`‖φ‖ < r`、`U = V ∘ φ`、
`dφ` 单射、germ 相等。 -/
theorem sheetInside_props_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅) {r : ℝ} (hr1 : r ≤ 1)
    (hRo : IsOpen {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)})
    {z : ℂ} (hz : z ∈ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
        Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)}) :
    ∃ N ∈ 𝓝 z, (N ⊆ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
        Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)}) ∧
      ∃ Φ : ℂ → ℂ, ContDiffAt ℝ ∞ Φ z ∧ ConformalAt Φ z ∧ Injective (fderiv ℝ Φ z) ∧
        (∀ z' ∈ N, sheetPartner_R5 u q z' = Φ z') ∧
        ‖sheetPartner_R5 u q z‖ < r ∧
        diskExtension u z = diskExtension q (sheetPartner_R5 u q z) := by
  obtain ⟨hzB, hzi, W, hWr, hval, hgerm⟩ := hz
  have hW : W ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_lt_of_le hWr hr1)
  obtain ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, hΦmaps, hfac, hreg⟩ :=
    sheetPartner_local_R5 hu hq hVrank hcoin hzB hW hval hgerm.le
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hWr) : ball (0 : ℂ) r ∈ 𝓝 W)
  set R : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z)} with hR
  have hNR : N ∩ R ∈ 𝓝 z := Filter.inter_mem (hNo.mem_nhds hzN) (hRo.mem_nhds ⟨hzB, hzi⟩)
  obtain ⟨hp, -, hd, hc⟩ := hreg z hzN hzi
  refine ⟨N ∩ R, hNR, ?_, Φ, (hΦ z hzN).contDiffAt (hNo.mem_nhds hzN), hc, hd,
    fun z' hz' => (hreg z' hz'.1 hz'.2.2).1, ?_, ?_⟩
  · rintro z' ⟨hz'N, hz'B, hz'i⟩
    obtain ⟨hp', hg', -, -⟩ := hreg z' hz'N hz'i
    exact ⟨hz'B, hz'i, Φ z', mem_ball_zero_iff.mp (hΦmaps hz'N).1, hfac z' hz'N, hg'⟩
  · rw [hp, hΦz]
    exact hWr
  · rw [hp]
    exact hfac z hzN

/-- 局部 bi-Lipschitz：`C^∞` 且导数单射 ⇒ 邻域上 Lipschitz 且有下界。 -/
theorem exists_localBiLip_of_contDiffAt_R5 {Φ : ℂ → ℂ} {z : ℂ} (hΦ : ContDiffAt ℝ ∞ Φ z)
    (hinj : Injective (fderiv ℝ Φ z)) :
    ∃ W ∈ 𝓝 z, ∃ K L : ℝ≥0, LipschitzOnWith K Φ W ∧
      ∀ y ∈ W, ∀ y' ∈ W, edist y y' ≤ (L : ℝ≥0∞) * edist (Φ y) (Φ y') := by
  have hs : HasStrictFDerivAt Φ (fderiv ℝ Φ z) z := hΦ.hasStrictFDerivAt (by simp)
  obtain ⟨W₁, hW₁, hlip⟩ := hs.exists_lipschitzOnWith_of_nnnorm_lt (‖fderiv ℝ Φ z‖₊ + 1)
    (by simp)
  obtain ⟨W₂, hW₂, L, hL⟩ := exists_nhds_lower_bound_of_hasStrictFDerivAt_AREA hs hinj
  exact ⟨W₁ ∩ W₂, Filter.inter_mem hW₁ hW₂, _, L, hlip.mono inter_subset_left,
    fun y hy y' hy' => hL y hy.2 y' hy'.2⟩

/-- **闭性（不逃逸）**：`U` 的正则点 `z` 若在 `Ω_in` 的闭包中，则存在 `W ∈ closedBall 0 r` 使
`U z = V W` 且 germ 相等（`r < 1` ⇒ `W` 在 `q` 的内部）。 -/
theorem exists_partner_of_mem_closure_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u)
    (hq : IsMorreyDisk g γ q) (hd3 : Module.finrank ℝ E = 3)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    {r : ℝ} (hr1 : r < 1) {z : ℂ} (hzB : z ∈ ball (0 : ℂ) 1)
    (hzi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hcl : z ∈ closure {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ diskExtension u z = diskExtension q W ∧
        Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W)}) :
    ∃ W ∈ closedBall (0 : ℂ) r, diskExtension u z = diskExtension q W ∧
      Filter.map (diskExtension u) (𝓝 z) = Filter.map (diskExtension q) (𝓝 W) := by
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose W hWr hWval hWgerm using fun n => (hxmem n).2.2
  have hWK : ∀ n, W n ∈ closedBall (0 : ℂ) r := fun n =>
    mem_closedBall_zero_iff.mpr (hWr n).le
  obtain ⟨W₀, hW₀K, k, hk, hWlim⟩ := (isCompact_closedBall (0 : ℂ) r).tendsto_subseq hWK
  have hW₀B : W₀ ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hW₀K) hr1)
  have hUc : Continuous (diskExtension u) := u.continuous.comp diskRetraction_lipschitz.continuous
  have hVc : Continuous (diskExtension q) := q.continuous.comp diskRetraction_lipschitz.continuous
  have hxk : Tendsto (x ∘ k) atTop (𝓝 z) := hxlim.comp hk.tendsto_atTop
  have hval : diskExtension u z = diskExtension q W₀ := by
    have h1 : Tendsto (fun n => diskExtension u (x (k n))) atTop (𝓝 (diskExtension u z)) :=
      (hUc.tendsto z).comp hxk
    have h2 : Tendsto (fun n => diskExtension q (W (k n))) atTop (𝓝 (diskExtension q W₀)) :=
      (hVc.tendsto W₀).comp hWlim
    exact tendsto_nhds_unique (h1.congr fun n => hWval (k n)) h2
  refine ⟨W₀, hW₀K, hval, ?_⟩
  exact IsMorreyDisk.image_germs_eq_of_regular_interior_limit hu hq hd3 hzB hW₀B hval hzi
    (hVrank W₀ hW₀B) hxk hWlim (Filter.Eventually.of_forall fun n => hWgerm (k n))

end DifferentialGeometry.Geometry
