import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaWireC11KW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b

set_option autoImplicit false

/-!
# hK 的 seedScale 形 `hKseed`：producer-closed（S-CH11-KWIRE G3a，后缀 `_C11KW`；INTEGRATION-ONLY）

lead 13:4x 裁定 (b)：v3 `hK` 的未缩放 `LocalKappaWideSupply_C11Q` 强于 κ 线可生产（OPEN-1，小种子 event node 数据）。
本文件把 `hK` 槽换成 **尺度 wide** 形（`LocalKappaWideScaledSupply_C11Q4b`，`LocalKappaWideAt_C11Q` 逐字多
`nr t/100 ≤ r`）：

* `seedReducedVolumeScaled_of_blocks_C11KW`：块数据 ⇒ K3（`nodes_of_retention_C11Q6`.1）⇒ K4 尺度
  （`boundedReducedLengthScaled_of_end_C11Q4`）⇒ K5 尺度（`seedReducedVolumeScaled_of_block_C11Q4`，
  URE 块），即 `nonempty_pre841Data_of_retention_C11Q6` 的 κ 段；**无 OPEN**。
* `localKappaWideScaled_of_blocks_C11KW`：K5 尺度 ⇒ 尺度 wide
  （`localKappaWideScaled_of_reducedVolumeScaled_C11Q4b`）。
* `hKseed_of_producers_C11KW`：v3 `hK` 槽逐字，结论换成 `LocalKappaWideScaledSupply_C11Q4b F q.delta
  (diagonalAccuracy_C11S q.delta) q.neckRadius`；**无任何额外 binder**（ADP-1 certified tower ⇒ 块数据，
  KWIRE G2 `blockData_of_certifiedTower_C11KW`）。
* `localKappaP6B_of_wideScaled_C11KW`：`L = 1` 时小种子 `r < nr t/100` 空真 ⇒ 尺度 wide ⇒
  `LocalKappaSupply_P6B`。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 尺度 wide 的 congruence / tower transport -/

theorem LocalKappaWideScaledSupply_C11Q4b.congr_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ δ' : ℝ → ℝ} {α α' : ℝ → ℝ → ℝ} {nr nr' : ℝ → ℝ}
    (hδ : ∀ s, 0 ≤ s → δ s = δ' s) (hα : ∀ A s, 0 ≤ s → α A s = α' A s)
    (hnr : ∀ t, 0 ≤ t → nr t = nr' t) (h : LocalKappaWideScaledSupply_C11Q4b F δ α nr) :
    LocalKappaWideScaledSupply_C11Q4b F δ' α' nr' := by
  intro A L hA hL
  obtain ⟨κ, hκ, hW⟩ := h A L hA hL
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol hscale x hx ρ' hlow hup hball
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  refine hW n t p r hr (fun s hs => ?_) hsmall hvol ?_ x hx ρ' ?_ hup hball
  · have hs0 : 0 ≤ s := by linarith [hs.1]
    rw [hδ s hs0, hα A s hs0]
    exact hacc s hs
  · rw [hnr t ht0]
    exact hscale
  · rw [hnr t ht0]
    exact hlow

theorem LocalKappaWideScaledSupply_C11Q4b.of_tower_eq_C11KW {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F F' : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    {nr : ℝ → ℝ} (h : F'.tower = F.tower) (hW : LocalKappaWideScaledSupply_C11Q4b F' δ α nr) :
    LocalKappaWideScaledSupply_C11Q4b F δ α nr := by
  obtain rfl := rawSurgery_eq_of_tower_eq_C11KW h.symm
  exact hW

/-! ## 2. 块数据 ⇒ K5 尺度 ⇒ 尺度 wide（无 OPEN） -/

/-- **块数据 ⇒ K5（种子尺度）**：`nonempty_pre841Data_of_retention_C11Q6` 的 κ 段。 -/
theorem seedReducedVolumeScaled_of_blocks_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    ∃ v : ℝ → ℝ, SeedReducedVolumeScaled_C11Q4 F N.params.delta
      (diagonalAccuracy_C11S N.params.delta) N.params.neckRadius v := by
  obtain ⟨hK3, hnode, hure⟩ :=
    nodes_of_retention_C11Q6 N rad Df εf cap mf hrad hnr1 hev hdomK3 hdomE hdomU
  have hK4 := boundedReducedLengthScaled_of_end_C11Q4
    (weightedMinBoundEndScaled_of_nodeData_C11Q4 N.params N.records N.Ctime hnode) hK3
    (fun _ _ => le_rfl)
  exact ⟨_, seedReducedVolumeScaled_of_block_C11Q4 (fun A _ => ureBlockKappa_pos_C11Q3 A) hK4
    (seedRegularBlock_of_URE_C11Q4 N.params N.records N.Ctime hure)⟩

/-- **块数据 ⇒ 尺度 wide 供给**（任意 `A L`，种子 `nr t/100 ≤ r`）。 -/
theorem localKappaWideScaled_of_blocks_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g}
    (N : Pre841NativeData_C11K (fun n => (F.tower.history n).toHistory))
    (rad Df εf cap : ℕ → ℝ) (mf : ℕ → ℕ) (hrad : ∀ m, 0 < rad m)
    (hnr1 : ∀ s, 0 ≤ s → N.params.neckRadius s ≤ 1)
    (hev : ∀ n (j : Fin (F.tower.history n).toHistory.eventCount), ∃ m : ℕ,
      preparedSpatialHorizon m < (F.tower.history n).toHistory.time j.succ ∧
      (F.tower.history n).toHistory.time j.succ ≤ (3 : ℝ) ^ m ∧
      N.params.delta ((F.tower.history n).toHistory.time j.succ) ≤ cap m ∧
      (∀ T ∈ Icc ((F.tower.history n).toHistory.time j.succ)
          (2 * (F.tower.history n).toHistory.time j.succ),
        rad (m + 1) ≤ N.params.neckRadius T) ∧
      (∀ A : ℝ, 0 < A → N.params.delta ((F.tower.history n).toHistory.time j.succ) <
        diagonalAccuracy_C11S N.params.delta A ((F.tower.history n).toHistory.time j.succ) →
        A < 12 * (3 : ℝ) ^ m) ∧
      ∀ b', ∃ raw : ((F.tower.history n).toHistory.event j).PresentedStaticCap N.params.fixed
          (Df m) (mf m) (εf m) b',
        raw.hasCanonicalWindow ∧ raw.neck.scale = ((N.records n j).static b').neck.scale ∧
        ∀ z, raw.inclusion (raw.witness.cap z) =
          ((N.records n j).static b').inclusion (((N.records n j).static b').witness.cap z))
    (hdomK3 : ∀ m : ℕ,
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ Df m ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤ mf m ∧
      εf m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap m ≤ (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤
        Df (m + 1) ∧
      (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2 ≤
        mf (m + 1) ∧
      εf (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ∧
      cap (m + 1) ≤
        (k3BlockConsts_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1)
    (hdomE : ∀ m : ℕ,
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (eventBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2)
    (hdomU : ∀ m : ℕ,
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.1 ≤ Df m ∧
      (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.1 ≤ mf m ∧
      εf m ≤ (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).1 ∧
      cap m ≤
        (ureBlockRequest_C11Q6 P g N.params.recenterConstant N.Ctime m (rad (m + 1))).2.2.2) :
    LocalKappaWideScaledSupply_C11Q4b F N.params.delta (diagonalAccuracy_C11S N.params.delta)
      N.params.neckRadius := by
  obtain ⟨v, hK5⟩ := seedReducedVolumeScaled_of_blocks_C11KW N rad Df εf cap mf hrad hnr1 hev
    hdomK3 hdomE hdomU
  exact localKappaWideScaled_of_reducedVolumeScaled_C11Q4b hK5

/-! ## 3. `hKseed_of_producers_C11KW` -/

/-- **`hK` 槽的 seedScale 形（producer-closed）**：v3 `hK` 的 binder 逐字，结论换成尺度 wide。
`εκ := 1`；无任何额外 binder。 -/
theorem hKseed_of_producers_C11KW (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εκ : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εκ Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      (∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
        q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
          diagonalAccuracy_C11S q.delta A
            ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
        A < 12 * (3 : ℝ) ^ m) →
      pB.modelAccuracy ≤ εκ Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta) q.neckRadius := by
  refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
  intro pB Γ Cdist εReserve T hcert F q hTower hq _hguard _hacc _hrad _hord
  obtain ⟨F', hF', N, rad, Df, εf, cap, mf, hdiagN, hrad, hnr1, hev, hdomK3, hdomE, hdomU⟩ :=
    blockData_of_certifiedTower_C11KW T hcert
  have hwide := localKappaWideScaled_of_blocks_C11KW N rad Df εf cap mf hrad hnr1 hev hdomK3
    hdomE hdomU
  refine LocalKappaWideScaledSupply_C11Q4b.of_tower_eq_C11KW (hF'.trans hTower.symm) ?_
  refine hwide.congr_C11KW (fun s hs => ?_) (fun A s hs => ?_) (fun t ht => ?_)
  · exact (hdiagN s hs).1.trans (hq s hs).1.symm
  · have hm : 0 ≤ max 0 (A / 4) := le_max_left _ _
    change 2 * N.params.delta (max 0 (A / 4)) = 2 * q.delta (max 0 (A / 4))
    rw [(hdiagN _ hm).1.trans (hq _ hm).1.symm]
  · exact (hdiagN t ht).2.trans (hq t ht).2.symm

/-! ## 4. consumer：尺度 wide ⇒ P6B 局部 κ（`L = 1`，小种子空真） -/

/-- `L = 1`：`ρ' ∈ [nr t/100, r]` 非空 ⇒ `nr t/100 ≤ r`，尺度前提自动成立。 -/
theorem localKappaP6B_of_wideScaled_C11KW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr : ℝ → ℝ}
    (h : LocalKappaWideScaledSupply_C11Q4b F δ α nr) : LocalKappaSupply_P6B F δ α nr := by
  intro A hA
  obtain ⟨κ, hκ, hW⟩ := h A 1 hA one_pos
  refine ⟨κ, hκ, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ρ' hlow hup hball
  exact hW n t p r hr hacc hsmall hvol (hlow.trans hup) x hx ρ' hlow (by rwa [one_mul]) hball

/-- consumer：`hKseed` 槽的输出（某个 `T` 上）⇒ P6B 局部 κ。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (hKseed_of_producers_C11KW P g) := hKseed_of_producers_C11KW P g

end GC.LongTime.Ch11
