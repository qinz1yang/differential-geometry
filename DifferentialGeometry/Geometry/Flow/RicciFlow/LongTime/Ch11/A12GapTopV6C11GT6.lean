import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV4C11SC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV5C11KW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6

set_option autoImplicit false

/-!
# A12′ 顶层缺口定理第六版：`hP6b` 按 R-C11-8 D-4 schema 收窄（O-CH11-GAPTOP6 G1，后缀 `_C11GT6`）

设计：`docs/geometrization/chapter8/design-C11-gaptop6-20261007.md`。相对 v5（`_C11KW`）/ v4（`_C11SC`）：

* **`hP6b′`**（D-4 schema 逐字落 Lean）：只对携带 W0 预算证书（`BudgetCertificate_C11GT2`）与
  **同构造保留供给** `SameConstructionRetentionSupply_C11GT6 T` 的 budget tower `T` 成立；`∀ F q` 保留
  （实现该构造：`F.tower = T.toChain.tower`、`q` = chain diagonal），ModelSmallness 照旧；结论常数
  = closed-term ceiling `C1P6_C11GT6 X1 Γ / C2P6_C11GT6 X2 Γ`（`P6CeilingC11GT6`，selection 之前固定）。
* **`SameConstructionRetentionSupply_C11GT6 T`**（lead 登记的合同 Prop）：`∃ F₀ q₀ κ records` 同一 tower 上
  astra 的独立产出——参数识别、κ / noncollapsing、κ-volume（`LocalKappaWideScaledSupply_C11Q4b`）、
  records（canonical window、S9 recent、S10 linked、S14 late）、S5 native canonical（旧 ceiling）、S11；
  不含 `CanonicalLateCore` / S15 / `hspine` / S8 / S16。
* **tower-congruence**：`canonicalLateCore_congr_tower_C11GT6`（`CanonicalLateCore_P6X` 只读 `F.tower`）。
* **`hspine′`**：v5 `hspine` 逐字（种子限制 window），`hb` 常数换 `C1P6 / C2P6`；直接喂
  `s8_of_smallVolSeed_C11KW` 的 S8 槽（大常数 witness 不能缩小，不经 old-ceiling adapter）。
* `hKseed`（`hKseed_of_producers_C11KW`）、`hfull`（`hfull_ceiling_C11SC`）、SCRS（同一 `T` 上的
  retention / κ-wide / S11 / S14 / S10）在证明体内供给 ⇒ **binder 只有 `hspine′ hP6b′`**。
* `a12EnhancedFull_of_gaps_v6_gen_C11GT6`：对 ceiling 附加项 `X1 X2` 泛型；主定理
  `a12EnhancedFull_of_gaps_v6_C11GT6` 取标准 `p6X1std_C11GT6 / p6X2std_C11GT6`。
* 方向记录：`hP6bV6_of_v3_C11GT6`（v3 / v5 的 `hP6b` ⇒ `hP6b′`：新义务更弱）、
  `hspineV5_of_v6_C11GT6`（`hspine′` ⇒ v5 `hspine`：新 spine 义务更强，反向不成立）。
-/

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11

universe u

/-! ## 1. 同构造保留供给（SCRS）与 tower-congruence -/

/-- **`SameConstructionRetentionSupply_C11GT6 T`**（R-C11-8 D-4；lead 登记的合同 Prop）：budget tower `T`
的**同一次构造**的 astra 独立产出（同 tower 的 `F₀`、diagonal `q₀`、`κ`、records）：
(1) 参数识别；(2) κ 与 noncollapsing；(3) κ-volume（种子尺度 wide）；(4) 参数单调 / 小性；
(5) records（canonical window、S9、S10、S14）；(6) S5 native canonical（旧 ceiling）+ S11。 -/
def SameConstructionRetentionSupply_C11GT6 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve) : Prop :=
  ∃ (F₀ : GC.Interface.RawSurgery P g) (q₀ : CutoffParameters) (κ : ℝ → ℝ)
    (records : CutoffRecords_C11S F₀ q₀),
    (F₀.tower = T.toChain.tower ∧
      (∀ t : ℝ, 0 ≤ t → q₀.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q₀.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) ∧
      (q₀.fixed = pB.fixed ∧ q₀.modelRadius = pB.modelRadius ∧
        q₀.modelOrder = pB.modelOrder ∧ q₀.modelAccuracy = pB.modelAccuracy ∧
        q₀.recenterConstant = pB.recenterConstant)) ∧
    ((∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F₀.tower.history n).NoncollapsedBefore (κ t) Γ.epsilon t) ∧
    LocalKappaWideScaledSupply_C11Q4b F₀ q₀.delta (diagonalAccuracy_C11S q₀.delta)
      q₀.neckRadius ∧
    (AntitoneOn q₀.delta (Ici 0) ∧ AntitoneOn q₀.neckRadius (Ici 0) ∧
      Tendsto q₀.delta atTop (𝓝 0)) ∧
    ((∀ n i b, ((records n i).static b).hasCanonicalWindow) ∧ RecentCutoffSupply_C11S records ∧
      LinkedWindowsSupply_C11E records ∧ LateLinkedRecordsSupply_C11E F₀ q₀) ∧
    HistoryCanonicalSupply_C11S F₀ q₀.neckRadius Γ.epsilon (max Γ.C1s Γ.Cbirth)
      (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) ∧
    TimeDerivativeSupply_C11E F₀ q₀.neckRadius Γ.Ctime

/-- **tower-congruence**：`CanonicalLateCore_P6X` 只读 `F.tower`，同 tower 的两个 surgery 等价地满足它。 -/
theorem canonicalLateCore_congr_tower_C11GT6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F F' : GC.Interface.RawSurgery P g} (h : F.tower = F'.tower) {ε C1 C2 : ℝ}
    (hF : CanonicalLateCore_P6X F ε C1 C2) : CanonicalLateCore_P6X F' ε C1 C2 := by
  obtain ⟨tw, ec⟩ := F
  obtain ⟨tw', ec'⟩ := F'
  change tw = tw' at h
  subst h
  exact hF

/-- `CanonicalLateCore_P6X` 对常数上调稳定（同 `K₁ T`）。 -/
theorem canonicalLateCore_mono_C11GT6 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 C1' C2' : ℝ}
    (h : CanonicalLateCore_P6X F ε C1 C2) (h1 : C1 ≤ C1') (h2 : C2 ≤ C2') :
    CanonicalLateCore_P6X F ε C1' C2' := by
  intro A hA
  obtain ⟨K₁, T, hK₁, hT, hS⟩ := h A hA
  refine ⟨K₁, T, hK₁, hT, fun n t p r hTt ht hs hv y hy hK => ?_⟩
  obtain ⟨W, hW⟩ := hS n t p r hTt ht hs hv y hy hK
  exact ⟨W.enlargeConstants h1 h2, hW.enlarge_constants h1 h2⟩

/-- **"∀F 保留"的 producer 侧用法**：SCRS 的 `F₀` 上得到的 `CanonicalLateCore` 送到任一实现该构造的 `F`。 -/
theorem canonicalLateCore_of_scrs_C11GT6 {pB : CutoffParameters} {Γ : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve} {ε C1 C2 : ℝ}
    (hcore : ∀ F₀ : GC.Interface.RawSurgery P g, F₀.tower = T.toChain.tower →
      CanonicalLateCore_P6X F₀ ε C1 C2)
    (hS : SameConstructionRetentionSupply_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (hF : F.tower = T.toChain.tower) :
    CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨F₀, -, -, -, ⟨hF₀, -⟩, -⟩ := hS
  exact canonicalLateCore_congr_tower_C11GT6 (hF₀.trans hF.symm) (hcore F₀ hF₀)

/-! ## 2. v6 顶层（ceiling 泛型引擎） -/

/-- **A12′ v6 引擎（ceiling 泛型）**：binder `hspine′ hP6b′`（常数 `C1P6_C11GT6 X1 Γ / C2P6_C11GT6 X2 Γ`）；
`hKseed`、`hfull`、SCRS 在证明体内由 producer / 同一构造供给。 -/
theorem a12EnhancedFull_of_gaps_v6_gen_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupply_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, hmake⟩ := hpbase_of_provider_C11GT3 P g
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed_of_producers_C11KW P g
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull_ceiling_C11SC P g
  obtain ⟨ε₀, hε₀, hS8wire⟩ := s8_of_smallVolSeed_C11KW.{u} Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
    (C2P6_C11GT6.{u} X2 Γ) P
  have hεR : 0 < min εProf_C11E.{u} (min (εK_threshold_C11GT2 εκ εsp εP6 εfull Γ) ε₀) :=
    lt_min εProf_pos_C11E (lt_min (εK_threshold_pos_C11GT2 hεκ hεsp hεP6 hεfull Γ) hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccT : pB.modelAccuracy ≤ εK_threshold_C11GT2 εκ εsp εP6 εfull Γ :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨haccκ, haccsp, haccP6, haccfull⟩ := εK_threshold_le_C11GT2 εκ εsp εP6 εfull Γ haccT
  have hacc₀ : pB.modelAccuracy ≤ ε₀ := hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP3 : CollarWindowSupply_C11E.{u} pB := ⟨hcollar, hradB⟩
  have hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u} := by
    refine ⟨haccProf, hordB, ?_⟩
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E at hradB
    linarith
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := exists_inv_base_C11W Cdist 1 (capWindowRadius_C11E + 1) _
    one_pos prepared hbase hdist hres
  have hΛ : 0 < pB.recenterConstant := lt_of_lt_of_le (by norm_num) pB.recenterConstant_ge_four
  obtain ⟨T, hQ⟩ := exists_budget_tower_C11GT2 hΛ Γ.Ctime (1 / 8646) (by norm_num) hstep X₀ hX₀
    hhist hrad₀
  obtain ⟨a₀, hctrl⟩ := exists_initialControl_C11GT P g
  have hS : ∀ n, (T.toChain.state n).DistanceData Cdist := fun n => (T.inv n).distance
  obtain ⟨W⟩ : Nonempty (∀ m, PreparedSpatialStepRetention (T.toChain.state m)
      (T.toChain.state (m + 1)) (T.toChain.accuracy m) (1 / ((m : ℝ) + 2))
      (T.request m).epsCut (T.request m).Dcut (T.request m).mcut) :=
    ⟨fun m => Classical.choice (T.extension m).retention⟩
  have hshift : ∀ m, (T.toChain.state (m + 1)).shift =
      (T.toChain.state m).history.time (Fin.last (T.toChain.state m).history.eventCount) :=
    fun m => (T.extension m).shift_eq
  have hoffset : ∀ m, (T.toChain.state (m + 1)).offset = (T.toChain.state m).history.eventCount :=
    fun m => (T.extension m).offset_eq
  obtain ⟨F, q, κ, records, hOld, hRaw⟩ := T.toChain.exists_surgery_with_retained_raw_caps hS
    (fun m => (T.request m).epsCut) (fun m => (T.request m).Dcut) (fun m => (T.request m).mcut)
    W hshift hoffset (fun n => T.toChain_accuracy_le_quarter n) a₀ hctrl
  obtain ⟨⟨hTower, -, ⟨hfixed, hradq, hordq, haccq, hrc⟩, hκ, hκanti, hδanti, hρanti, hpref,
    hrecHEq, hcan, hwin, hnc, -, hδlim, hrecent⟩, hdiag, -, -, hmi, -⟩ := hOld
  have hconst := canonicalConstantsSupply_mono_C11RD
    (canonicalConstantsSupply_of_closedBirthConstants_C11A Γ) (oldC1_le_C1P6_C11GT6.{u} X1 Γ)
    (oldC2_le_C2P6_C11GT6.{u} X2 Γ)
  have hdelta : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t :=
    fun t ht => (hdiag t ht).1
  have hlinkS : LinkedWindowsSupply_C11E records :=
    (hlinkfine_of_chain_C11GT3 T.toChain).hlinkS10 F q records hTower
      ⟨hfixed, hradq, hordq, haccq, hrc⟩ (fun n i j hij => hrecHEq n i j hij)
  have hguard : ∀ (m : ℕ) (i : Fin (T.toChain.state (m + 1)).native.eventCount) (A : ℝ), 0 < A →
      q.delta ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) <
        diagonalAccuracy_C11S q.delta A
          ((T.toChain.state (m + 1)).native.time i.succ + (T.toChain.state (m + 1)).shift) →
      A < 12 * (3 : ℝ) ^ m := by
    intro m i A hA hlt
    obtain ⟨-, -, -, -, hAg, -⟩ := hmi m i
    exact lt_of_accuracyGuard_C11Q6 T.toChain q (fun t ht => (hdiag t ht).1) hA hAg hlt
  have hwide : LocalKappaWideScaledSupply_C11Q4b F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    hKp Cdist _ T (fun j => (hQ j).1) F q hTower hdiag hguard haccκ hradB hordB
  have hTD := timeDerivativeSupply_of_astra_C12X T.toChain _ _ _ W hshift hoffset F hTower q
    hρanti (diagonal_neckRadius_of_prefix_C12X T.toChain q (fun n t ht => (hpref n t ht).2.1))
  have hcof : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      D ≤ (W k).fineParameters.modelRadius ∧ (W k).fineParameters.modelAccuracy ≤ ζ ∧
        m ≤ (W k).fineParameters.modelOrder := by
    intro D ζ m hζ
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1
      (tower_fine_request_eventually_C11W4 T (fun j => (hQ j).2.1) hζ D m)
    refine ⟨k₀, fun k hk => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hk₀ k hk (W k)
    exact ⟨h2, h1, h3⟩
  have hlate := lateLinkedRecordsSupply_of_outer_C12X T.toChain W F q records hfixed hrc hmi hRaw
    hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hSCRS : SameConstructionRetentionSupply_C11GT6 T :=
    ⟨F, q, κ, records, ⟨hTower, hdiag, hfixed, hradq, hordq, haccq, hrc⟩, ⟨hκ, hκanti, hnc⟩,
      hwide, ⟨hδanti, hρanti, hδlim⟩, ⟨hwin, hrecent, hlinkS, hlate⟩, hcan, hTD⟩
  have hP6 : LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
      (C2P6_C11GT6.{u} X2 Γ) :=
    largerBallCanonicalLateSupply_of_core_C11GT2
      (hP6p Cdist _ T (fun j => (hQ j).1) hSCRS F q hTower hdiag haccP6 hradB hordB)
  have hcanP6 := historyCanonicalSupply_mono_C12X hcan (oldC1_le_C1P6_C11GT6.{u} X1 Γ)
    (oldC2_le_C2P6_C11GT6.{u} X2 Γ)
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    hS8wire hP3 hprof hfixed hradq hordq haccq hacc₀ records hlinkS hδanti hρanti hcanP6 hwide hP6
      (fun A hA hw hb => hspinep T.toChain F q hTower hdiag haccsp hradB hordB A hA hw hb)
  have hStrong := strongCanonicalSupplyV2_mono_C12X (strongCanonicalSupplyV2_of_towerFull_C12X
    (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)) (C1ceil_le_C1P6_C11GT6.{u} X1 Γ)
    (C2ceil_le_C2P6_C11GT6.{u} X2 Γ)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_C12X hP3 hprof ⟨T.toChain, F, q, κ, records, Γ.epsilon,
    C1P6_C11GT6.{u} X1 Γ, C2P6_C11GT6.{u} X2 Γ, hTower, rfl,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ, hκanti, hδanti, hρanti, hcanP6, hnc, hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17, frontierCollarSupplyFull_C12X F q⟩

/-! ## 3. v6 顶层（标准 closed-term ceiling） -/

/-- **A12′ v6 顶层缺口定理**：binder 只有 `hspine′ hP6b′`（2 个；v5 `noK` 是 3 个 `hspine hP6b hfull`）。
`hP6b′` = R-C11-8 D-4 schema（budget tower + SCRS + `∀ F q` 实现该构造 + ModelSmallness ⇒
`CanonicalLateCore` 在标准 ceiling `C1P6 / C2P6`）；`hspine′` = v5 种子限制 window 形，`hb` 在同一 ceiling。 -/
theorem a12EnhancedFull_of_gaps_v6_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupply_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v6_gen_C11GT6 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} hspine hP6b

/-! ## 4. 与 v3 / v5 binder 的方向（记录） -/

/-- **`hP6b′` 比 v3 / v5 的 `hP6b` 弱**：旧 `hP6b`（任意 chain、旧 ceiling）⇒ `hP6b′`（budget tower + SCRS，
ceiling `C1P6`）——`T.toChain` 实例化 + 常数上调。所以 v6 只减少 P6 义务。 -/
theorem hP6bV6_of_v3_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)))) :
    ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants} (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupply_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ) := by
  obtain ⟨εP6, hεP6, hp⟩ := hP6b
  exact ⟨εP6, hεP6, fun _ _ T _ _ F q hT hd ha hr ho =>
    canonicalLateCore_mono_C11GT6 (hp T.toChain F q hT hd ha hr ho) (oldC1_le_C1P6_C11GT6 X1 _)
      (oldC2_le_C2P6_C11GT6 X2 _)⟩

/-- **`hspine′` 比 v5 的 `hspine` 强**：`hspine′`（`hb` 在 `C1P6`）⇒ v5 `hspine`（`hb` 在旧 ceiling），经
`largerBallCanonicalLateSupply_mono_C12X`；反向需要把大常数 witness 缩小，不成立（D-4）。 -/
theorem hspineV5_of_v6_C11GT6 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
          (C2P6_C11GT6.{u} X2 Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A) :
    ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (max Γ.C1s Γ.Cbirth)
          (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ))) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A := by
  obtain ⟨εsp, hεsp, hp⟩ := hspine
  exact ⟨εsp, hεsp, fun S F q hT hd ha hr ho A hA hw hb => hp S F q hT hd ha hr ho A hA hw
    (largerBallCanonicalLateSupply_mono_C12X hb (oldC1_le_C1P6_C11GT6 X1 _)
      (oldC2_le_C2P6_C11GT6 X2 _))⟩

/-! ## 5. consumers -/

/-- consumer：v6 的结论（A12′）⇒ 晚期共同 neck accuracy 与 A12 的 `hasCommonNeckAccuracy`
（与 v1–v5 同一结论类型，下游不变）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} (h : A12EnhancedFullConclusion_C11F P g) :
    ∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧ hasCommonNeckAccuracy F δ := by
  obtain ⟨δ, F, -, hdec, ⟨E⟩⟩ := h
  exact ⟨δ, F, hdec, E.toAnalyticSurgeryProfile.commonNeckAccuracy⟩

/-- consumer：v6 的签名稳定（binder 列表即 `type_of%`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    type_of% (a12EnhancedFull_of_gaps_v6_C11GT6 P g) := a12EnhancedFull_of_gaps_v6_C11GT6 P g

/-- consumer：旧 `hP6b`（v3 / v5 逐字）+ `hspine′` ⇒ A12′（经 `hP6bV6_of_v3_C11GT6`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          (∀ w : ℝ, (t : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (t : ℝ) → q.neckRadius w ≤ r) →
          ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
            (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
          ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
            (H.activeStage_mono haT) p,
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
            (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
          ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
            (A * r),
          ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' < r / 100 → H.isParabolicallyRmControlledBall v x ρ' →
            ENNReal.ofReal (κ'' * ρ' ^ 3) ≤
              ballVolume (H.stageMetric (H.activeStage v) v) x ρ') →
        LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) →
        LargerBallScalarAt_C11S F q.delta (diagonalAccuracy_C11S q.delta) A)
    (hP6b : ∃ εP6 : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εP6 Γ) ∧
      ∀ {pB : CutoffParameters} {Γ : ClosedBirthConstants}
      (S : PreparedSpatialChain pB Γ P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (max Γ.C1s Γ.Cbirth)
        (max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)))) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v6_C11GT6 P g hspine
    (hP6bV6_of_v3_C11GT6 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} hP6b)

end GC.LongTime.Ch11
