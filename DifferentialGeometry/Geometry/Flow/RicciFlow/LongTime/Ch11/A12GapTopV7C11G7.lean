import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2

set_option autoImplicit false

/-!
# A12′ 顶层 v7（GAMMA2 方案 A：两级精度）——O-CH11-GAPTOP7 G2，后缀 `_C11G7`

设计 `docs/geometrization/chapter8/design-C11-gamma2-20261007.md` §3.3 / §6.2（L1–L4）。tower 在更细的
`Γf`（`FineOf_C11G2 Γf Γ`）上构造，结论元组在粗 `Γ`（`Γ.epsilon`、`C1P6 / C2P6 Γ`）：
* **L1** `noncollapsedBefore_coarsen_C11G7`：`NoncollapsedBefore κ ρ` ⇒
  `NoncollapsedBefore (κ · (ρ/ρ')³) ρ'`
  （`ρ ≤ ρ'`；`mono_radius` + 球体积对半径单调）——astra 的 `hnc` 在 `Γf.epsilon` 尺度，元组要 `Γ.epsilon`；
* **L2** `strongCanonicalSupplyV2_monoEps_C11G7`：S16（hStrong v2）对精度单调（`W.monoEps`、
  `capTubeHasNeckChart.mono_eps`、neck 分支反演 + `StrongNeck.mono`）；
* **L3** 不另起 def：四个 producer 阈值的合成直接复用 `εK_threshold_C11GT2`（常值函数
  `εκ Γf`、`εsp Γ Γf`、`εP6 Γ Γf`、`εfull Γf`）；
* **L4** 引擎 `a12EnhancedFull_of_gaps_v7_gen_C11G7`（ceiling 泛型 `X1 X2`，**两参数**阈值 `εsp Γ Γf` /
  `εP6 Γ Γf`）：`hpbaseTwoLevel_C11G2`（CX-OUTER2 插入点）给 `(Γ, Γf)`；reserve 含 `epsilon0_C11FR` 在 `Γf`
  （S8 wire 实际喂入的精度）；tower / SCRS⁺ / hKseed / hfull / S8 在 `Γf`；`hP6` 由 `hP6b‴` 在粗 `Γ`；
  `hcan`、`hStrong`、`hnc` 经 monoEps / 常数单调 / L1 粗化到 `Γ`；最终装配
  `a12EnhancedFull_of_chain_cone_C11G2`（`ε ≤ coneAccuracy` 形）。
* **冻结顶层** `a12EnhancedFull_of_gaps_v7_C11G7`（lead 裁定 5 行最小版）：相对 v6fwd 顶层
  （`A12GapTopV6FwdC11GT6.lean` L539–581）逐行只改 541 / 542 / 570（拆 2 行，含 CX-OUTER2 G2′ 两条 Γ-accuracy
  门槛）/ 571 / 572，结论逐字；`εsp Γ` / `εP6 Γ` 只依赖粗 `Γ`。它与 GAMMA2 登记的 9 行形
  `GapTop7Statement_C11G2` 都是 L4 的推论（`gapTop7Statement_C11G7`）。
* 方向记录：`FineOf_C11G2` 反自反（`fineOf_irrefl_C11G7`）。`hspine‴ ⇐ hspine″`、`hP6b‴ ⇐ hP6b′` **无合法适配**
  （原因见 `state-O-CH11-GAPTOP7.md`：hspine″ 在 `Γf` 处要 `hP6` 在细 `Γf.epsilon`、常数 `C1P6 Γf`，而 hspine‴
  只给粗 `Γ.epsilon`——HCS 类供给只能细 ⇒ 粗；hP6b′ 在 `Γf` 处给的常数 `C1P6 X1 Γf ∋ p6CoarseC Γf.epsilon`
  与 `C1P6 X1 Γ` 无序关系，`p6CoarseC` 对精度不单调）。
不声称 `hspine‴` / `hP6b‴` 已闭合（仍 OPEN binder）。
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

/-! ## 1. L1：noncollapsed 尺度上界的粗化 -/

/-- **L1**：`NoncollapsedBefore κ ρ t₀`（尺度 `r ≤ ρ`）⇒ `NoncollapsedBefore (κ · (ρ/ρ')³) ρ' t₀`
（`ρ ≤ ρ'`）。`r ≤ ρ'` 的受控球缩到半径 `min r ρ`（`mono_radius`），体积对半径单调，`(ρ/ρ') r ≤ min r ρ`。 -/
theorem noncollapsedBefore_coarsen_C11G7 (H : RetainedCoreHistory.{u}) {κ ρ ρ' t₀ : ℝ}
    (hκ : 0 ≤ κ) (hρ : 0 < ρ) (hρρ' : ρ ≤ ρ') (h : H.NoncollapsedBefore κ ρ t₀) :
    H.NoncollapsedBefore (κ * (ρ / ρ') ^ 3) ρ' t₀ := by
  intro t p r ht hr hball
  have hr0 : 0 < r := hball.1
  have hρ'0 : 0 < ρ' := hρ.trans_le hρρ'
  have hr₀ : 0 < min r ρ := lt_min hr0 hρ
  have hb₀ := ObservedHistory.isParabolicallyRmControlledBall.mono_radius _ hball hr₀
    (min_le_left r ρ)
  have hv := h t p (min r ρ) ht (min_le_right r ρ) hb₀
  have hsub := riemannianBallOf_mono (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p
    (min_le_left r ρ)
  have hq0 : 0 ≤ ρ / ρ' := (div_pos hρ hρ'0).le
  have hq1 : ρ / ρ' * r ≤ r := by
    have h1 : ρ / ρ' ≤ 1 := (div_le_one hρ'0).2 hρρ'
    nlinarith
  have hq2 : ρ / ρ' * r ≤ ρ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hρ'0]
    nlinarith
  have hpow : (ρ / ρ' * r) ^ 3 ≤ (min r ρ) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hq0 hr0.le) (le_min hq1 hq2) 3
  have hreal : κ * (ρ / ρ') ^ 3 * r ^ 3 ≤ κ * (min r ρ) ^ 3 := by
    have heq : κ * (ρ / ρ') ^ 3 * r ^ 3 = κ * (ρ / ρ' * r) ^ 3 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpow hκ
  calc ENNReal.ofReal (κ * (ρ / ρ') ^ 3) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal (κ * (ρ / ρ') ^ 3 * r ^ 3) := by
        rw [← ENNReal.ofReal_pow hr0.le,
          ← ENNReal.ofReal_mul (mul_nonneg hκ (pow_nonneg hq0 3))]
    _ ≤ ENNReal.ofReal (κ * (min r ρ) ^ 3) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal κ * ENNReal.ofReal (min r ρ) ^ 3 := by
        rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hr₀.le]
    _ ≤ _ := hv
    _ ≤ _ := measure_mono hsub

/-! ## 2. L2：S16（hStrong v2）对精度单调 -/

/-- **L2**：`StrongCanonicalSupplyV2_C11E F ρ ε C1 C2` ⇒ 同形在 `ε' ∈ [ε, 1/11)`（同阈值、同常数）。
witness 用 `monoEps`；neck 分支：`(W.monoEps).alternative = neck nk'` 反演出 `W.alternative = neck data`，
原 strong neck 经 `StrongNeck.mono` 放宽到 `ε'`。 -/
theorem strongCanonicalSupplyV2_monoEps_C11G7 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε ε' C1 C2 : ℝ}
    (h : StrongCanonicalSupplyV2_C11E F ρ ε C1 C2) (hε : ε ≤ ε') (hsmall : ε' < 1 / 11) :
    StrongCanonicalSupplyV2_C11E F ρ ε' C1 C2 := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hWc, hWn⟩ := hT s hs x hR
  refine ⟨W.monoEps hε hsmall, hWc.mono_eps hε hsmall hε hsmall, fun nk heq => ?_⟩
  change W.alternative.monoEps W.eps_pos hε hsmall = SpatialCanonicalAlternative.neck nk at heq
  cases halt : W.alternative with
  | neck data =>
    obtain ⟨U, hxU, a, E, S, h1, h2, h3, h4, ⟨nkS⟩⟩ := hWn data halt
    exact ⟨U, hxU, a, E, S, h1, h2, h3, h4, ⟨nkS.mono hε hsmall⟩⟩
  | cap data deep =>
    rw [halt] at heq
    cases heq
  | positive whole data sec =>
    rw [halt] at heq
    cases heq
  | round whole data =>
    rw [halt] at heq
    cases heq

/-! ## 3. 方向记录 -/

/-- `FineOf_C11G2` 反自反（`Γ.epsilon ≤ p6FineEta Γ.epsilon ≤ Γ.epsilon / 2` 与 `0 < Γ.epsilon` 矛盾）：
v6fwd 的单级 binder 不是 v7 两级 binder 的对角特例——不存在"取 `Γf = Γ`"的平凡适配。 -/
theorem fineOf_irrefl_C11G7 (Γ : ClosedBirthConstants) : ¬ FineOf_C11G2.{u} Γ Γ := by
  intro h
  have h1 := p6FineEta_le_C11GT6 Γ.epsilon
  have h2 := Γ.epsilon_pos
  linarith [h.1]

/-! ## 4. L4：v7 引擎（ceiling 泛型，两参数阈值） -/

/-- **A12′ v7 引擎（GAMMA2 方案 A，ceiling 泛型 `X1 X2`，两参数阈值）**：binder `hspine‴ hP6b‴`（链 / tower 在
`Γf`，`FineOf Γf Γ`；`hP6` 与 `hP6b‴` 结论在粗 `Γ`）；`hKseed`、`hfull`、SCRS⁺、同 tower 前向 wide、
`hpbaseTwoLevel` 在证明体内供给。 -/
theorem a12EnhancedFull_of_gaps_v7_gen_C11G7 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (X1 X2 : ClosedBirthConstants → ℝ)
    (hspine : ∃ εsp : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εsp Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = S.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
      pB.modelAccuracy ≤ εsp Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ A : ℝ, 1 < A →
      (∃ κ'' : ℝ, 0 < κ'' ∧ ∃ T : ℝ, 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          q.neckRadius t ≤ r →
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
    (hP6b : ∃ εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ,
      (∀ Γ Γf, 0 < εP6 Γ Γf) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨Cdist, Γ, Γf, hfine, hΓs, hΓW, -, -, hmake⟩ := hpbaseTwoLevel_C11G2.{u} P g
  obtain ⟨εκ, hεκ, hKp⟩ := hKseed_of_producers_C11KW P g
  obtain ⟨εsp, hεsp, hspinep⟩ := hspine
  obtain ⟨εP6, hεP6, hP6p⟩ := hP6b
  obtain ⟨εfull, hεfull, hfullp⟩ := hfull_ceiling_C11SC P g
  have hε₀ := epsilon0_pos_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
    (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P
  have hεT : 0 < εK_threshold_C11GT2 (fun _ => εκ Γf) (fun _ => εsp Γ Γf) (fun _ => εP6 Γ Γf)
      (fun _ => εfull Γf) Γ :=
    εK_threshold_pos_C11GT2 (fun _ => hεκ Γf) (fun _ => hεsp Γ Γf) (fun _ => hεP6 Γ Γf)
      (fun _ => hεfull Γf) Γ
  have hεR : 0 < min εProf_C11E.{u} (min (εK_threshold_C11GT2 (fun _ => εκ Γf)
      (fun _ => εsp Γ Γf) (fun _ => εP6 Γ Γf) (fun _ => εfull Γf) Γ)
      (epsilon0_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
        (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P)) :=
    lt_min εProf_pos_C11E (lt_min hεT hε₀)
  obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR
  obtain ⟨hacc, hradB, hordB⟩ := pBase_bounds_of_reserve_C11W6 hbase hres
  have haccProf : pB.modelAccuracy ≤ εProf_C11E.{u} := hacc.trans (min_le_left _ _)
  have haccT : pB.modelAccuracy ≤ εK_threshold_C11GT2 (fun _ => εκ Γf) (fun _ => εsp Γ Γf)
      (fun _ => εP6 Γ Γf) (fun _ => εfull Γf) Γ :=
    hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨haccκ, haccsp, haccP6, haccfull⟩ := εK_threshold_le_C11GT2 _ _ _ _ Γ haccT
  have hacc₀ : pB.modelAccuracy ≤ epsilon0_C11FR.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
      (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P :=
    hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP3 : CollarWindowSupply_C11E.{u} pB := ⟨hcollar, hradB⟩
  have hprof : ModelConstraintsSupply_C11E pB εProf_C11E.{u} := by
    refine ⟨haccProf, hordB, ?_⟩
    have hte := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E at hradB
    linarith
  obtain ⟨X₀, hX₀, hhist, hrad₀⟩ := exists_inv_base_C11W Cdist 1 (capWindowRadius_C11E + 1) _
    one_pos prepared hbase hdist hres
  have hΛ : 0 < pB.recenterConstant := lt_of_lt_of_le (by norm_num) pB.recenterConstant_ge_four
  obtain ⟨T, hQ⟩ := exists_budget_tower_C11GT2 hΛ Γf.Ctime (1 / 8646) (by norm_num) hstep X₀ hX₀
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
  have hwideF : LocalKappaWideFwdSupply_C11FR F q.delta (diagonalAccuracy_C11S q.delta)
      q.neckRadius :=
    localKappaWideFwd_of_certifiedTower_C11GT6 T (fun j => (hQ j).1) F q hTower hdiag
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
  have hnom := lateLinkedRecordsSupplyNom_of_outer_P6NI T.toChain W F q records hfixed hrc hmi
    hRaw hcof ((hlinkfine_of_chain_C11GT3 T.toChain).hfine_S14 W)
  have hSCRS : SameConstructionRetentionSupplyPlus_C11GT6 T :=
    ⟨F, q, κ, records, ⟨hTower, hdiag, hfixed, hradq, hordq, haccq, hrc⟩, ⟨hκ, hκanti, hnc⟩,
      hwide, ⟨hδanti, hρanti, hδlim⟩, ⟨hwin, hrecent, hlinkS, hlate⟩, hcan, hTD, hwideF,
      fun n => eventSlabsDerivative_qcanSup_P6WR T.toChain _ _ _ W hshift hoffset F hTower n,
      hnom⟩
  -- 两级：`hP6` 由 `hP6b‴` 在粗 `Γ`；tower 一侧的供给经 `FineOf` 粗化到 `Γ`
  have hP6 : LargerBallCanonicalLateSupply_C11E F Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
      (C2P6_C11GT6.{u} X2 Γ) :=
    largerBallCanonicalLateSupply_of_core_C11GT2
      (hP6p hfine hΓs hΓW Cdist _ T (fun j => (hQ j).1) hSCRS F q hTower hdiag haccP6 hradB
        hordB)
  have hΓ11 : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  have hC1 : C1ceil_C11SC.{u} Γf ≤ C1P6_C11GT6.{u} X1 Γ :=
    hfine.2.1.trans (C1ceil_le_C1P6_C11GT6.{u} X1 Γ)
  have hC2 : C2ceil_C11SC.{u} Γf ≤ C2P6_C11GT6.{u} X2 Γ :=
    hfine.2.2.1.trans (C2ceil_le_C2P6_C11GT6.{u} X2 Γ)
  have hcanP6 := historyCanonicalSupply_mono_all_C11G2 hcan hfine.epsilon_le hΓ11
    ((oldC1_le_C1ceil_C11SC.{u} Γf).trans hC1) ((oldC2_le_C2ceil_C11SC.{u} Γf).trans hC2)
  have hS8 : LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) :=
    s8_of_smallVolFwd_C11GT6.{u} Γf.epsilon (max Γf.C1s Γf.Cbirth)
      (max Γf.C2s (max Γf.Cbirth (Γf.Cgrad : ℝ))) P hP3 hprof hfixed hradq hordq haccq hacc₀
      records hlinkS hδanti hρanti hcan hwide hwideF
      (fun A hA hw => hspinep hfine T.toChain F q hTower hdiag haccsp hradB hordB A hA hw hP6)
  have hStrong := strongCanonicalSupplyV2_mono_C12X (strongCanonicalSupplyV2_monoEps_C11G7
    (strongCanonicalSupplyV2_of_towerFull_C12X
      (hfullp T.toChain F q hTower hdiag haccfull hradB hordB)) hfine.epsilon_le hΓ11) hC1 hC2
  have hc3 : 0 < (Γf.epsilon / Γ.epsilon) ^ 3 :=
    pow_pos (div_pos Γf.epsilon_pos Γ.epsilon_pos) 3
  have hκ' : ∀ t : ℝ, 0 < κ t * (Γf.epsilon / Γ.epsilon) ^ 3 := fun t => mul_pos (hκ t) hc3
  have hκ'anti : Antitone fun t => κ t * (Γf.epsilon / Γ.epsilon) ^ 3 :=
    fun a b hab => mul_le_mul_of_nonneg_right (hκanti hab) hc3.le
  have hnc' : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
      (F.tower.history n).NoncollapsedBefore (κ t * (Γf.epsilon / Γ.epsilon) ^ 3) Γ.epsilon t :=
    fun n t ht => noncollapsedBefore_coarsen_C11G7 _ (hκ t).le Γf.epsilon_pos hfine.epsilon_le
      (hnc n t ht)
  have hacc17 : ∀ n, T.toChain.accuracy n ≤ 1 / 8646 :=
    fun n => ((T.extension n).accuracy_le_cap).trans (hQ n).2.2
  have hS17 := compatibleCapsSupply_of_eventDelta_C12X records
    (eventDelta_of_accuracy_C12X T.toChain (1 / 8646) hacc17 F q hdelta)
  exact a12EnhancedFull_of_chain_cone_C11G2 hP3 hprof ⟨T.toChain, F, q,
    fun t => κ t * (Γf.epsilon / Γ.epsilon) ^ 3, records, Γ.epsilon,
    C1P6_C11GT6.{u} X1 Γ, C2P6_C11GT6.{u} X2 Γ, hTower, Γ.epsilon_cone,
    ⟨hfixed, hradq, hordq, haccq⟩, hconst, hκ', hκ'anti, hδanti, hρanti, hcanP6, hnc', hδlim,
    hrecent, hS8, hlinkS, hTD, hlate, hP6, hStrong, hS17, frontierCollarSupplyFull_C12X F q⟩

/-! ## 5. 冻结顶层 v7（5 行最小版）与推论 -/

/-- **A12′ v7 顶层缺口定理（冻结形，lead 裁定 5 行最小版，标准 ceiling）**：binder 只有 `hspine‴ hP6b‴`。
相对 v6fwd `a12EnhancedFull_of_gaps_v6fwd_C11GT6` 只改：`∀ {pB} {Γ Γf}, FineOf_C11G2 Γf Γ →`（两处）、
链 / tower 在 `Γf`、`BudgetCertificate … Γf.Ctime …`、`hP6b‴` 带 CX-OUTER2 G2′ 的两条 Γ-accuracy 门槛；
结论、hw guard、
`hP6`（粗 `Γ.epsilon`、`C1P6 / C2P6 std Γ`）、SCRS⁺、阈值 `εsp Γ` / `εP6 Γ` 逐字。证明 = 两参数引擎取常值阈值。 -/
theorem a12EnhancedFull_of_gaps_v7_C11G7 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hspine : ∃ εsp : ClosedBirthConstants → ℝ, (∀ Γ, 0 < εsp Γ) ∧
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ → ∀
      (S : PreparedSpatialChain pB Γf P g) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
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
          q.neckRadius t ≤ r →
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
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} → ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j (T.block j) (T.lookahead j)
        (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      CanonicalLateCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨εsp, hεsp, hs⟩ := hspine
  obtain ⟨εP6, hεP6, hp⟩ := hP6b
  exact a12EnhancedFull_of_gaps_v7_gen_C11G7 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u}
    ⟨fun Γ _ => εsp Γ, fun Γ _ => hεsp Γ, hs⟩ ⟨fun Γ _ => εP6 Γ, fun Γ _ => hεP6 Γ, hp⟩

/-- **GAMMA2 登记的 9 行形** `GapTop7Statement_C11G2`（两参数阈值，标准 ceiling）是 v7 引擎的实例
（GAMMA2 G1 "只登记，未证" 的项在此证出；binder `hspine‴ hP6b‴` 仍 OPEN）。 -/
theorem gapTop7Statement_C11G7 (P : OrientedThreeStage.{u}) (g : P.Metric) :
    GapTop7Statement_C11G2.{u} P g := fun hs hp =>
  a12EnhancedFull_of_gaps_v7_gen_C11G7 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} hs hp

/-! ## 6. consumers -/

/-- consumer (i)：GAMMA2 consumer (ii) 的 `htop` 前提由 `gapTop7Statement_C11G7` 付清——9 行 binder +
闭合两级 provider ⇒ A12′ 增强结论 与 `(Γ, Γf)` 的两级关系。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (hs : HSpineTwoLevel_C11G2.{u} P g)
    (hp : HP6bTwoLevel_C11G2.{u} P g) :
    (∃ Γ Γf : ClosedBirthConstants, FineOf_C11G2.{u} Γf Γ ∧ Γ.epsilon ≤ εStrong_C12X.{u} ∧
      Γ.epsilon ≤ epsW_CXOU2.{u} ∧ ¬ FineOf_C11G2.{u} Γ Γ) ∧
      A12EnhancedFullConclusion_C11F P g := by
  obtain ⟨-, Γ, Γf, hfine, hs1, hW, -⟩ := hpbaseTwoLevel_C11G2.{u} P g
  exact ⟨⟨Γ, Γf, hfine, hs1, hW, fineOf_irrefl_C11G7 Γ⟩, gapTop7Statement_C11G7 P g hs hp⟩

/-- consumer (ii)：L1 + L2 联用——细 `Γf` 处的 noncollapsing 与 S16 供给搬到粗 `Γ`（v7 引擎的两处粗化，
单独可用）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ρ : ℝ → ℝ} {Γ Γf : ClosedBirthConstants} (hfine : FineOf_C11G2.{u} Γf Γ) {κ t : ℝ}
    (hκ : 0 < κ) (n : ℕ) (hnc : (F.tower.history n).NoncollapsedBefore κ Γf.epsilon t)
    (hS : StrongCanonicalSupplyV2_C11E F ρ Γf.epsilon (C1ceil_C11SC.{u} Γf)
      (C2ceil_C11SC.{u} Γf)) :
    (F.tower.history n).NoncollapsedBefore (κ * (Γf.epsilon / Γ.epsilon) ^ 3) Γ.epsilon t ∧
      StrongCanonicalSupplyV2_C11E F ρ Γ.epsilon (C1ceil_C11SC.{u} Γ) (C2ceil_C11SC.{u} Γ) := by
  have hΓ11 : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  exact ⟨noncollapsedBefore_coarsen_C11G7 _ hκ.le Γf.epsilon_pos hfine.epsilon_le hnc,
    strongCanonicalSupplyV2_mono_C12X (strongCanonicalSupplyV2_monoEps_C11G7 hS
      hfine.epsilon_le hΓ11) hfine.2.1 hfine.2.2.1⟩

end GC.LongTime.Ch11
