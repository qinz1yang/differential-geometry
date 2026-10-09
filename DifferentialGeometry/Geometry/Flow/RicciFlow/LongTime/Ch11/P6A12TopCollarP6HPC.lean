import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyCollarP6HPC

/-!
# A12′ 顶层 collar 版（O-CH11-HP6B-COLLAR G2，后缀 `_P6HPC`；R-C11-19 D-19-1 顶层 consumer 同步切换）

* **G2 `a12EnhancedFull_of_gaps_v7two_collar_P6HPC`**：GAPTOP7B 冻结形
    `a12EnhancedFull_of_gaps_v7two_C11G7B` 的孪生，
  `hP6b` binder 只在 env 末尾加一行 `collarAdmitsAllOrders_C11E pB.fixed.collarLength pB.fixed.collar_pos
      →`
  （= collar 合同 `HP6bTwoLevelTimeCollar_C11G7B2` 正文，生成器 H6 断言）；`hspine` binder 不变；结论 =
  `A12EnhancedFullConclusion_C11F P g`（A12′ 逐字）。
* 证明 = HP6B2 collar 引擎 `a12EnhancedFull_of_gaps_v7twoCollar_gen_C11G7B2`（tracked）：它是 GAPTOP7B gen 引擎
  `a12EnhancedFull_of_gaps_v7two_gen_C11G7B` 的**原证明模式**孪生，恰三处改动（改名 / hP6b binder 加 collar 行 /
  `hP6p … haccP6 hradB hordB` 调用多传 `hcollar`），生成器 H7 断言。collar 前提的付款点：GAPTOP7B 引擎
  `obtain ⟨pB, prepared, hbase, hdist, hres, hcollar, hstep⟩ := hmake _ hεR`（`hmake` 来自
  `hpbaseTwoLevel_C11G2 P g`），同一 `pB` 上的 `T : BlockTower_C11W pB …` 喂 `hP6p` ⇒ collar 由 `hmake` 付。
* **G2′ `a12EnhancedFull_of_v7two_collar_contracts_P6HPC`**：合同形 `(hs : HSpineTwoLevelTime_C11G7B)
  (hp : HP6bTwoLevelTimeCollar_C11G7B2)`。
* 不改 GAPTOP7B 文件；不把 collar 合同喂回旧 `HP6bTwoLevelTime_C11G7B`（审计传递闭包 deny 0 hit）。
块标 **PROVED**（条件形：binder = `hspine‴` + collar 版 `hP6b‴`，与 GAPTOP7B 冻结形同构）。
生成：`build-logs/scratch/O-CH11-HP6B-COLLAR/gen/gen.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped NNReal Topology ContDiff Manifold ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G2 `a12EnhancedFull_of_gaps_v7two_collar_P6HPC`（A12′ 顶层，collar 版冻结形）**：binder 只有 `hspine‴`
与 collar 版 `hP6b‴`；collar 前提由引擎内 pBase provider `hmake` 付。 -/
theorem a12EnhancedFull_of_gaps_v7two_collar_P6HPC (P : OrientedThreeStage.{u}) (g : P.Metric)
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
        CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
          (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ) →
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
      collarAdmitsAllOrders_C11E.{u} pB.fixed.collarLength pB.fixed.collar_pos →
      CanonicalLateTimeCore_P6X F Γ.epsilon (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ)
        (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) (p6Ctime_C11G7B.{u} Γ)) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v7twoCollar_gen_C11G7B2 P g p6X1std_C11GT6.{u} p6X2std_C11GT6.{u}
    p6Ctime_C11G7B.{u} hspine hP6b

/-- **G2′ 合同形**：`hspine‴ : HSpineTwoLevelTime_C11G7B`（不变）+
`hP6b‴ : HP6bTwoLevelTimeCollar_C11G7B2`（collar 合同）。 -/
theorem a12EnhancedFull_of_v7two_collar_contracts_P6HPC (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hs : HSpineTwoLevelTime_C11G7B.{u} P g) (hp : HP6bTwoLevelTimeCollar_C11G7B2.{u} P g) :
    A12EnhancedFullConclusion_C11F P g :=
  a12EnhancedFull_of_gaps_v7two_collar_P6HPC P g hs hp

/-- consumer（D-19-1 同步切换）：G1 collar 版装配的输出直接喂 G2′ collar 版顶层。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) (hs : HSpineTwoLevelTime_C11G7B.{u} P g) :
    True := by
  have _h := fun εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8 hgapJF hgapJF8 hmargin hrecords
      hpinch hderivL hgradL hdistLA hscaleSep =>
    a12EnhancedFull_of_v7two_collar_contracts_P6HPC P g hs
      (ObservedHistory.hP6bTwoLevelTimeCollar_of_slots_P6HPC P g εP6 hεP6 Csel T₀sel Qtsel hmono
          Cgsel hgapJ hgapJ8 hgapJF hgapJF8 hmargin hrecords hpinch hderivL hgradL hdistLA
          hscaleSep)
  trivial

end GC.LongTime.Ch11
