import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3DerivSlotP6F5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FootSecondP6F2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingDomC11CL2

/-!
# FOOT3 局域五项之 `hmargin` / `hrecords`（O-CH11-FOOT5 G3，后缀 `_P6F5`）

**G3a `hmargin_slot_P6F5`（PROVED，0 binder）**：结论 = HP6B2 v2 `hP6bTwoLevelTime_of_slots_v2_P6HPB2` 的
`hmargin` 槽**逐字**（gen 从 l.1078–1139 切出）。= FOOT2 闭合形 `hmargin_of_supplies_P6F2`（结论 = BCDT `hmargin`
逐字、无 footprint `D`、不经 `hcenE(D)`）在**实际反证族的 env** 上实例化（R-C11-19 Q1 的要求）：
`F = F₀`（`rawSurgery_eq_of_tower_eq_C11KW`）；SCRS⁺ 的 `q₀ / hq₀ / hδ₀ / hP5L₀`；
`outerSupply_twoLevel_C11G2 … F q₀ hF hq₀` @ `(C1P6 std, C2P6 std, C_t*)` 给 `hcan₁`（同 HCENE
`hcenE_bad_P6HC`）。
**常数比较逐式**（lead 01:0x 要求列出；全部已付）：
* `hε : 0 < Γ.ε` ← `Γ.epsilon_pos`；`hε' : Γ.ε < 1/11` ← `Γ.epsilon_small` + linarith；
* `hCs1 : capCollarCs_P6HE Γ.ε ≤ C1P6 std Γ` ← `capCollar_le_C1P6_C11CL3 Γ`；
* `hCs2 : capCollarCs_P6HE Γ.ε ≤ C2P6 std Γ` ← `capCollar_le_C2P6_C11CL3 Γ`；
* `η₁ := Γ.ε`、`C1₁ := C1P6 std Γ`、`C2₁ := C2P6 std Γ`（`hcan₁` 直接在标准元组）⇒ `hηε hC1 hC2` 都是 `le_rfl`；
* `outerSupply_twoLevel_C11G2`
的三条：`C1ceil_le_C1P6_C11GT6`、`C2ceil_le_C2P6_C11GT6`、`Ctime_le_p6Ctime_C11G7B`。
槽里的 `q`（tower 对角参数）不参与：`hmargin` 结论不含它（records 在 FOOT2 内部取自 `hP5L₀ @ q₀`）。

**G3b `hrecords_slot_of_nCWP_P6F5`（PROVISIONAL[`hnCWPslot`]）**：结论 = HP6B2 v2 `hrecords` 槽**逐字**
（l.1141–1208）。已付部分（PROVED）：records = SCRS⁺ 的 S14 `hP5L₀`（`D := Rrad`、`ζ := min ζ₀ ζ*`、`m :=
2`；`ζ*` 由 binder 给）逐 `n`
`choose` 后的 `rescale_P6M (c k)`（同 FOOT2 G3 `hrec6S_of_sep_P6F2`）；`pp := (p (ind k)).rescale_P6N
(c k)`；
canonical windows ⇐ `linkedCanonicalWindow_hasCanonicalWindow_C11E` +
`hasCanonicalWindow_rescale_P6M`；
`Rrad ≤ radius`、`2 ≤ order` 直接，`accuracy ≤ min ζ₀ ζ* ≤ ζ₀`；`T₀ := Tthr / c_k ≤ σ_k − B/R_k` ⇐
`c_k σ_k → ∞`
（前缀 `k+1 ≤ c_k Tn`、`aSeed = Tn − 1 ≥ 1`）+ `B/R_k ≤ 1/2`（`R_k ≥ k+1`）。
**唯一剩余 = late non-CWP**（R-C11-19 Q1："不能只用普通 record 投影替代"）= binder **`hnCWPslot`**：对 HP6b env
给一个精度门槛 `ζ* > 0`（env 依赖；records 取 `ζ := min ζ₀ ζ*`，故 binder 只需对**足够精确**的 records 成立，
(CWS) 的 cap 标量下界需要精度小），
任意满足 S14 形状的 linked late records `(p n, Tthr, records)`（`Rrad ≤ radius`、`accuracy ≤ ζ₀ ≤ ζ*`、`2 ≤
order`、
`δ / ρ` 在 `t ≥ 0` 与槽 `q` 一致、`recenterConstant = pB.recenterConstant`、linked canonical windows），在槽的同一
selected family 前缀下 `∀ᶠ k`、`∀ p′ q′`（crossing）、`∀ᶠ t ↑ σ_k`：`p′` 回溯到任一 late event `i′`
（`Tthr ≤ time i′⁺`、`i′⁺ ≤ (i k)⁻`）的 birth 时刻**不**落在 rescaled record 的 cap window `‖w‖ < Dcap + 1`、
年龄 `t − time i′⁺ ≤ ½ · scale⁻¹` 里。
**ANCHOR2 `notCWP_of_hnot_P6AN2` 不适用**（lead 要求写明）：它要 `hnot`（`P6AnchorSecondP6AN2.lean:197`：
`¬ ∃ j hT hl B b x, B.point j⁺ = window x ∧ ‖x‖ < Dsel + 1 ∧ t − time j⁺ ≤ θsel·scale⁻¹`，`H :
RetainedCoreHistory`、
`y ∈` 末 stage）；`hnot` 的来源是 P6CD / P6HF 选点合同的 `hnotK`（`P6ClosedConditionalP6CD.lean:69`，`Dsel = n+1`、
`θsel = 1 − 1/(n+2)`，本身是 binder），producer = P6R2 `hnotK_of_capWindowScalar_P6R2`（(CWS)+(SEP′)）/
`hnotK_of_capWindowWitness_P6R2`（(CWW)+时间半）、KD2 `hnotK_of_P5L_diagonal_P6KD2`、SN
`hnotK_of_diagonal_cws_P6SN`——都在**另一族**（P6CD 的 `K n`、`yG n`、`t n`）。HP6B2 槽的族（`Kh k`、bad `y k`、
crossing `p′`、`t ↑ σ_k`）的前缀**没有** non-CWP 条款，加条款 = 改冻结槽形（禁止）。
**repair target（精确）**：`hnCWPslot` ⇐ P6R2 (CWS)+(SEP′) 在本族的孪生：(CWS) late cap-window 点的标量下界
`η·scale ≤ R(t, z)`（年龄 `≤ ½ scale⁻¹`、`‖w‖ < Dcap + 1`；owner = cap 链 / hcapWL，HP6B2 已付
`hcapWL_std_of_P5L_P6HPB`）；(SEP′) 新近 record 尺度分离 `2·R_k < η·scale`（owner = HFOOT / SCALESEP，
`hscaleSep` 槽同源；FOOT2 G3 `record_scaleSep_P6SS` 只给 event `i k` 本身的 record）；连续性 `R(t, p′) → R_k`
（`RegularCrossing.scalar_eq`，`t ↑ σ`）。反证同 P6R2：`R(t, p′) ≥ η·scale > 2R_k > R(t, p′)`。
生成：build-logs/scratch/O-CH11-FOOT5/gen/gen_g3.py。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory

/-- **G3a `hmargin_slot_P6F5`**（PROVED，0 binder）：结论 = HP6B2 v2 `hmargin` 槽逐字；= FOOT2
`hmargin_of_supplies_P6F2` 在 HP6b env 上实例化（常数比较全部已付，见文件头）。 -/
theorem hmargin_slot_P6F5 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)) (δ : ℝ), 0 < δ →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            riemannianEDistOf ((Kh k).stageMetric (i k).castSucc t)
                ((seedTrace k).point (i k).castSucc h1 h2) p' ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal δ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt
  subst hε hC1 hC2 hCt
  obtain ⟨F₀, q₀, -, -, ⟨hF₀, hq₀, -⟩, -, -, ⟨-, -, hδ₀⟩, ⟨-, -, -, hP5L₀⟩, -⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨-, hcanS, -, -⟩ := GC.LongTime.Ch11.outerSupply_twoLevel_C11G2 hS hfine F q₀ hF hq₀
    (GC.LongTime.Ch11.C1ceil_le_C1P6_C11GT6 p6X1std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.C2ceil_le_C2P6_C11GT6 p6X2std_C11GT6.{u} Γ)
    (GC.LongTime.Ch11.Ctime_le_p6Ctime_C11G7B.{u} Γ)
  have hΓ : Γ.epsilon < 1 / 11 := by
    have := Γ.epsilon_small
    linarith
  exact hmargin_of_supplies_P6F2 F (Ctime := p6Ctime_C11G7B.{u} Γ) Γ.epsilon_pos hΓ
    (GC.LongTime.Ch11.capCollar_le_C1P6_C11CL3 Γ) (GC.LongTime.Ch11.capCollar_le_C2P6_C11CL3 Γ)
    hP5L₀ hδ₀ hcanS le_rfl le_rfl le_rfl

/-- **G3b `hrecords_slot_of_nCWP_P6F5`**（PROVISIONAL[`hnCWPslot`]）：结论 = HP6B2 v2 `hrecords` 槽
逐字；records 投影（S14 rescaled）PROVED，late non-CWP = `hnCWPslot`（linked late records 形）。 -/
theorem hrecords_slot_of_nCWP_P6F5 (P : OrientedThreeStage.{u}) (g : P.Metric)
    (εP6 : ClosedBirthConstants → ClosedBirthConstants → ℝ)
    (hnCWPslot :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∃ ζstar : ℝ, 0 < ζstar ∧
      ∀ (Rrad ζ₀ Dcap : ℝ), 0 < ζ₀ → ζ₀ ≤ ζstar →
      ∀ (p : ℕ → CutoffParameters) (Tthr : ℝ)
        (records : ∀ (n : ℕ) (e : Fin (F.tower.history n).eventCount),
          Tthr ≤ (F.tower.history n).time e.succ →
            GeometricCutoffRecord (F.tower.history n).toHistory e (p n)),
        (∀ n, Rrad ≤ (p n).modelRadius ∧ (p n).modelAccuracy ≤ ζ₀ ∧ 2 ≤ (p n).modelOrder) →
        (∀ n (s : ℝ), 0 ≤ s → (p n).delta s = q.delta s ∧ (p n).neckRadius s = q.neckRadius s) →
        (∀ n, (p n).recenterConstant = pB.recenterConstant) →
        (∀ n e he b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records n e he).static b)) →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
            (hT : Tthr ≤ (F.tower.history (ind k)).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
            (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
            (b : ((Kh k).event i').RetainedBoundaryIndex)
            (w : standardCapWindow (p (ind k)).modelRadius),
            Btr.point i'.succ le_rfl hl =
                (((records (ind k) i' hT).rescale_P6M (c k) (hc k)).static b).window w ∧
              ‖w.val‖ < Dcap + 1 ∧
              t - (Kh k).time i'.succ ≤ 1 / 2 *
                ((((records (ind k) i' hT).rescale_P6M (c k) (hc k)).static b).neck.scale)⁻¹) :
      ∀ {pB : CutoffParameters} {Γ Γf : ClosedBirthConstants}, FineOf_C11G2.{u} Γf Γ →
      Γ.epsilon ≤ εStrong_C12X.{u} → Γ.epsilon ≤ epsW_CXOU2.{u} →
      ∀ (Cdist : ℝ≥0) (εReserve : ℝ)
        (T : BlockTower_C11W pB Γf P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γf.Ctime j
        (T.block j) (T.lookahead j) (T.request j)) →
      SameConstructionRetentionSupplyPlus_C11GT6 T →
      ∀ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters), F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      pB.modelAccuracy ≤ εP6 Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (Rrad ζ₀ B Dcap : ℝ), 0 < ζ₀ →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (T₀ : ℝ)
          (records : ∀ i' : Fin (Kh k).eventCount, T₀ ≤ (Kh k).time i'.succ →
            GeometricCutoffRecord (Kh k) i' pp),
          (∀ i' hT b, ((records i' hT).static b).hasCanonicalWindow) ∧
          Rrad ≤ pp.modelRadius ∧ 2 ≤ pp.modelOrder ∧ pp.modelAccuracy ≤ ζ₀ ∧
          T₀ ≤ (σ k : ℝ) - B / R k ∧
          ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ¬ ∃ (i' : Fin (Kh k).eventCount)
              (hT : T₀ ≤ (Kh k).time i'.succ) (hl : i'.succ ≤ (i k).castSucc)
              (Btr : BackwardPointTrace (Kh k) i'.succ (i k).castSucc hl p')
              (b : ((Kh k).event i').RetainedBoundaryIndex)
              (w : standardCapWindow pp.modelRadius),
              Btr.point i'.succ le_rfl hl = ((records i' hT).static b).window w ∧
                ‖w.val‖ < Dcap + 1 ∧
                t - (Kh k).time i'.succ ≤ 1 / 2 * (((records i' hT).static b).neck.scale)⁻¹ := by
  intro pB Γ Γf hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad hord ε C1 C2 Ctime
    hε hC1 hC2 hCt Rrad ζ₀ B Dcap hζ₀ ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  obtain ⟨F₀, q₀, -, -, ⟨hF₀, hq₀, ⟨-, -, -, -, hprc₀⟩⟩, -, -, -, ⟨-, -, -, hP5L₀⟩, -⟩ := id hS
  have hFF : F = F₀ := GC.LongTime.Ch11.rawSurgery_eq_of_tower_eq_C11KW (hF.trans hF₀.symm)
  subst F₀
  obtain ⟨ζs, hζs, hbind0⟩ := hnCWPslot hfine hs hW Cdist εReserve T hcert hS F q hF hq hacc hrad
    hord hε hC1 hC2 hCt
  have hζ₁ : 0 < min ζ₀ ζs := lt_min hζ₀ hζs
  obtain ⟨Tthr, hTthr⟩ := hP5L₀ Rrad (min ζ₀ ζs) 2 hζ₁
  choose p hpδ hpρ _hpf hprc hD hacc' hord' hrec using hTthr
  choose records hlink using hrec
  have hlinkq : ∀ n (s : ℝ), 0 ≤ s →
      (p n).delta s = q.delta s ∧ (p n).neckRadius s = q.neckRadius s := by
    intro n s hs0
    refine ⟨?_, ?_⟩
    · rw [hpδ n]
      exact (hq₀ s hs0).1.trans (hq s hs0).1.symm
    · rw [hpρ n]
      exact (hq₀ s hs0).2.trans (hq s hs0).2.symm
  have hbind := hbind0 Rrad (min ζ₀ ζs) Dcap hζ₁ (min_le_right _ _) p Tthr records
    (fun n => ⟨hD n, hacc' n, hord' n⟩) hlinkq
    (fun n => (hprc n).trans hprc₀) hlink ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y
    R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroom hradii i hi
  have hlate : Tendsto (fun k => c k * (σ k : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_)
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        two_pos)
    have hck := hc k
    have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have hcl := hclock k
    have h1k := h1 k
    have hT := hTc k
    nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
      mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]
  have hBR : ∀ᶠ k in atTop, B / R k ≤ 1 / 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * |B|)] with k hk
    rw [div_le_iff₀ (hRpos k)]
    have hR1 := hRr k
    linarith [le_abs_self B]
  filter_upwards [hbind, hlate.eventually_ge_atTop (2 * Tthr), hBR] with k hk hk2 hkB
  have hσ1 : (1 : ℝ) ≤ σ k := (h1 k).trans (Subtype.coe_le_coe.mpr (has k))
  have hck := hc k
  have hT0 : Tthr / c k ≤ (σ k : ℝ) - B / R k := by
    rw [div_le_iff₀ hck]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (σ k : ℝ) / 2 - B / R k by linarith) hck.le]
  have conv : ∀ i' : Fin (Kh k).eventCount, Tthr / c k ≤ (Kh k).time i'.succ →
      Tthr ≤ (F.tower.history (ind k)).time i'.succ := by
    intro i' hT
    have e : c k * (Kh k).time i'.succ = (F.tower.history (ind k)).time i'.succ :=
      mul_div_cancel₀ _ (hc k).ne'
    rw [← e]
    rw [div_le_iff₀ hck] at hT
    linarith
  refine ⟨(p (ind k)).rescale_P6N (c k) (hc k), Tthr / c k,
    fun i' hT => (records (ind k) i' (conv i' hT)).rescale_P6M (c k) (hc k),
    fun i' hT b => ?_, hD (ind k), hord' (ind k), (hacc' (ind k)).trans (min_le_left _ _), hT0, ?_⟩
  · exact ((records (ind k) i' (conv i' hT)).static b).hasCanonicalWindow_rescale_P6M
      (GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
        (hlink (ind k) i' (conv i' hT) b)) (c k) (hc k)
  · intro p' q' hq' hcr
    filter_upwards [hk p' q' hq' hcr] with t ht
    rintro ⟨i', hT, hl, Btr, b, w, hw1, hw2, hw3⟩
    exact ht ⟨i', conv i' hT, hl, Btr, b, w, hw1, hw2, hw3⟩

/-- consumer（G3 → HP6B2 v2）：`hmargin` 槽由 G3a 付（0 binder），`hrecords` 槽由 G3b 付（binder `hnCWPslot`），
喂 `hP6bTwoLevelTime_of_slots_v2_P6HPB2`（其余参数保持 binder）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := fun εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8 hgapJF hgapJF8 hnCWPslot
      hpinch hderivL hgradL hdistLA hscaleSep hcollar =>
    hP6bTwoLevelTime_of_slots_v2_P6HPB2 P g εP6 hεP6 Csel T₀sel Qtsel hmono Cgsel hgapJ hgapJ8
      hgapJF hgapJF8 (hmargin_slot_P6F5 P g εP6) (hrecords_slot_of_nCWP_P6F5 P g εP6 hnCWPslot)
      hpinch hderivL hgradL hdistLA hscaleSep hcollar
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
