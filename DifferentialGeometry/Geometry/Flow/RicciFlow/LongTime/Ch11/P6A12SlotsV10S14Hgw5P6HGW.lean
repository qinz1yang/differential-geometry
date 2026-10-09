import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6A12SlotsV10LocActualS14CXW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyV7LocHgw5P6HGW

set_option autoImplicit false

/-!
# A12′ 顶层孪生（W9S 基底）：hgap 四槽换成开放核，Level 3（O-CH11-HGAPWIRE，后缀 `_P6HGW`）

孪生 `a12EnhancedFull_of_slots_v10_loc_s14_sel_W9S`（10 binder → 10 binder，生成器
`build-logs/scratch/HGW/gen/gen_top6.py`）。四个 Θ 形 hgap 槽换成 `_hres{J,J8,JF,JF8}`：同一 env 前缀，
加 `∀ a₀ (ha₀) (hHI)`、`∃ Θ`，结论为开放核（`HgwRes*`，abbreviation of producer premise conjuncts,
no new content，可 unfold）。
* 事件槽：`hgapJ_loc_of_producers_q0kTD_fresh_J16`（本车道 EvQ0，J8 q0kTD 同法：J7 ⇐ hpc/hδ₀Cb/hT₀Λ、
  J13 ⇐ hnom+hrcs，
  J6 ⇐ recent（引擎），J14 → hDext，J16 ⇐ J16PT）；核 = `hpc ∧ hδ₀Cb ∧ hJ11 ∧ hOpenJ(无 J6/J16)`。
* J8 槽：J16PT `q0kTD_fresh_J16` producer（含 J16 付）（J7 ⇐ `hpc / hδ₀Cb / hT₀Λ`，hOpen 收窄 witness 形）；
  J6 由 SEPFIX recent 付（`j6_of_recent_seq_P6HGW`，阈值 `recentThr ≤ T₀`，无子列）；
  核 = `hpc ∧ hδ₀Cb ∧ hJ11 ∧ hOpen8J(无 J6)`。
* JF / JF8：G1b fresh producer 不变（HNOT G9 cap-window 待 O1/O2，FCOND 未交，留接口）。
已付：TDS、hanti、hδq、hP5L、records、nom（SCRS⁺ 见证）、J15*（FRESH）、阈值并入 Θ。无新 binder。
-/

noncomputable section

universe u

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1std_C11GT6 p6X2std_C11GT6 p6Ctime_C11G7B p6BadC_C11G2 htransMBad_C11G7B)

namespace ObservedHistory
open GC.GeneralFlow (PreparedSpatialChain)

/-- hgap 四槽 = 开放核（10 binder）。 -/
theorem a12EnhancedFull_of_slots_v10_loc_s14_hgw5_P6HGW
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∀ (_hkerJx : NotKKernelExpT_P6KT.{u}) (_hkerJ : NotKKernelDecT_P6KT2.{u})
    (_hkerFx : FinalKernelExpT_P6KT.{u}) (_hkerF8 : FinalKernelDecT_P6KT2.{u})
    (_hresJ :
      ∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
      (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) → (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) →
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResE2_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    (_hresJ8 :
      ∀ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
      (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ (2 : ℕ)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) →
      (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) → (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) →
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJ8F_P6HGW F q ε C1 C2 Ctime Ctime₀ T₀ (fun _ => (0 : ℝ)) Cb Rn ζ δ₀ m₀ a₀)
    (_hresJF :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJF_P6HGW F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (_hresJF8 :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {a₀ : ℝ}, 0 < a₀ →
      (∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x) →
      ∃ Θ : ℕ → ℝ,
      ∀ {ε C1 C2 : ℝ} {Ctime Ctime₀ : ℝ≥0} {T₀ : ℕ → ℝ}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ → Ctime₀ = Γf.Ctime → (∀ n, Θ n ≤ T₀ n) →
      HgwResJF8_P6HGW F q ε C1 C2 Ctime T₀ (fun _ => (0 : ℝ)) a₀)
    (_hstaySlot :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ (T r : ℝ), 0 < T → 0 < r →
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
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
              (m : Fin ((Kh k).eventCount + 1)) (hf : first ≤ m) (hm : m ≤ (i k).castSucc)
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              t - T / R k ≤ (v : ℝ) → (v : ℝ) ≤ t → (Kh k).activeStage v = m →
            ∀ zz : ((Kh k).stageAt v).Carrier, HEq zz (B.point m hf hm) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) zz ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))
      )
    (_hdistLA :
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
      pB.modelAccuracy ≤ εSel_W9S.{u} Γ Γf → capWindowRadius_C11E + 1 ≤ pB.modelRadius →
      2 ≤ pB.modelOrder →
      ∀ {ε C1 C2 : ℝ} {Ctime : ℝ≥0}, ε = Γ.epsilon →
      C1 = C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ →
      C2 = C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ →
      Ctime = p6Ctime_C11G7B.{u} Γ →
      ∀ Aseed : ℝ, 1 < Aseed →
        ∀ (T r : ℝ), 0 < T → 0 < r →
        ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
          let Kh : ℕ → ObservedHistory.{u} := fun k =>
            ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
          ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
            (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
          ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
            (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
            (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
            (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
              riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
                ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                  (pT k) 1)) →
            (∀ k, 2 < (Tn k : ℝ)) →
            (∀ k (w : ℝ), (Tn k : ℝ) - 1 ^ 2 / 2 ≤ w → w ≤ (Tn k : ℝ) →
              q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k) ≤ 1) →
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
            (∀ᶠ k in atTop,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                    ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((Aseed + 3) * 1)) →
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
            (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
            ((Kh k).event (i k)).RegularCrossing p' q →
            ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
              (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)),
            ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : ℝ,
              t - T / R k ≤ τ → τ ≤ t → (Kh k).time (i k).castSucc < τ →
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
                riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
                    ((seedTrace k).point (i k).castSucc h1 h2) z ≤
                  riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
                    ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1),
    GC.LongTime.Ch11.A12EnhancedFullConclusion_C11F P g := by
  intro hkerJx hkerJ hkerFx hkerF8 hresJ hresJ8 hresJF hresJF8 hstaySlot hdistLA
  obtain ⟨Rn, mn, hslot⟩ := GC.LongTime.Ch11.hspineTwoLevelTime_of_recent_PB_CXW.{u} P g
  exact GC.LongTime.Ch11.a12EnhancedFull_of_v8_collar_actual_S14CXW P g Rn mn hslot
    (hP6bTwoLevelTimeCollar_of_slots_v7_loc_hgw5_P6HGW P g hkerJx hkerJ hkerFx hkerF8 εSel_W9S.{u}
      εSel_pos_W9S.{u} (fun _ _ => 4) (fun _ _ => le_rfl)
      hresJ hresJ8 hresJF hresJF8 (hinit_slot_P6HI P g εSel_W9S.{u})
      (hrecT_slot_P6HI P g εSel_W9S.{u}) hstaySlot hdistLA)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
