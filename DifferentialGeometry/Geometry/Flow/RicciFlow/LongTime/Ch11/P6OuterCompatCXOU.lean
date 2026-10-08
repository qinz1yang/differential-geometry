import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV6FwdC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilingC11GT6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6JointFinalP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformSuppliesC12X

/-!
# OuterCompat：由 SCRS⁺ 与 P6 ceiling 支付 `canonicalLateCore_of_jointD_P6CK` 的外层前提
（CX-OUTER，后缀 `_CXOU`；处置 R-C11-10 D-1）

`canonicalLateCore_of_jointD_P6CK`（`P6JointFinalP6CK.lean:743–1000`）在 `hgapJ` 之外的前提：
ε 门槛、`C ≤ C1 / C ≤ C2 / C.toNNReal ≤ Ctime`、`AntitoneOn q.neckRadius`、`HistoryCanonicalSupply`、
`TimeDerivativeSupply`、`Monotone T₀ / Qt`（`Ctime₀ T₀ Qt` 为 ∀，位于 `hgapJ` 之前，即 selection 之前）。

* G1（PROVED）`outerSupply_of_scrsPlus_CXOU`：SCRS⁺ ⇒ Antitone ∧ HCS ∧ TDS，常数可任意放大
  （HCS：`C1 ≥ max C1s Cbirth`、`C2 ≥ …`；TDS：`Ctime ≥ Γ.Ctime`）；`q` 与 SCRS⁺ 的 `q₀` 只在 `t ≥ 0`
  上一致，故先证 `neckRadius` 的 congruence。`outerSupply_ceiling_CXOU`：放大到 `C1P6 X1 Γ / C2P6 X2 Γ`
  与 `max Γ.Ctime C.toNNReal`（`C` 为 joint 的 `∃ C`）。
* G2（PROVISIONAL）`canonicalLateCore_of_jointD_scrsPlus_CXOU`：joint 定理的外层前提被 SCRS⁺ + ceiling 支付，
  剩余 binder 只有两类（BLOCKED 项，见 DELIVERIES）：(a) ε 门槛 `ε ≤ epsW`（joint 自己的 `∃ epsW`，
  `Γ.epsilon = ε`）；(b) `C ≤ C1P6 X1 Γ`、`C ≤ C2P6 X2 Γ`（joint 的 `∃ C` 不是 `p6CoarseC`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- `HistoryCanonicalSupply` 只读 `ρ` 在 `t ≥ 0` 的值。 -/
theorem historyCanonicalSupply_congr_CXOU {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ ρ' : ℝ → ℝ} {ε C1 C2 : ℝ}
    (h : HistoryCanonicalSupply_C11S F ρ ε C1 C2) (hρ : ∀ t : ℝ, 0 ≤ t → ρ t = ρ' t) :
    HistoryCanonicalSupply_C11S F ρ' ε C1 C2 := by
  intro n t x hx
  rw [← hρ (t : ℝ) t.2.1] at hx
  exact h n t x hx

/-- `TimeDerivativeSupply`：`ρ` 只读 `t ≥ 0`（event 时刻非负）；`Ctime` 可放大。 -/
theorem timeDerivativeSupply_congr_mono_CXOU {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ ρ' : ℝ → ℝ} {C C' : ℝ≥0}
    (h : TimeDerivativeSupply_C11E F ρ C) (hρ : ∀ t : ℝ, 0 ≤ t → ρ t = ρ' t) (hC : C ≤ C') :
    TimeDerivativeSupply_C11E F ρ' C' := by
  obtain ⟨h1, h2⟩ := h
  have hc : (C : ℝ) ≤ C' := NNReal.coe_le_coe.2 hC
  refine ⟨fun n j y t ht hy => ?_, fun n hh y t ht hy => ?_⟩
  · have ht0 : 0 ≤ t :=
      ((F.tower.history n).toHistory.time_nonneg j.castSucc).trans ht.1.le
    rw [← hρ t ht0] at hy
    exact (h1 n j y t ht hy).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  · have ht0 : 0 ≤ t :=
      ((F.tower.history n).toHistory.time_nonneg (Fin.last _)).trans ht.1.le
    rw [← hρ t ht0] at hy
    exact (h2 n hh y t ht hy).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- **G1**：SCRS⁺ ⇒ joint 定理的三个外层前提（`Antitone` / `HCS` / `TDS`），常数任意放大。 -/
theorem outerSupply_of_scrsPlus_CXOU {pB : CutoffParameters}
    {Γ : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t)
    {C1 C2 : ℝ} {Ctime : ℝ≥0} (hC1 : max Γ.C1s Γ.Cbirth ≤ C1)
    (hC2 : max Γ.C2s (max Γ.Cbirth (Γ.Cgrad : ℝ)) ≤ C2) (hCt : Γ.Ctime ≤ Ctime) :
    AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon C1 C2 ∧
      TimeDerivativeSupply_C11E F q.neckRadius Ctime := by
  obtain ⟨F₀, q₀, κ, records, h1, -, -, h4, -, h6, h7, -, -, -⟩ := hS
  obtain rfl : F₀ = F := rawSurgery_eq_of_tower_eq_C11KW (h1.1.trans hF.symm)
  have hnr : ∀ t : ℝ, 0 ≤ t → q₀.neckRadius t = q.neckRadius t := fun t ht =>
    ((h1.2.1 t ht).2).trans (hq t ht).2.symm
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [← hnr a ha, ← hnr b hb]
    exact h4.2.1 ha hb hab
  · exact historyCanonicalSupply_congr_CXOU (historyCanonicalSupply_mono_C12X h6 hC1 hC2) hnr
  · exact timeDerivativeSupply_congr_mono_CXOU h7 hnr hCt

/-- **G1（ceiling 版）**：放大到 `C1P6 X1 Γ / C2P6 X2 Γ` 与 `max Γ.Ctime C.toNNReal`
（`C` = joint 的 `∃ C`，故 `C.toNNReal ≤ Ctime` 由构造给出）。 -/
theorem outerSupply_ceiling_CXOU {pB : CutoffParameters} {Γ : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (X1 X2 : GC.GeneralFlow.ClosedBirthConstants → ℝ) (C : ℝ)
    {T : BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve}
    (hS : SameConstructionRetentionSupplyPlus_C11GT6 T)
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (hF : F.tower = T.toChain.tower)
    (hq : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) :
    AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon (C1P6_C11GT6.{u} X1 Γ)
        (C2P6_C11GT6.{u} X2 Γ) ∧
      TimeDerivativeSupply_C11E F q.neckRadius (max Γ.Ctime C.toNNReal) :=
  outerSupply_of_scrsPlus_CXOU hS F q hF hq (oldC1_le_C1P6_C11GT6.{u} X1 Γ)
    (oldC2_le_C2P6_C11GT6.{u} X2 Γ) (le_max_left _ _)

/-- consumer（G1 端到端，producer-closed）：W0 证书 + ModelSmallness ⇒ SCRS⁺ ⇒ 标准 ceiling
`p6X1std / p6X2std` 处的 `Antitone / HCS / TDS`（`C` 任意，如 joint 的 `∃ C`）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ εS : GC.GeneralFlow.ClosedBirthConstants → ℝ, (∀ Γ, 0 < εS Γ) ∧
    ∀ {pB : CutoffParameters} {Γ : GC.GeneralFlow.ClosedBirthConstants} (Cdist : ℝ≥0)
      (εReserve : ℝ) (T : BlockTower_C11W pB Γ P g Cdist 1 (capWindowRadius_C11E + 1) εReserve),
      (∀ j, BudgetCertificate_C11GT2 pB.recenterConstant Γ.Ctime j (T.block j) (T.lookahead j)
        (T.request j) ∧ RequestCofinal_C11W4 j (T.request j)) →
      pB.modelAccuracy ≤ εS Γ → capWindowRadius_C11E + 1 ≤ pB.modelRadius → 2 ≤ pB.modelOrder →
      ∀ (C : ℝ) (F : GC.Interface.RawSurgery P g) (q : CutoffParameters),
      F.tower = T.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A T.toChain).delta t ∧
        q.neckRadius t = (chainDiagonal_C11A T.toChain).neckRadius t) →
      AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius Γ.epsilon
          (C1P6_C11GT6.{u} p6X1std_C11GT6.{u} Γ) (C2P6_C11GT6.{u} p6X2std_C11GT6.{u} Γ) ∧
        TimeDerivativeSupply_C11E F q.neckRadius (max Γ.Ctime C.toNNReal) := by
  obtain ⟨εS, hεS, h⟩ := sameConstructionRetentionSupplyPlus_of_tower_C11GT6 P g
  exact ⟨εS, hεS, fun Cdist εReserve T hQ ha hr ho C F q hF hq =>
    outerSupply_ceiling_CXOU p6X1std_C11GT6.{u} p6X2std_C11GT6.{u} C
      (h Cdist εReserve T hQ ha hr ho) F q hF hq⟩

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **G2（PROVISIONAL）**：`canonicalLateCore_of_jointD_P6CK` 的外层前提由 SCRS⁺ + P6 ceiling 支付。
与 joint 定理相比：`Antitone / HCS / TDS` 不再是前提（由 `Tw` 的 SCRS⁺ 给出），`C1 C2 Ctime`
固定为 `C1P6 X1 Γ`、`C2P6 X2 Γ`、`max Γ.Ctime C.toNNReal`；`Ctime₀ T₀ Qt` 仍在 `hgapJ` 之前量化
（selection 之前选定）。剩余 binder：`Γ.epsilon = ε`（连同 `ε ≤ epsW` 门槛）与
`C ≤ C1P6 X1 Γ`、`C ≤ C2P6 X2 Γ`。 -/
theorem canonicalLateCore_of_jointD_scrsPlus_CXOU :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ),
    (∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ 2) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n ∧ ζ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n ∧ δ₀ C n ≤ 1 / ((n : ℝ) + 1)) ∧
    (∀ (C : ℝ≥0) (n : ℕ), (n : ℝ) + 1 ≤ Rn C n) ∧ (∀ (C : ℝ≥0) (n : ℕ), n + 2 ≤ m₀ C n) ∧
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X1 X2 : GC.GeneralFlow.ClosedBirthConstants → ℝ)
      {P : OrientedThreeStage.{u}} {g : P.Metric} {pB : CutoffParameters}
      {Γ : GC.GeneralFlow.ClosedBirthConstants} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
      (Tw : GC.LongTime.Ch11.BlockTower_C11W pB Γ P g Cdist cMax Dstar εReserve),
      GC.LongTime.Ch11.SameConstructionRetentionSupplyPlus_C11GT6 Tw → Γ.epsilon = ε →
      C ≤ GC.LongTime.Ch11.C1P6_C11GT6.{u} X1 Γ → C ≤ GC.LongTime.Ch11.C2P6_C11GT6.{u} X2 Γ →
      ∀ {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      F.tower = Tw.toChain.tower →
      (∀ t : ℝ, 0 ≤ t → q.delta t = (GC.LongTime.Ch11.chainDiagonal_C11A Tw.toChain).delta t ∧
        q.neckRadius t = (GC.LongTime.Ch11.chainDiagonal_C11A Tw.toChain).neckRadius t) →
      ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C1 = GC.LongTime.Ch11.C1P6_C11GT6.{u} X1 Γ →
      C2 = GC.LongTime.Ch11.C2P6_C11GT6.{u} X2 Γ → Ctime = max Γ.Ctime C.toNNReal →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapJ : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters) (Qs : ℕ → ℝ)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          0 < a₀ ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) a₀ x ∧
            -3 / a₀ ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) ∧
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, max (Qs n) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qs n) (Fin.last (Ho n).eventCount)) ∧
          (∀ n, c n * Qs n < R n) ∧
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ) ∧
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) ∧
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stageAt (σ n)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
                ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨c₀, hc₀, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, hRn, hm₀, epsW, hepsW, hB⟩ :=
    canonicalLateCore_of_jointD_P6CK.{u}
  refine ⟨c₀, hc₀, Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ₀, hRn, hm₀, epsW, hepsW,
    fun ε hε hsmall hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall hεW hεX hεN hεcone
  refine ⟨C, hC, fun X1 X2 {P g pB Γ Cdist cMax Dstar εReserve} Tw hS hΓ hC1 hC2 {F q} hF hq
    {C1 C2 Ctime} hC1e hC2e hCte Ctime₀ T₀ Qt hT₀m hQm hgap hrest => ?_⟩
  subst hΓ hC1e hC2e hCte
  obtain ⟨hanti, hcan, hder⟩ := GC.LongTime.Ch11.outerSupply_ceiling_CXOU X1 X2 C hS F q hF hq
  exact hB' hC1 hC2 (le_max_right _ _) hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgap hrest

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
