import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A

set_option autoImplicit false

/-!
# O-CH11-OUTER (G3)：block tower ⇒ `PreparedSpatialChain` ⇒ A12（显式前提清单）+ (F) 路线对齐

两条到 `∃ S : PreparedSpatialChain` 的路：
(i) 经 astra `SH/PreparedSpatialExistence`（E1 闭包落地后直接给 `∃ S`；ASM 车道 `A12OfExistenceC11A`）；
(ii) 经本车道合同 `tower_of_blockSteps_C11W`（G2）。本文件给 (ii) 的 A12 形与 (F) 对齐：
`blockStep_of_astraStepShape_C11W`：astra `exists_prepared_spatial_step_with_quality_and_distance_
scalars_and_small_test_margin_with_reserve_quality`（`SH/PreparedSpatialStep:1112`，PENDING）在
`E = b_j, B = 3^j, Bnext = 3^(j+1), activation = (5/6)3^j, η = 1/(j+2)` 处的结论形（`makeCap` 支）
+ W2 的导数界维护 ⇒ `BlockStep_C11W j`。即：E1 落地后 (W-step) 只差 `TimeDerivativeControl` 的维护。

A12 的完整显式前提清单（`a12_of_blockSteps_C11W`）：Γ = `pBase`、`C : ClosedBirthConstants`、
`Cdist cMax Dstar εReserve`；W0-base：`X₀` 带 `Inv_C11W`、`history = atZero`、`radius ≤ 1`；
W1–W4：`∀ j, BlockStep_C11W … j`；S8（P6）：对每个以 `X₀` 起头的 block tower `T`，S8 在
`T.toChain` 上。W0（`budgetChoice_C11W`）与 W5（`tower_of_blockSteps_C11W`、`toChain`）是定理。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open Set Filter
open scoped NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **(F) 对齐**：astra step 结论形（specialised 到第 `j` 块）+ W2 导数界维护 ⇒ `BlockStep_C11W j`。
`ℓ` 打包 astra 的 `(nextClass, rNext)`；Inv 的 fit / reserve 沿 `HEq Y.prepared ℓ.nextClass` 运输。 -/
theorem blockStep_of_astraStepShape_C11W {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric} {Cdist : ℝ≥0} {cMax Dstar εReserve : ℝ}
    (j : ℕ)
    (hshape : ∀ X : BlockState_C11W pBase C P g j, X.DistanceData Cdist →
      ∃ ℓ : BlockLookahead_C11W X,
        ℓ.nextClass.HasReserveQuality Dstar εReserve ∧ ℓ.nextClass.HasDistanceExtension Cdist ∧
        0 < ℓ.rNext ∧ ℓ.rNext ≤ X.radius ∧ ℓ.nextClass.Qall ≤ (ℓ.rNext ^ 2)⁻¹ ∧
        ℓ.rNext * Real.sqrt ℓ.nextClass.Qall ≤ 100 * cMax ∧
        ∀ (εcut Dcut : ℝ) (mcut : ℕ), 0 < εcut → 0 < Dcut →
        ∀ accuracyCap : ℝ, 0 < accuracyCap →
          ∃ d : ℝ, 0 < d ∧ d < 1 ∧ d ≤ X.parameters.delta (preparedSpatialHorizon j) ∧
            d ≤ accuracyCap ∧
          ∃ Y : BlockState_C11W pBase C P g (j + 1),
            Y.radius = ℓ.rNext ∧ Y.shift = X.history.time (Fin.last X.history.eventCount) ∧
            Y.offset = X.history.eventCount ∧
            Y.nativeStage = X.native.stage (Fin.last X.native.eventCount) ∧
            HEq Y.nativeMetric (X.native.initialMetric (Fin.last X.native.eventCount)) ∧
            HEq Y.prepared ℓ.nextClass ∧ Y.DistanceData Cdist ∧
            PreparedSpatialSuccessor X Y ((5 / 6 : ℝ) * 3 ^ j) (1 / ((j : ℝ) + 2)) d ∧
            Nonempty (PreparedSpatialStepRetention X Y d (1 / ((j : ℝ) + 2)) εcut Dcut mcut))
    (hderiv : ∀ (X : BlockState_C11W pBase C P g j) (Y : BlockState_C11W pBase C P g (j + 1))
      (ℓ : BlockLookahead_C11W X) (req : BlockRequest_C11W) (d : ℝ),
      Inv_C11W Cdist cMax Dstar εReserve X → PhysicalExtension_C11W X Y ℓ req d →
      TimeDerivativeControl_C11W Y) :
    BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j := by
  intro X hX
  obtain ⟨ℓ, hres, hdist, hr, hrle, hQ, hfit, make⟩ := hshape X hX.distance
  refine ⟨ℓ, lookaheadReady_of_class_C11W ℓ hr hrle hQ hfit hres hdist, ?_⟩
  intro req hreq
  obtain ⟨d, hd, hd1, -, hdcap, Y, hrad, hshift, hoff, hstage, hmetric, hprep, hYdist, hsucc,
    hret⟩ := make req.epsCut req.Dcut req.mcut hreq.epsCut_pos hreq.Dcut_pos req.accuracyCap
      hreq.cap_pos
  have hPE : PhysicalExtension_C11W X Y ℓ req d :=
    ⟨hsucc, hd, hd1, hdcap, hshift, hoff, hstage, hmetric, hrad, hprep, hret⟩
  obtain ⟨hQall, hRes⟩ := preparedClass_heq_transport_C11W hstage hmetric
    (congrArg (fun s => (3 : ℝ) ^ (j + 1) - s) hshift) hprep Dstar εReserve
  refine ⟨Y, d, hPE, ⟨?_, hRes.mpr hres, hYdist, hderiv X Y ℓ req d hX hPE⟩⟩
  rw [hrad, hQall]
  exact hfit

/-- **A12 ⇐ (W-step) + Inv_0 + S8（on the constructed tower）**（路线 (ii)）。结论逐字是 A12。 -/
theorem a12_of_blockSteps_C11W (P : OrientedThreeStage.{u}) (g : P.Metric)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (hS8 : ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve, T.block 0 = X₀ →
      ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) := by
  obtain ⟨T, hT, -⟩ := exists_chain_of_blockSteps_C11W hstep X₀ hX₀ hhist hrad
  exact exists_surgery_with_decaying_accuracy_of_someChain_C11A P g
    ⟨pBase, C, T.toChain, hS8 T hT⟩

/-- **A12 的最短显式前提清单**（W0、W0-base、W5 全部是定理）：Γ + capacity 1 的 prepared class
（参数 = `pBase`、distance rule、reserve quality）+ `∀ j, BlockStep_C11W j`【W1–W4】+ S8（对每个
block tower 的 `toChain`）【P6】。 -/
theorem a12_of_preparedBase_C11W (P : OrientedThreeStage.{u}) (g : P.Metric)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ) (hcMax : 0 < cMax)
    (prepared : ClosedBirthPreparedClass pBase C P g 1) (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist)
    (hres : prepared.HasReserveQuality Dstar εReserve)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (hS8 : ∀ T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve,
      ∀ F : GC.Interface.RawSurgery P g, F.tower = T.toChain.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A T.toChain).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A T.toChain).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) := by
  obtain ⟨X₀, hX₀, hhist, hrad⟩ :=
    exists_inv_base_C11W Cdist cMax Dstar εReserve hcMax prepared hbase hprepared hres
  exact a12_of_blockSteps_C11W P g pBase C Cdist cMax Dstar εReserve X₀ hX₀ hhist hrad hstep
    fun T _ => hS8 T

/-- consumer：同一前提（不要 S8）下，构造出的 chain 已给出 W1 的十项（S1–S7、S9 的原料），
且 tower 的第 0 块就是 `X₀`。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j) :
    ∃ (T : BlockTower_C11W pBase C P g Cdist cMax Dstar εReserve)
      (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
      (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
      T.toChain.state 0 = X₀ ∧ F.tower = T.toChain.tower ∧
      CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
      AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
      (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
        (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
      Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records := by
  obtain ⟨T, -, h0⟩ := exists_chain_of_blockSteps_C11W hstep X₀ hX₀ hhist hrad
  obtain ⟨F, q, κ, records, ε, C1, C2, hTower, -, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    -, hnc, hδlim, hrecent⟩ := w1_of_preparedSpatialChain_C11A T.toChain
  exact ⟨T, F, q, κ, records, ε, C1, C2, h0, hTower, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    hnc, hδlim, hrecent⟩

/-- consumer（(F) 路线端到端）：astra step 结论形 + 导数界维护（逐块）+ base + S8 ⇒ A12。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric)
    (pBase : CutoffParameters) (C : ClosedBirthConstants)
    (Cdist : ℝ≥0) (cMax Dstar εReserve : ℝ)
    (X₀ : BlockState_C11W pBase C P g 0) (hX₀ : Inv_C11W Cdist cMax Dstar εReserve X₀)
    (hhist : X₀.history = RetainedCoreHistory.atZero P g) (hrad : X₀.radius ≤ 1)
    (hstep : ∀ j, BlockStep_C11W pBase C P g Cdist cMax Dstar εReserve j)
    (hS8 : ∀ S : PreparedSpatialChain pBase C P g,
      ∀ F : GC.Interface.RawSurgery P g, F.tower = S.tower →
        LargerBallScalarLargeSupply_C11S F (chainDiagonal_C11A S).delta
          (diagonalAccuracy_C11S (chainDiagonal_C11A S).delta)) :
    (∃ (δ : ℝ → ℝ) (F : GC.Interface.RawSurgery P g),
      AntitoneOn δ (Set.Ici 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε) ∧
      hasAnalyticAdmissibility F δ) :=
  a12_of_blockSteps_C11W P g pBase C Cdist cMax Dstar εReserve X₀ hX₀ hhist hrad hstep
    fun T _ => hS8 T.toChain

/-- consumer：W0-base 的条件 inhabitant 与 overlap 免费引理联用（型对齐）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {pBase : CutoffParameters}
    {C : ClosedBirthConstants} (Cdist : ℝ≥0) (cMax : ℝ) (hcMax : 0 < cMax)
    (prepared : ClosedBirthPreparedClass pBase C P g 1) (hbase : prepared.parameters = pBase)
    (hprepared : prepared.HasDistanceExtension Cdist) :
    ∃ X : BlockState_C11W pBase C P g 0, X.DistanceData Cdist ∧
      X.history = RetainedCoreHistory.atZero P g ∧
      X.native.NoncollapsedBefore X.prepared.kappa C.epsilon X.native.horizon := by
  obtain ⟨X, hdist, hhist, -, -, -⟩ :=
    exists_blockState_base_C11W Cdist cMax hcMax prepared hbase hprepared
  exact ⟨X, hdist, hhist, (overlap_of_state_C11W X).1⟩

end GC.LongTime.Ch11
