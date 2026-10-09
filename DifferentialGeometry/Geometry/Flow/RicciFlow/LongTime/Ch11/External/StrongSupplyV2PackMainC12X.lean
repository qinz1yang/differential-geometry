import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongSupplyV2PackC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileFullC11F

set_option autoImplicit false

/-!
# O-C12X-S16C (G2)：hStrong v2 打包定理 `strongCanonicalSupplyV2_of_towerFull_C12X`

输入（设计 `out/CH12X-S16-design.md` §5 G3）：tower 晚期 slice 上 `R > ρ⁻²` 的点有 canonical witness，
neck 分支在最后 stage 上带 Full strong neck——入射 slab `G`（在 `[time last, t]` 上与 stage 度量一致）
上的 `HistoryStrongNeckFull_C12X`（O-C12X-S16B G2a，深度 1、精度 `ε`）。前提逐项写成显式
`∀ / ∃`（无新具名 Prop）。逐点打包由 G1 的 `strongNeckV2Branch_of_full_C12X`（`H := s.history`，
`t := s.time`，`s.history.horizon = s.time` 为 `rfl`）给出。

consumer：`a12Enhanced_of_chain_towerFull_C12X` = `a12Enhanced_of_chain_C11P2`，`hext` 的 S16 合取项
`StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2` 换成上面的 tower Full 前提（其余逐字）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set Filter TopologicalSpace
open scoped Topology NNReal ContDiff Manifold

namespace GC.LongTime.Ch11

universe u

/-- **S16 打包**：tower 晚期点上"W 是 neck ⇒ 最后 stage 上的 Full strong neck" ⇒ hStrong v2。 -/
theorem strongCanonicalSupplyV2_of_towerFull_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 : ℝ}
    (hfull : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier, (ρ s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric ε C1 C2 x,
        W.capTubeHasNeckChart ε ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (s' : ℝ)
            (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
            (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
              G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
            s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G ε x s.time) :
    StrongCanonicalSupplyV2_C11E F ρ ε C1 C2 := by
  obtain ⟨T, hT⟩ := hfull
  refine ⟨T, fun s hs x hR => ?_⟩
  obtain ⟨W, hW, hneck⟩ := hT s hs x hR
  refine ⟨W, hW, fun nk hnk => ?_⟩
  obtain ⟨s', G, hG, hF⟩ := hneck nk hnk
  exact strongNeckV2Branch_of_full_C12X s.history hG rfl
    (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR) hF

/-- **v1 投影**：同一前提给 hStrong v1（`strongCanonicalSupplyV1_of_v2_C11F`）。 -/
theorem strongCanonicalSupplyV1_of_towerFull_C12X {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ρ : ℝ → ℝ} {ε C1 C2 : ℝ}
    (hfull : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier, (ρ s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
      ∃ W : SpatialCanonicalWitness s.metric ε C1 C2 x,
        W.capTubeHasNeckChart ε ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (s' : ℝ)
            (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
            (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
              G.flow.base.metric τ = s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
            s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G ε x s.time) :
    StrongCanonicalSupplyV1_C11F F ρ ε C1 C2 :=
  strongCanonicalSupplyV1_of_v2_C11F (strongCanonicalSupplyV2_of_towerFull_C12X hfull)

/-- **A12′ 从链（S16 换成 tower Full 前提）**：`a12Enhanced_of_chain_C11P2` 的 `hext`，S16 合取项
`StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2` 换成 `strongCanonicalSupplyV2_of_towerFull_C12X`
的前提（`ρ := q.neckRadius`；其余 19 项逐字）。 -/
theorem a12Enhanced_of_chain_towerFull_C12X {pBase : CutoffParameters}
    {C : GC.GeneralFlow.ClosedBirthConstants} {P : OrientedThreeStage.{u}} {g : P.Metric}
    (hP3 : CollarWindowSupply_C11E.{u} pBase)
    (hprof : ModelConstraintsSupply_C11E pBase εProf_C11E.{u})
    (hext : ∃ S : GC.GeneralFlow.PreparedSpatialChain pBase C P g,
      ∃ (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (κ : ℝ → ℝ)
        (records : CutoffRecords_C11S F q) (ε C1 C2 : ℝ),
        F.tower = S.tower ∧ ε = C.epsilon ∧
        (q.fixed = pBase.fixed ∧ q.modelRadius = pBase.modelRadius ∧
          q.modelOrder = pBase.modelOrder ∧ q.modelAccuracy = pBase.modelAccuracy) ∧
        CanonicalConstantsSupply_C11S ε C1 C2 ∧ (∀ t : ℝ, 0 < κ t) ∧ Antitone κ ∧
        AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
        HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 ∧
        (∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) (n : ℝ) →
          (F.tower.history n).NoncollapsedBefore (κ t) ε t) ∧
        Tendsto q.delta atTop (𝓝 0) ∧ RecentCutoffSupply_C11S records ∧
        LargerBallScalarLargeSupply_C11S F q.delta (diagonalAccuracy_C11S q.delta) ∧
        LinkedWindowsSupply_C11E records ∧ TimeDerivativeSupply_C11E F q.neckRadius C.Ctime ∧
        LateLinkedRecordsSupply_C11E F q ∧ LargerBallCanonicalLateSupply_C11E F ε C1 C2 ∧
        (∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
          ∀ x : s.stage.Carrier, (q.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x →
          ∃ W : SpatialCanonicalWitness s.metric ε C1 C2 x,
            W.capTubeHasNeckChart ε ∧
            ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
              ∃ (s' : ℝ)
                (G : s.stage.IncomingSlab (s.history.time (Fin.last s.history.eventCount)) s'),
                (∀ τ ∈ Icc (s.history.time (Fin.last s.history.eventCount)) s.time,
                  G.flow.base.metric τ =
                    s.history.stageMetric (Fin.last s.history.eventCount) τ) ∧
                s.history.HistoryStrongNeckFull_C12X (Fin.last s.history.eventCount) G ε x
                  s.time) ∧
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupply_C11E F q) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, hfull, h19, h20⟩ := hext
  exact a12Enhanced_of_chain_C11P2 hP3 hprof ⟨S, F, q, κ, records, ε, C1, C2, h1, h2, h3, h4,
    h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    strongCanonicalSupplyV2_of_towerFull_C12X hfull, h19, h20⟩

end GC.LongTime.Ch11
