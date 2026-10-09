import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12GapTopV7TwoC11G7B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FinalCoarseBadTopP6FK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SmallDeltaRecordsP6HD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateRecordsSixP6H6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Gamma2ContractC11G2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HP6bAssemblyP6HPB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnDefsCH2

set_option autoImplicit false

/-!
[CEILHN2：自 `P6HcapWLStdCHN.lean` 机械克隆]
# CHN G2h：hcapWL_std（HN ceiling）

CEIL-HN 孪生（O-CH11-CEILHN，后缀 `_CHN`）：自 `P6HP6bAssemblyP6HPB.lean` 机械克隆
（生成器 `build-logs/scratch/CEILHN/gen/clone.py`），ceiling 常数换 HN 扩展。
-/

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)
open GC.GeneralFlow (ClosedBirthConstants)
open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6 p6FineEta_pos_C11GT6 epsW_CXOU2)
open GC.LongTime.Ch11 (BlockTower_C11W capWindowRadius_C11E FineOf_C11G2 BudgetCertificate_C11GT2
  SameConstructionRetentionSupplyPlus_C11GT6 chainDiagonal_C11A C1P6_C11GT6 C2P6_C11GT6
  p6X1HN_CH2 p6X2HN_CH2 p6CtimeHN_CH2 p6BadCH2_CH2 htransMBadHN_CH2)
namespace ObservedHistory
open GC.LongTime.Ch11 (p6CoarseCH2_CH2 one_le_p6CoarseCH2_CH2 p6CoarseC_le_p6CoarseCH2_CH2)

/-- **`hcapWL` 在标准 ceiling 常数处（已付）**：P5L supply（任意 `q`）⇒ FINCOARSE G3 的 `hcapWL` 槽在
`(Γ.ε, C1P6 std Γ, C2P6 std Γ)` 处。`hcapWL_of_P5L_P6H6` 的 `Cs` 是 `∃` 匿名常数；此处改用 GT6
`capWitness_at_C1P6HN_CH2`（闭项 `p6CapCs ≤ C1P6 / C2P6 std`）+ `hrec_of_P5L_P6H6`，证明照
`hcapWL_of_records_P6HB`。 -/
theorem hcapWL_std_of_P5L_P6HPB_CH2 (Γ : ClosedBirthConstants) {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q) :
    ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric Γ.epsilon
              (C1P6_C11GT6.{u} p6X1HN_CH2.{u} Γ) (C2P6_C11GT6.{u} p6X2HN_CH2.{u} Γ)
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)),
              W.capTubeHasNeckChart Γ.epsilon := by
  intro ind c hc Kh i hlate
  obtain ⟨Rcap, mcap, εcap, hεcap, hW⟩ := GC.LongTime.Ch11.capWitness_at_C1P6HN_CH2.{u} Γ
  filter_upwards [hrec_of_P5L_P6H6 hP5L ind c hc i hlate εcap Rcap mcap hεcap] with k hk
  obtain ⟨pp, Rc, hcan, hacc, hrad, hord⟩ := hk
  exact ⟨pp, Rc, fun b x => hW (Rc.static b) (hcan b) hacc hrad hord x⟩
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
