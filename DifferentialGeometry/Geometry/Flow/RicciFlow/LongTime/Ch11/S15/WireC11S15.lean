import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.S15.ScalarToCanonicalC11S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.S15.SliceBridgeC11S15
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2

set_option autoImplicit false

/-!
# S-CH11-S15 G2：装配 `LargerBallCanonicalLateSupply_C11E`（S15 = P6 (b)）（`_C11S15`）

`s15_of_s8_C11S15`：S7（accuracy 数值律）+ S8（`LargerBallScalarLargeSupply_C11S`，A > 1）+
canonical supply（history 形，阈值 `ρ`）+ 显式 band 前提 `hband`
⇒ `LargerBallCanonicalLateSupply_C11E F ε C1 C2`（= `P6LateSupply_P6A`，RegularSlice 形）。
装配：`A ≤ 1` 用 `largerBallCanonicalLateAt_of_le_one_P6A`
（经 `largerBallCanonicalLate_of_large_P6A`），`A > 1` 用 G1，再用 G2a 的 slice 桥
（`largerBallCanonicalLateSupply_of_history_C11S15`）转成 RegularSlice 形。

**缺口形 `hband`**（G1 的 band 前提对全部 `A > 1`、全部 `r̄ > 0`）：
`r̄√t < r`（且 `2r² < t`）、`K₁ r⁻² ≤ R(y) ≤ ρ(t)⁻²` 的点有带 neck chart 的 canonical witness。
它是 KL 84.1(b) 的实质（大尺度 `r ~ √t` 时 `R ≥ K₁ r⁻²` 只是 `R ≳ 1/t`，远低于 canonical 阈值
`ρ(t)⁻²`），由 P6 线（E-local 收口）负责证明；本文件不证，也不当作已证。`∀ r̄` 是因为 S8 的 `r̄` 是
`∃`（想用 S8 给的那个 `r̄` 的消费者用 G1 的 `∃ rbar` 形，更弱）。

consumer `example`：`a12Enhanced_of_chain_C11P2` 的 `hext` 里 P6 (b) 合取项换成 `hband`
（其余合取项原样），经本定理给出该合取项。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- **G2**：S7 + S8 + canonical supply + band 缺口 ⇒ S15 = `LargerBallCanonicalLateSupply_C11E`。 -/
theorem s15_of_s8_C11S15 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ ρ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {ε C1 C2 : ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α)
    (hS8 : LargerBallScalarLargeSupply_C11S F δ α)
    (hcanon : HistoryCanonicalSupply_C11S F ρ ε C1 C2)
    (hband : ∀ A : ℝ, 1 < A → ∀ rbar : ℝ, 0 < rbar → ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → rbar * Real.sqrt t < r → 2 * r ^ 2 < (t : ℝ) →
          hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
            K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
            metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ (ρ t ^ 2)⁻¹ →
            ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
              W.capTubeHasNeckChart ε) :
    LargerBallCanonicalLateSupply_C11E F ε C1 C2 := by
  refine largerBallCanonicalLateSupply_of_history_C11S15 (largerBallCanonicalLate_of_large_P6A ?_)
  intro A hA
  obtain ⟨rbar, hrbar, himp⟩ :=
    largerBallCanonicalLate_of_scalarLarge_C11S15 hacc (zero_lt_one.trans hA) (hS8 A hA) hcanon
  exact himp (hband A hA rbar hrbar)

/-- consumer：`a12Enhanced_of_chain_C11P2` 的 `hext` 里 P6 (b)（`LargerBallCanonicalLateSupply_C11E`）
合取项换成 `hband`（`ρ := q.neckRadius`、`α := diagonalAccuracy_C11S q.delta`，S7 由 `hδanti` 给），
其余合取项原样；S15 合取项由 `s15_of_s8_C11S15` 给，得 `A12EnhancedConclusion_C11E`。 -/
example {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
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
        LateLinkedRecordsSupply_C11E F q ∧
        (∀ A : ℝ, 1 < A → ∀ rbar : ℝ, 0 < rbar → ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
          ∀ n, let H := (F.tower.history n).toHistory;
          ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
            T ≤ (t : ℝ) → rbar * Real.sqrt t < r → 2 * r ^ 2 < (t : ℝ) →
            hasSmallParabolicCurvature H t p r →
            ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
            ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
              K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
              metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ (q.neckRadius t ^ 2)⁻¹ →
              ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ε C1 C2 y,
                W.capTubeHasNeckChart ε) ∧
        StrongCanonicalSupplyV2_C11E F q.neckRadius ε C1 C2 ∧
        CompatibleCapsSupply_C11E F q records ∧ FrontierCollarSupply_C11E F q) :
    A12EnhancedConclusion_C11E P g := by
  obtain ⟨S, F, q, κ, records, ε, C1, C2, hF, hε, hq, hconst, hκ, hκanti, hδanti, hρanti, hcan,
    hnc, hδlim, hrecent, hS8, hP1, hP2, hP5, hband, hStrong, hCompat, hRFC⟩ := hext
  exact a12Enhanced_of_chain_C11P2 hP3 hprof
    ⟨S, F, q, κ, records, ε, C1, C2, hF, hε, hq, hconst, hκ, hκanti, hδanti, hρanti, hcan, hnc,
      hδlim, hrecent, hS8, hP1, hP2, hP5,
      s15_of_s8_C11S15 (largerBallAccuracySupply_diagonal_C11S q hδanti) hS8 hcan hband,
      hStrong, hCompat, hRFC⟩

end GC.LongTime.Ch11
