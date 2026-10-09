import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnSpecCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResEngineSupplyT0K

/-!
# FSUP W3：final 帧 hnot producer 的单一元组（`(ε, Ctd)` 定出，后缀 `_FS`）

`P6HnrTupleMJ` 的 final 孪生：`hnotK_final_cww_at_CH2`（`hnotK_final_cww_P6HN` 在 `csHN / ctHN` 处的显式规格，
元组 `(Cb Rn ζ δ₀ m₀)` 只依赖 `(ε, C)`）标准化成 T0K 供给直接可用的单一元组 `(Nf ζ Rn δ₀ m₀)`：
`Nf = Cb⁻¹`，`ζ ≤ 1/(n+1)`，`Rn ≥ max (n+1) (transitionEnd + 11)`，`δ₀ ≤ 1/(n+1)`，`m₀ ≥ n+2`。
* `hnotPackExF_FS`（PROVED）：存在性 + 数值规格 + final hnotK 在标准化元组处的结论；
* `hnotNfF_FS … hnotmF_FS` / `hnotPackF_spec_FS`：分量与规格；
* `thetaF_FS`：T0K 供给在该元组处的 `Θ`。
元组固定后再取 Θ，不是 `∀` 元组形；无新 binder / Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **单一元组的存在性与标准化规格（final，`_FS`，PROVED）**。 -/
theorem hnotPackExF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) :
    ∃ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Nf n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n : ℕ, ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, StandardCap.transitionEnd + 11 ≤ Rn n) ∧
      (∀ n, 0 < δ₀ n) ∧ (∀ n : ℕ, δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C1' →
      GC.LongTime.Ch11.csHN_CH2.{u} ε ≤ C2' → GC.LongTime.Ch11.ctHN_CH2.{u} ε ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {Tn : ℕ → ℝ}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
        (σ n : ℝ) < (K n).horizon) → (∀ n, (σ n : ℝ) ≤ Tn n) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℕ → ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
        -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n (j : Fin (K n).eventCount),
        ((K n).toHistory.event j).incoming.DerivativeBoundBefore Ctd (Q n)
          (min ((K n).time j.succ) (Tn n))) →
      (∀ n (hK : (K n).time (Fin.last (K n).eventCount) < (K n).horizon),
        (((K n).finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore
          Ctd (Q n) (min (K n).horizon (Tn n))) →
      (∀ n i hi b, Nf n * Q n ≤ ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
    ∀ (n : ℕ) (yG' : ((K n).stage (Fin.last (K n).eventCount)).Carrier), HEq (y n) yG' →
      ¬ (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ Fin.last (K n).eventCount)
        (A : BackwardPointTrace (K n).toHistory i.succ (Fin.last (K n).eventCount) hl yG')
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹) := by
  obtain ⟨-, -, hall⟩ := RetainedCoreHistory.hnotK_final_cww_at_CH2.{u} hε hε'
  obtain ⟨Cb, Rn0, ζ0, δ0, m0, hCb, hζ0, hδ0, hRn0, hm0, hprod⟩ := hall Ctd
  have hte : (0 : ℝ) < StandardCap.transitionEnd + 11 := by
    have := StandardCap.transitionEnd_pos
    linarith
  refine ⟨fun n => (Cb n)⁻¹, ζ0, fun n => max (Rn0 n) (StandardCap.transitionEnd + 11), δ0, m0,
    fun n => inv_pos.mpr (hCb n).1, fun n => (hζ0 n).1, fun n => (hζ0 n).2,
    fun n => (hRn0 n).trans (le_max_left _ _), fun n => le_max_right _ _,
    fun n => (hδ0 n).1, fun n => (hδ0 n).2, hm0, ?_⟩
  intro C1' C2' Ctime' h1 h2 h3 K Tn σ y hfin hσT Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδ
    hacc hrad hord hQ hD1 hDF hbirth hbirthA hsel
  exact hprod h1 h2 h3 σ y hfin hσT recordsF hHI hcanK hδ hacc
    (fun n => (le_max_left _ _).trans (hrad n)) hord hQ hD1 hDF
    (fun n i hi b => (inv_mul_le_iff₀ (hCb n).1).mp (hbirth n i hi b)) hbirthA hsel

/-- 元组的 `Nf` 分量。 -/
def hnotNfF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (hnotPackExF_FS.{u} hε hε' Ctd)

/-- 元组的 `ζ` 分量。 -/
def hnotζF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctd))

/-- 元组的 `Rn` 分量。 -/
def hnotRnF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctd)))

/-- 元组的 `δ₀` 分量。 -/
def hnotδF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (hnotPackExF_FS.{u} hε hε' Ctd))))

/-- 元组的 `m₀` 分量。 -/
def hnotmF_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctd)))))

/-- **标准化规格（final，`_FS`，PROVED）**。 -/
theorem hnotPackF_spec_FS {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) :
    (∀ n, 0 < hnotNfF_FS.{u} hε hε' Ctd n) ∧ (∀ n, 0 < hnotζF_FS.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, hnotζF_FS.{u} hε hε' Ctd n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ hnotRnF_FS.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, StandardCap.transitionEnd + 11 ≤ hnotRnF_FS.{u} hε hε' Ctd n) ∧
      (∀ n, 0 < hnotδF_FS.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, hnotδF_FS.{u} hε hε' Ctd n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, n + 2 ≤ hnotmF_FS.{u} hε hε' Ctd n) := by
  have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackExF_FS.{u} hε hε' Ctd)))))
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.1⟩

/-- **供给阈值 Θ（final，`_FS`）**：T0K 供给 `drvResE_records_of_engine_T0K` 在 `(ε, Ctd)` 定出的单一
元组处的 `Θ`。 -/
def thetaF_FS {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (drvResE_records_of_engine_T0K records hrcs hanti hδq hfine ha₀ hHI
    (hnotNfF_FS.{u} hε hε' Ctd) (hnotζF_FS.{u} hε hε' Ctd) (hnotRnF_FS.{u} hε hε' Ctd)
    (hnotδF_FS.{u} hε hε' Ctd) (hnotmF_FS.{u} hε hε' Ctd)
    (hnotPackF_spec_FS.{u} hε hε' Ctd).2.1 (hnotPackF_spec_FS.{u} hε hε' Ctd).2.2.2.2.2.1)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
