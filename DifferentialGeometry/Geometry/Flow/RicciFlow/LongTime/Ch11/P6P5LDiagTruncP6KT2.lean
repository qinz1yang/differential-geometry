import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateKdataNomDiagCXKN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformTruncP6KT2

/-!
# P5L 对角包装件的截断孪生（O-CH11-KTRUNC2b 续，期 3；后缀 `_P6KT2`）

`hnotK_of_P5L_diagonal_P6KD2`（P6KdataDiagonalP6KD2:184）与 `hnotK_of_P5L_diagonal_CXKN`
（P6LateKdataNomDiagCXKN:223）都是 `hnotK_of_diagonal_cws_P6SN` 的包装（hslab 只透传）。孪生：
hslab（塔帧 `EventSlabsDerivative … (Fin.last)`）→
`DerivativeBoundBefore … (min (time j'.succ) (tK n))`，
全称量加 `tK`，坏点时刻处加连接前提 `t n ≤ tK n`（调用方取 `tK := Tno`，`c·σ ≤ Tno` ⇐ `hsT`），
内部调 G2a `hnotK_of_diagonal_cws_T_P6KT2`。其余逐字。生成器 `gen/gen_p5l.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **截断孪生（`_P6KT2`，期 3 对角包装件）**：`hnotK_of_P5L_diagonal_P6KD2` 的 hslab 换截断形（塔帧终点
`min (time j'.succ) (tK n)`）+ 坏点时刻连接前提 `t n ≤ tK n`，内部调 `hnotK_of_diagonal_cws_T_P6KT2`。
原 docstring：
 **consumer：P5L supply + (SEP′) ⇒ `hnotK`（`_P6KD2`）**。`c` 与 diagonal 序列取自
`hnotK_of_diagonal_cws_P6SN`；K 层 `hcanK hδF hacc hrad hord hbirth hbirthA` 全由
`diagonalPack_of_lateKdata_P6KD2`（`H := F.tower.history`，`pF := q`）供给，`a₀ hHI` 由
`exists_initialHI_P6WR`。残余显式义务：`hP5L hδq hanti records`、`hslabK`、(SEP′) `hsep`。 -/
theorem hnotK_of_P5L_diagonal_T_P6KT2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q → Tendsto q.delta atTop (𝓝 0) →
      GC.LongTime.Ch11.CutoffRecords_C11S F q →
      ∀ (ind : ℕ → ℕ) (Q tK : ℕ → ℝ),
      (∀ n (j' : Fin (F.tower.history (ind n)).eventCount),
        ((F.tower.history (ind n)).toHistory.event j').incoming.DerivativeBoundBefore C (Q n)
          (min ((F.tower.history (ind n)).time j'.succ) (tK n))) →
      ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      ∀ {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ},
      (∀ n, (F.tower.history (ind n)).time (j n).castSucc < t n) →
      (∀ n, t n < (F.tower.history (ind n)).time (j n).succ) →
      (∀ n, t n ≤ tK n) →
      ∀ {yG : ∀ n, ((F.tower.history (ind n)).stage (j n).castSucc).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = ((F.tower.history (ind n)).toHistory.event (j n)).incoming.flow.scalar (t n)
        (yG n)) →
      (∀ n (i : Fin (F.tower.history (ind n)).eventCount)
        (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
        (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (F.tower.history (ind n)).time i.succ ≤
          (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (F.tower.history (ind n)).eventCount)
          (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
          (hl : i.succ ≤ (j n).castSucc)
          (A : BackwardPointTrace (F.tower.history (ind n)).toHistory i.succ (j n).castSucc hl
            (yG n))
          (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (F.tower.history (ind n)).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := hnotK_of_diagonal_cws_T_P6KT2.{u}
  refine ⟨c, hc, fun C {P g F q} hanti hP5L hδq records ind Q tK hslab => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Tmin, hT⟩ := diagonalPack_of_lateKdata_P6KD2 (H := F.tower.history) (q := q) Cb Rn ζ δ₀
    m₀ hCb (fun n => (hζ n).1) (fun n => (hδ n).1) ha₀ Q hP5L hδq hanti
  refine ⟨Tmin, fun T₀ hT₀ => ?_⟩
  obtain ⟨p, recordsK, hcan, hδF, hacc, hrad, hord, hbirth, hbirthA⟩ := hT T₀ hT₀ ind
  refine ⟨p, recordsK, fun {j t} hjt htj htK {yG R} hRn' hsep => ?_⟩
  exact hdiag (K := fun n => F.tower.history (ind n)) hjt htj (pF := fun _ => q)
    (fun n i => records (ind n) i) (a₀ := a₀) (fun n x => hHI (ind n) x) hcan hδF hacc hrad hord
    htK hslab hbirth hbirthA hRn' hsep

/-- **截断孪生（`_P6KT2`，期 3 对角包装件）**：`hnotK_of_P5L_diagonal_CXKN` 的 hslab 换截断形（塔帧终点
`min (time j'.succ) (tK n)`）+ 坏点时刻连接前提 `t n ≤ tK n`，内部调 `hnotK_of_diagonal_cws_T_P6KT2`。
原 docstring：
 **consumer 孪生（`_CXKN`）**：`hnotK_of_P5L_diagonal_P6KD2` 的 nominal 版。`hP5L` 为带 nominal 合取的
形（参考 records = `records`，即 `CutoffRecords_C11S F q`）；结论在**同一** `p recordsK` 上先给
`p.delta/recenter` 与 nominal 识别（对 `records (ind n) i`），再给 `hnotK` 的 `∀ j …`（逐字同
`_P6KD2`）。J4/J5/J7/J8/J12/J13 取同一 witness。 -/
theorem hnotK_of_P5L_diagonal_nom_T_P6KT2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      Tendsto q.delta atTop (𝓝 0) →
      ∀ (records : GC.LongTime.Ch11.CutoffRecords_C11S F q),
      (∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
        p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
        p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
        m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
          T ≤ (F.tower.history k).time i.succ →
          GeometricCutoffRecord (F.tower.history k).toHistory i p,
        (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
        ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
          (rs i hi).delta = (records k i).delta ∧
          (rs i hi).order = (records k i).order ∧
          (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
          (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
              ((records k i).static b).inclusion (((records k i).static b).witness.cap z)) →
      ∀ (ind : ℕ → ℕ) (Q tK : ℕ → ℝ),
      (∀ n (j' : Fin (F.tower.history (ind n)).eventCount),
        ((F.tower.history (ind n)).toHistory.event j').incoming.DerivativeBoundBefore C (Q n)
          (min ((F.tower.history (ind n)).time j'.succ) (tK n))) →
      ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      ((∀ n, (p n).delta = q.delta) ∧ (∀ n, (p n).recenterConstant = q.recenterConstant) ∧
        ∀ n (i : Fin (F.tower.history (ind n)).eventCount)
          (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ),
          (recordsK n i hi).nominalRadius = (records (ind n) i).nominalRadius ∧
          (recordsK n i hi).delta = (records (ind n) i).delta ∧
          (recordsK n i hi).order = (records (ind n) i).order ∧
          (∀ α, HEq ((recordsK n i hi).neck α) ((records (ind n) i).neck α)) ∧
          (∀ b, ((recordsK n i hi).static b).neck.scale =
            ((records (ind n) i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((recordsK n i hi).static b).inclusion
                (((recordsK n i hi).static b).witness.cap z) =
              ((records (ind n) i).static b).inclusion
                (((records (ind n) i).static b).witness.cap z)) ∧
      ∀ {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ},
      (∀ n, (F.tower.history (ind n)).time (j n).castSucc < t n) →
      (∀ n, t n < (F.tower.history (ind n)).time (j n).succ) →
      (∀ n, t n ≤ tK n) →
      ∀ {yG : ∀ n, ((F.tower.history (ind n)).stage (j n).castSucc).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = ((F.tower.history (ind n)).toHistory.event (j n)).incoming.flow.scalar (t n)
        (yG n)) →
      (∀ n (i : Fin (F.tower.history (ind n)).eventCount)
        (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
        (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (F.tower.history (ind n)).time i.succ ≤
          (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (F.tower.history (ind n)).eventCount)
          (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
          (hl : i.succ ≤ (j n).castSucc)
          (A : BackwardPointTrace (F.tower.history (ind n)).toHistory i.succ (j n).castSucc hl
            (yG n))
          (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (F.tower.history (ind n)).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := hnotK_of_diagonal_cws_T_P6KT2.{u}
  refine ⟨c, hc, fun C {P g F q} hanti hδq records hP5L ind Q tK hslab => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Tmin, hT⟩ := diagonalPack_nom_CXKN (H := F.tower.history) (q := q) records Cb Rn ζ δ₀
    m₀ hCb (fun n => (hζ n).1) (fun n => (hδ n).1) ha₀ Q hP5L hδq hanti
  refine ⟨Tmin, fun T₀ hT₀ => ?_⟩
  obtain ⟨p, recordsK, hcan, hδF, hacc, hrad, hord, hbirth, hbirthA, hpδ, hprc, hnom⟩ :=
    hT T₀ hT₀ ind
  refine ⟨p, recordsK, ⟨hpδ, hprc, hnom⟩, fun {j t} hjt htj htK {yG R} hRn' hsep => ?_⟩
  exact hdiag (K := fun n => F.tower.history (ind n)) hjt htj (pF := fun _ => q)
    (fun n i => records (ind n) i) (a₀ := a₀) (fun n x => hHI (ind n) x) hcan hδF hacc hrad hord
    htK hslab hbirth hbirthA hRn' hsep

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
