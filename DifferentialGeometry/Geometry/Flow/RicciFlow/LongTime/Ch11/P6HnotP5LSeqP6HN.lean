import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcwwSeqP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataDiagonalP6KD2

/-!
# θ n 形 hnotK 的 diagonal 参数由 P5L late supply 付（O-CH11-HNOT-LOCALDT / HNOT-A3 G8，后缀 `_P6HN`）

`hnotK_of_P5L_diagonal_P6KD2`（(CWS) 路线，P6KdataDiagonalP6KD2:184）的 (CWW) 孪生：G7
`hnotK_of_capWindow_seq_P6HN` 的逐 `n` 参数 `Cb Rn ζ δ₀ m₀`（只依赖 `(C, θ, n)`，先于 K 数据）由
`diagonalPack_of_lateKdata_P6KD2` 在 tower 帧 `K n = F.tower.history (ind n)` 上付清：records 精度 / 半径 / 阶、
late δ（`pF n := q`，全 records `CutoffRecords_C11S`）、出生尺度（`Cb' n = min (Cb n) (1/(n+1)²)`，无条件形
⇒ G2 的条件形）、`1 ≤ a₀·scale`；`a₀`、`hHI` 由 `exists_initialHI_P6WR`。INTEGRATION-ONLY（证明体 = P6KD2
consumer 逐项换源）。剩余前提：P5L 供给 / `hδq` / antitone / 全 records（同 P6KD2）、前缀 Dt 两条、`hsel`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`hnotK_of_P5L_capWindow_seq_P6HN`（INTEGRATION-ONLY）**：tower 帧、年龄序列 `θ n < 1` 的 hnotK，
diagonal 参数由 P5L late supply 付；不带 `hcww`、不带 `hsep`。 -/
theorem hnotK_of_P5L_capWindow_seq_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ (C : ℝ≥0) {θ : ℕ → ℝ}, (∀ n, θ n < 1) →
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q → Tendsto q.delta atTop (𝓝 0) →
      GC.LongTime.Ch11.CutoffRecords_C11S F q →
      ∀ (ind : ℕ → ℕ) (Q : ℕ → ℝ), (∀ n, 0 < Q n) →
      ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, Cs ≤ C1' → Cs ≤ C2' → Ctime₀ ≤ Ctime' →
      ∀ {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ},
      (∀ n, (F.tower.history (ind n)).time (j n).castSucc < t n) →
      (∀ n, t n < (F.tower.history (ind n)).time (j n).succ) →
      (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C (Q n) (j n).castSucc) →
      (∀ n, ((F.tower.history (ind n)).toHistory.event (j n)).incoming.DerivativeBoundBefore
        C (Q n) (t n)) →
      ∀ {yG : ∀ n, ((F.tower.history (ind n)).stage (j n).castSucc).Carrier}
        {Kh : ℕ → ObservedHistory.{u}}, Kh = (fun n => (F.tower.history (ind n)).toHistory) →
      ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier),
        (∀ n, (σ n : ℝ) = t n) → (∀ n, HEq (y n) (yG n)) →
        (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
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
              θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, hall⟩ := RetainedCoreHistory.hnotK_of_capWindow_seq_P6HN.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun C θ hθ P g F q hanti hP5L hδq records ind Q hQ => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, -, hζ, hδ, hdiag⟩ := hall C hθ
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  have hCb' : ∀ n : ℕ, 0 < min (Cb n) (1 / ((n : ℝ) + 1) ^ 2) ∧
      min (Cb n) (1 / ((n : ℝ) + 1) ^ 2) ≤ 1 / ((n : ℝ) + 1) ^ 2 :=
    fun n => ⟨lt_min (hCb n) (by positivity), min_le_right _ _⟩
  obtain ⟨Tmin, hT⟩ := diagonalPack_of_lateKdata_P6KD2 (H := F.tower.history) (q := q)
    (fun n => min (Cb n) (1 / ((n : ℝ) + 1) ^ 2)) Rn ζ δ₀ m₀ hCb' hζ hδ ha₀ Q hP5L hδq hanti
  refine ⟨Tmin, fun T₀ hT₀ => ?_⟩
  obtain ⟨p, recordsK, hcan, hδF, hacc, hrad, hord, hbirth, hbirthA⟩ := hT T₀ hT₀ ind
  refine ⟨p, recordsK, fun {C1' C2' Ctime'} hC1 hC2 hCt {j t} hjt htj hder hcur {yG Kh} hKh σ y
    hσ hyG hsel => ?_⟩
  exact hdiag hC1 hC2 hCt (K := fun n => F.tower.history (ind n)) hjt htj (Q := Q) (T₀ := T₀)
    (p := p) (pF := fun _ => q) (recordsK := recordsK) (fun n i => records (ind n) i)
    (a₀ := a₀) (fun n x => hHI (ind n) x) hcan hδF hacc hrad hord hQ hder hcur
    (fun n i hi b _ _ => (le_max_left _ 1).trans ((hbirth n i hi b).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _)
        ((recordsK n i hi).static b).neck.scale_pos.le)))
    (fun n i hi b _ _ => hbirthA n i hi b) hKh σ y hσ hyG hsel

/-- consumer（`_P6HN`）：θ₀ 常序列（SLICE-BCBD G5 槽年龄）与 `θ n = 1 − 1/(n+2)`（closed 主形 (CWW)）都满足
`θ n < 1`，同一 `(Ctime₀, Cs)` 服务两者。 -/
example {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) {θ₀ : ℝ} (hθ₀ : θ₀ < 1) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
      (∀ n : ℕ, (fun _ : ℕ => θ₀) n < 1) ∧ ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := by
  obtain ⟨Ct₀, Cs, hCt₀, hCs, -⟩ := hnotK_of_P5L_capWindow_seq_P6HN.{0} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun _ => hθ₀, fun n => ?_⟩
  have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
