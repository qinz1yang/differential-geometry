import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixProdHNF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CeilHnRCH2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10JP

/-!
# MJ G2：hnot producer 的单一元组（`(ε, Ctd)` 定出，后缀 `_MJ`）

`hnotK_seq_a0_HNF` 的 `hall Ctd θ`（`θ n = 1 − 1/(n+2)`）给出元组 `(Cb Rn ζ δ₀ m₀)`，该元组只依赖
`(ε, Ctd)`（经 `Cs`/`Ctime₀`）。本文件把它**标准化**成消费点直接可用的单一元组
`(Nf ζ Rn δ₀ m₀)`：`Nf = Cb⁻¹`，`ζ ≤ 1/(n+1)`，`Rn ≥ max (n+1) (transitionEnd + 11)`，`δ₀ ≤ 1/(n+1)`，
`m₀ ≥ n+2`；并把 hnotK 结论在标准化元组处重述（birth 写成 `Nf n * Q n ≤ scale`）。

* `hnotPackEx_MJ`（PROVED）：存在性 + 标准化规格 + hnotK 在标准化元组处的结论；
* `hnotNf_MJ / hnotζ_MJ / hnotRn_MJ / hnotδ_MJ / hnotm_MJ`：元组分量 = 存在性定理的 `Classical.choose`
  （`hε`、`hε'` 为显式参数，无 `dite`）；`hnotPack_spec_MJ`：数值规格（PROVED）。消费点
  取 `Classical.choose_spec` 链的最后一个合取得到 hnotK 在该元组处的结论。
元组固定后再取 Θ（T0K 供给对该元组），不是 `∀` 元组形；无新 binder / Prop。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **单一元组的存在性与标准化规格（`_MJ`，PROVED）**：`(Nf ζ Rn δ₀ m₀)` 只依赖 `(ε, Ctd)`；
最后一个合取是 `hnotK_seq_a0_HNF` 的 `hall` 结论在标准化元组处的重述。 -/
theorem hnotPackEx_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) :
    ∃ (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Nf n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n : ℕ, ζ n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n) ∧ (∀ n : ℕ, StandardCap.transitionEnd + 11 ≤ Rn n) ∧
      (∀ n, 0 < δ₀ n) ∧ (∀ n : ℕ, δ₀ n ≤ 1 / ((n : ℝ) + 1)) ∧ (∀ n : ℕ, n + 2 ≤ m₀ n) ∧
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C1' →
      GC.LongTime.Ch11.csSeq_CH2.{u} ε ≤ C2' → GC.LongTime.Ch11.ctSeq_CH2.{u} ε ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon),
      (∀ n, (K n).time (j n).castSucc < (σ n : ℝ)) → (∀ n, (σ n : ℝ) < (K n).time (j n).succ) →
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
      (∀ n, (K n).EventSlabsDerivative Ctd (Q n) (j n).castSucc) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore Ctd (Q n) (σ n)) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        (σ n : ℝ) - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Nf n * Q n ≤ ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        (σ n : ℝ) - (K n).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) →
    ∀ (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}, (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (K n).toHistory.HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  have hX := RetainedCoreHistory.hnotK_seq_a0_HNF.{u} hε hε'
  have e1 : GC.LongTime.Ch11.csSeq_CH2.{u} ε =
      Classical.choose (Classical.choose_spec hX) := by
    unfold GC.LongTime.Ch11.csSeq_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
  have e2 : GC.LongTime.Ch11.ctSeq_CH2.{u} ε = Classical.choose hX := by
    unfold GC.LongTime.Ch11.ctSeq_CH2; rw [dite_eq_left ⟨hε, hε'⟩]
  obtain ⟨-, -, hall⟩ := Classical.choose_spec (Classical.choose_spec hX)
  obtain ⟨Cb, Rn0, ζ0, δ0, m0, hCb, hRn0, hζ0, hδ0, hprod⟩ :=
    hall Ctd (θ := fun n => 1 - 1 / ((n : ℝ) + 2)) RetainedCoreHistory.thetaCap_lt_one_HNF
  have hte : (0 : ℝ) < StandardCap.transitionEnd + 11 := by
    have := StandardCap.transitionEnd_pos
    linarith
  refine ⟨fun n => (Cb n)⁻¹, fun n => min (ζ0 n) (1 / ((n : ℝ) + 1)),
    fun n => max (Rn0 n) (max ((n : ℝ) + 1) (StandardCap.transitionEnd + 11)),
    fun n => min (δ0 n) (1 / ((n : ℝ) + 1)), fun n => max (m0 n) (n + 2),
    fun n => inv_pos.mpr (hCb n), fun n => lt_min (hζ0 n) (by positivity),
    fun n => min_le_right _ _,
    fun n => (le_max_left _ _).trans (le_max_right _ _),
    fun n => (le_max_right _ _).trans (le_max_right _ _),
    fun n => lt_min (hδ0 n) (by positivity), fun n => min_le_right _ _,
    fun n => le_max_right _ _, ?_⟩
  intro C1' C2' Ctime' h1 h2 h3 K j σ hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδ hacc
    hrad hord hQ hD1 hD2 hbirth hbirthA y yG hyG hsel
  rw [e1] at h1 h2
  rw [e2] at h3
  exact hprod h1 h2 h3 σ hjt htj recordsF hHI hcanK
    (fun n i hi => (hδ n i hi).trans (min_le_left _ _))
    (fun n => (hacc n).trans (min_le_left _ _))
    (fun n => (le_max_left _ _).trans (hrad n))
    (fun n => (le_max_left _ _).trans (hord n)) hQ hD1 hD2
    (fun n i hi b hl hage => (inv_mul_le_iff₀ (hCb n)).mp (hbirth n i hi b hl hage))
    hbirthA y hyG hsel

/-- 元组的 `Nf` 分量（`hnotPackEx_MJ` 的 `Classical.choose`；以 `hε`、`hε'` 为显式参数，无 `dite`）。 -/
def hnotNf_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (hnotPackEx_MJ.{u} hε hε' Ctd)

/-- 元组的 `ζ` 分量。 -/
def hnotζ_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (hnotPackEx_MJ.{u} hε hε' Ctd))

/-- 元组的 `Rn` 分量。 -/
def hnotRn_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (hnotPackEx_MJ.{u} hε hε' Ctd)))

/-- 元组的 `δ₀` 分量。 -/
def hnotδ_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℝ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (hnotPackEx_MJ.{u} hε hε' Ctd))))

/-- 元组的 `m₀` 分量。 -/
def hnotm_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (hnotPackEx_MJ.{u} hε hε' Ctd)))))

/-- **标准化规格（`_MJ`，PROVED）**：元组分量满足存在性定理的数值规格（`Classical.choose_spec` 逐层）。 -/
theorem hnotPack_spec_MJ {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (Ctd : ℝ≥0) :
    (∀ n, 0 < hnotNf_MJ.{u} hε hε' Ctd n) ∧ (∀ n, 0 < hnotζ_MJ.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, hnotζ_MJ.{u} hε hε' Ctd n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 ≤ hnotRn_MJ.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, StandardCap.transitionEnd + 11 ≤ hnotRn_MJ.{u} hε hε' Ctd n) ∧
      (∀ n, 0 < hnotδ_MJ.{u} hε hε' Ctd n) ∧
      (∀ n : ℕ, hnotδ_MJ.{u} hε hε' Ctd n ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, n + 2 ≤ hnotm_MJ.{u} hε hε' Ctd n) := by
  have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (hnotPackEx_MJ.{u} hε hε' Ctd)))))
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
