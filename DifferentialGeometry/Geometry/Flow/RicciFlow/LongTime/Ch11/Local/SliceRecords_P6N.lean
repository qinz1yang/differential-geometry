import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SlicePresentation_P6N
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves

/-!
# L-RS（续）：late records / `hcan` / `CapWindowPoint` 展开形在 `K.prefixAt k` 上的 transport（`_P6N`）

方案 B 的 SLT 窗口版（P6WIN-A）在 `H = K.prefixAt k` 上吃 late records（G2a 形）与 `¬ CapWindowPoint`
展开形。本文件：
* `prefixLateRecords_P6N`：K 的 late records ⇒ prefix 的 late records
  （树内 `geometricCutoffRecordOfPrefix` 逐点；阈值条件 `T₀ ≤ time i.succ` 定义等）；
  `static` 字段定义等 ⇒ `hcan`/`hscale` 原样。
* `not_capWindowPoint_prefix_of_late_P6N`：K 上（late records）`¬ CapWindowPoint` 展开形 ⇒ prefix 上的
  展开形（prefix 的 trace 经 `backwardPointTraceOfPrefix` 上推）。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- **`_P6N`**：K 的 late records ⇒ `K.prefixAt k` 的 late records
（逐点 `geometricCutoffRecordOfPrefix`）。 -/
def prefixLateRecords_P6N (k : Fin (K.eventCount + 1)) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p) :
    ∀ i : Fin (K.prefixAt k).eventCount, T₀ ≤ (K.prefixAt k).time i.succ →
      GeometricCutoffRecord (K.prefixAt k).toHistory i p :=
  fun i hi =>
    K.geometricCutoffRecordOfPrefix k (records (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) hi)

theorem prefixLateRecords_static_P6N (k : Fin (K.eventCount + 1)) {p : CutoffParameters}
    {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (i : Fin (K.prefixAt k).eventCount) (hi : T₀ ≤ (K.prefixAt k).time i.succ) :
    (K.prefixLateRecords_P6N k records i hi).static =
      (records (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) hi).static :=
  rfl

/-- `hcan` 沿 prefix 原样。 -/
theorem prefixLateRecords_hcan_P6N (k : Fin (K.eventCount + 1)) {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow) :
    ∀ i hi b, ((K.prefixLateRecords_P6N k records i hi).static b).hasCanonicalWindow :=
  fun i hi b => hcan (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) hi b

/-- **`_P6N`**：K 上 `¬ CapWindowPoint` 展开形（late records，stage `k`）⇒ `K.prefixAt k` 上的展开形
（终端 stage = `Fin.last`）。 -/
theorem not_capWindowPoint_prefix_of_late_P6N (k : Fin (K.eventCount + 1)) {p : CutoffParameters}
    {T₀ t Dcap θ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (y : (K.stage k).Carrier)
    (hnot : ¬ ∃ (j : Fin K.eventCount) (hT : T₀ ≤ K.time j.succ) (hl : j.succ ≤ k)
      (A : BackwardPointTrace K.toHistory j.succ k hl y)
      (b : (K.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - K.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) :
    ¬ ∃ (j : Fin (K.prefixAt k).eventCount) (hT : T₀ ≤ (K.prefixAt k).time j.succ)
      (hl : j.succ ≤ Fin.last (K.prefixAt k).eventCount)
      (A : BackwardPointTrace (K.prefixAt k).toHistory j.succ
        (Fin.last (K.prefixAt k).eventCount) hl y)
      (b : ((K.prefixAt k).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((K.prefixLateRecords_P6N k records j hT).static b).window x ∧
        ‖x.val‖ < Dcap + 1 ∧
        t - (K.prefixAt k).time j.succ ≤
          θ * (((K.prefixLateRecords_P6N k records j hT).static b).neck.scale)⁻¹ := by
  rintro ⟨j, hT, hl, A, b, x, h1, h2, h3⟩
  exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ k.isLt) j, hT,
    Fin.le_iff_val_le_val.mpr (by
      change j.val + 1 ≤ k.val
      exact j.isLt),
    K.backwardPointTraceOfPrefix k A, b, x, h1, h2, h3⟩

/-- consumer：K 层 late `hcan` 与 `¬ CapWindowPoint` 展开形一起搬到 `K.prefixAt k`（= SLT 窗口版在 prefix
上要的 records 侧两前提）。 -/
example (k : Fin (K.eventCount + 1)) {p : CutoffParameters} {T₀ t Dcap θ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (y : (K.stage k).Carrier)
    (hnot : ¬ ∃ (j : Fin K.eventCount) (hT : T₀ ≤ K.time j.succ) (hl : j.succ ≤ k)
      (A : BackwardPointTrace K.toHistory j.succ k hl y)
      (b : (K.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - K.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) :
    (∀ i hi b, ((K.prefixLateRecords_P6N k records i hi).static b).hasCanonicalWindow) ∧
    ¬ ∃ (j : Fin (K.prefixAt k).eventCount) (hT : T₀ ≤ (K.prefixAt k).time j.succ)
      (hl : j.succ ≤ Fin.last (K.prefixAt k).eventCount)
      (A : BackwardPointTrace (K.prefixAt k).toHistory j.succ
        (Fin.last (K.prefixAt k).eventCount) hl y)
      (b : ((K.prefixAt k).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((K.prefixLateRecords_P6N k records j hT).static b).window x ∧
        ‖x.val‖ < Dcap + 1 ∧
        t - (K.prefixAt k).time j.succ ≤
          θ * (((K.prefixLateRecords_P6N k records j hT).static b).neck.scale)⁻¹ :=
  ⟨K.prefixLateRecords_hcan_P6N k records hcan,
    K.not_capWindowPoint_prefix_of_late_P6N k records y hnot⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
