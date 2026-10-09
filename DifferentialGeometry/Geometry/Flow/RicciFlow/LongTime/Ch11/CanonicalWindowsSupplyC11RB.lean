import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SurgerySuppliesC11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CutoffRecordSplicingC11RB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.CutoffRecordModelRestrictionC11RB

set_option autoImplicit false

/-!
# S-CH11-REPROVE-B (G4)：S3 `CanonicalWindowsSupply_C11S` 的树内适配

S3 = `∀ n i b, ((records n i).static b).hasCanonicalWindow`（A12 profile 的 `canonical_windows`）。
astra 里它来自 `exists_surgery_with_spatial_control` 的 `hcanonical` 一支：每个 observation `n`
的 records `old n`（参数 `p n`）有 canonical window，`records n i := (old n i).diagonalParameters …`
的 `static` 与 `old n i` 的 `static` HEq（`diagonalParameters_preserves`），再用
`hasCanonicalWindow_of_family_heq` 传递。这里给出三个**通用**形（显式 binder，无新结构）：

* `canonicalWindowsSupply_of_heq_C11RB`：任意与 `old n i` 的 `static` HEq 的 `records`；
* `canonicalWindowsSupply_of_diagonal_C11RB`：`q = CutoffParameters.diagonal p`、
  `records n i = (old n i).diagonalParameters …`（astra 的 `hcanonical` 一支逐字）；
* `canonicalWindowsSupply_restrictModelWindow_C11RB`：model window 限制（G3）后 S3 保持；

以及 splicing 步（G1）的 `hasCanonicalCutoffRecords` 形：
`RetainedCoreHistory.hasCanonicalCutoffRecords_appendEvent_spliceAfter_C11RB`。
对 S3 的 W1 conjunct 来说：observation 层的 windows（`old`）由 G1 的 splicing 归纳 + 每步新
record 的 window 给出，本组只负责从 observation 层到 A12 的共同 `q` 上的 records。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set

namespace GC.LongTime.Ch11

universe u

/-- **S3 的 HEq 适配**：`records n i` 的 `static` 与有 canonical window 的 `old n i` 的 `static`
HEq，且静态模型参数一致，则 S3 成立。 -/
theorem canonicalWindowsSupply_of_heq_C11RB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (hfixed : ∀ n, q.fixed = (p n).fixed ∧ q.modelRadius = (p n).modelRadius ∧
      q.modelOrder = (p n).modelOrder ∧ q.modelAccuracy = (p n).modelAccuracy)
    (hbridge : ∀ n i, HEq (records n i).static (old n i).static)
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow) :
    CanonicalWindowsSupply_C11S records := fun n i =>
  MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
    rfl rfl rfl rfl HEq.rfl (hfixed n).1 (hfixed n).2.1 (hfixed n).2.2.1 (hfixed n).2.2.2
    (old n i).static (records n i).static (hbridge n i) (hwin n i)

/-- observation 层 records `old n`（参数 `p n`）在共同参数 `diagonal p` 上的 records
（astra `exists_surgery_with_spatial_control` 里的 `records`）。 -/
def diagonalRecords_C11RB {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (htime : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).toHistory.time i.succ ≤ (n : ℝ)) :
    CutoffRecords_C11S F (CutoffParameters.diagonal p) :=
  fun n i => (old n i).diagonalParameters (hstatic n) hcompat (htime n i)

/-- **S3 的 diagonal 适配**（astra `exists_surgery_with_spatial_control` 的 `hcanonical` 一支）：
`q = diagonal p`，`records = diagonalRecords_C11RB …`。 -/
theorem canonicalWindowsSupply_of_diagonal_C11RB {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters)
    (old : ∀ n (i : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory i (p n))
    (hwin : ∀ n i b, ((old n i).static b).hasCanonicalWindow)
    (hstatic : ∀ n, (p n).fixed = (p 0).fixed ∧ (p n).modelRadius = (p 0).modelRadius ∧
      (p n).modelOrder = (p 0).modelOrder ∧ (p n).modelAccuracy = (p 0).modelAccuracy ∧
      (p n).recenterConstant = (p 0).recenterConstant)
    (hcompat : ∀ m k : ℕ, m ≤ k → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p k).delta t ∧ (p m).neckRadius t = (p k).neckRadius t ∧
      (p m).protectedRadius t = (p k).protectedRadius t)
    (htime : ∀ n (i : Fin (F.tower.history n).eventCount),
      (F.tower.history n).toHistory.time i.succ ≤ (n : ℝ)) :
    CanonicalWindowsSupply_C11S (diagonalRecords_C11RB F p old hstatic hcompat htime) :=
  fun n i =>
  MetricCutCapEvent.PresentedStaticCap.hasCanonicalWindow_of_family_heq
    rfl rfl rfl rfl HEq.rfl (hstatic n).1.symm (hstatic n).2.1.symm (hstatic n).2.2.1.symm
    (hstatic n).2.2.2.1.symm (old n i).static
    ((old n i).diagonalParameters (hstatic n) hcompat (htime n i)).static
    ((old n i).diagonalParameters_preserves (hstatic n) hcompat (htime n i)).2.2.2.2 (hwin n i)

/-- model window 限制（G3）后 S3 保持：records 换成更粗的 static model `(D, m, ε)`，
窗口仍含 cap core（`transitionEnd < D + 1`）。 -/
theorem canonicalWindowsSupply_restrictModelWindow_C11RB {P : OrientedThreeStage.{u}}
    {g : P.Metric} {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : CutoffRecords_C11S F q) (hwin : CanonicalWindowsSupply_C11S records)
    {D ε : ℝ} {m : ℕ} (hD : 0 < D) (hDq : D ≤ q.modelRadius) (hm : m ≤ q.modelOrder)
    (hε : q.modelAccuracy ≤ ε)
    (hcap : DifferentialGeometry.PDE.RicciFlow.StandardCap.transitionEnd < D + 1) :
    CanonicalWindowsSupply_C11S (F := F)
      (q := q.withModelWindow_C11RB D m ε hD (q.modelAccuracy_pos.trans_le hε))
      (fun n i => (records n i).restrictModelWindow_C11RB (hwin n i) hD hDq hm hε) :=
  fun n i b =>
    (records n i).hasCanonicalWindow_restrictModelWindow_C11RB (hwin n i) hD hDq hm hε hcap b

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **S3 的 splicing 步**（`hasCanonicalCutoffRecords` 形）：已有 canonical records 的 history 追加
一个 event 后，在整个旧区间保持旧参数（`spliceAfter`），新 record 有 canonical window 与
`δ / ρ` 界，则追加后的 history 仍有 canonical records。tree 里原有的 `spliceAt` 形
（`hasCanonicalCutoffRecords_appendEvent`）只在单点 `s` 改参数；这里是 astra 用的 `spliceAfter` 形。 -/
theorem RetainedCoreHistory.hasCanonicalCutoffRecords_appendEvent_spliceAfter_C11RB
    {Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory.{u}) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hfuture : H.horizon < s) {p₀ q : CutoffParameters} {δ₀ ρ₀ : ℝ}
    (hH : H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀)
    (new : GeometricCutoffRecord (H.appendEvent hs E hinit).toHistory
      (Fin.last H.eventCount) q)
    (hstatic : q.fixed = p₀.fixed ∧ q.modelRadius = p₀.modelRadius ∧
      q.modelOrder = p₀.modelOrder ∧ q.modelAccuracy = p₀.modelAccuracy ∧
      q.recenterConstant = p₀.recenterConstant)
    (hnew : ∀ b, (new.static b).hasCanonicalWindow)
    (hδnew : q.delta s ≤ δ₀) (hρnew : q.neckRadius s ≤ ρ₀) :
    (H.appendEvent hs E hinit).hasCanonicalCutoffRecords p₀ δ₀ ρ₀ := by
  obtain ⟨p, old, hold⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δ₀ ρ₀).1 hH
  obtain ⟨R, hR, -⟩ :=
    H.exists_isCanonicalCutoffRecordFamily_appendEvent_spliceAfter_C11RB hs E hinit hfuture
      old hold new hstatic hnew hδnew hρnew
  exact ((H.appendEvent hs E hinit
    ).hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δ₀ ρ₀).2 ⟨_, R, hR⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
