import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalTransFS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HsepBridgeHSX
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvJ10HelpJP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.PrefixTransportC11G2

/-!
# FSUP W2-B'：final 截断帧 `E` 的 records / HI / `hfinX` / `hsepT` / final slab 导数界（`_FS`）

`P6DrvResJ10JP` 的 `eventPrefix` 件的 final 孪生：
* `finalE_FS`（abbrev）：`E := ((K.prefixAt last).extendAt … finalSlab …)`；
* `finalPrefixRecords_FS`：K 的 late records ⇒ `E` 的 late records（`geometricCutoffRecordOfPrefix` 后
  `GeometricCutoffRecord.extendHorizon`，同 `eventPrefixRecords_C11G2`）；`static` 逐点相等 / `hcan`；
* `inFixedHI_final_FS`：K 层 Pre841 native HI 形 ⇒ E 的同形；
* `hfinX_final_FS`：K 层基点到 seed 的 edist 有限 ⇒ E 帧同形；
* `hsepT_final_FS`：K 帧 `hsep`（T0K 供给）⇒ E 帧 `hsepT`；
* `finalSlab_derivativeBound_FS`：final slab 的导数界常数 / 阈值 / 终点搬运。
PROVED，无新前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u})

/-- final 截断 history `E`（时刻 `T ∈ (time last, horizon)`）。 -/
abbrev finalE_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) : RetainedCoreHistory.{u} :=
  (K.prefixAt (Fin.last K.eventCount)).extendAt (K.prefixAt_time_last _)
    ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl) (K.final_initial hfin) hT hTs

/-- **record adapter（final，`_FS`）**：K 的 `GeometricCutoffRecord`（事件 `castLE e`）⇒ `E` 的 record
（事件 `e`）。 -/
def finalPrefixRecord_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {p : CutoffParameters}
    (e : Fin (K.finalE_FS hfin hT hTs).toHistory.eventCount)
    (R : GeometricCutoffRecord K.toHistory
      (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) e) p) :
    GeometricCutoffRecord (K.finalE_FS hfin hT hTs).toHistory e p :=
  GeometricCutoffRecord.extendHorizon (H := K.prefixAt (Fin.last K.eventCount)) T hT.le
    (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).closedPrefix T hT hTs)
    (K.final_initial hfin) (K.geometricCutoffRecordOfPrefix (Fin.last K.eventCount) R)

/-- **late records 沿 final 截断帧（`_FS`）**。 -/
def finalPrefixRecords_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {p : CutoffParameters}
    {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p) :
    ∀ e : Fin (K.finalE_FS hfin hT hTs).toHistory.eventCount,
      T₀ ≤ (K.finalE_FS hfin hT hTs).toHistory.time e.succ →
      GeometricCutoffRecord (K.finalE_FS hfin hT hTs).toHistory e p :=
  fun e he => K.finalPrefixRecord_FS hfin hT hTs e
    (records (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) e) he)

/-- `hcan` 沿 final 截断帧原样。 -/
theorem finalPrefixRecords_hcan_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {p : CutoffParameters}
    {T₀ : ℝ}
    (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ → GeometricCutoffRecord K.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow) :
    ∀ (e : Fin (K.finalE_FS hfin hT hTs).toHistory.eventCount)
      (he : T₀ ≤ (K.finalE_FS hfin hT hTs).toHistory.time e.succ) b,
      (((K.finalPrefixRecords_FS hfin hT hTs records) e he).static b).hasCanonicalWindow :=
  fun e he b => hcan (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) e) he b

/-- **G1：pinching 沿 final 截断帧（`_FS`）**：K 层 Pre841 native 形 ⇒ `E` 的同形（对所有 `τ ≤ T`）。 -/
theorem inFixedHI_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon) {a₀ : ℝ}
    (hpin : ∀ (τ' : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (τ : Icc (0 : ℝ) (K.finalE_FS hfin hT hTs).toHistory.horizon)
    (x : ((K.finalE_FS hfin hT hTs).toHistory.stageAt τ).Carrier) :
    InFixedHamiltonIveyRegion ((K.finalE_FS hfin hT hTs).toHistory.stageMetric
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) τ) (a₀ + τ) x := by
  let τ' : Icc (0 : ℝ) K.toHistory.horizon := ⟨τ, τ.2.1, τ.2.2.trans hTs.le⟩
  have hAτ : @Eq (Fin (K.toHistory.eventCount + 1))
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) (K.toHistory.activeStage τ') :=
    K.activeStage_final_P6M hfin hT hTs τ τ' rfl
  have h := K.toHistory.inFixedHI_stage_C11G hpin τ'
    ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) hAτ.symm x
  have hmv : (K.finalE_FS hfin hT hTs).toHistory.stageMetric
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) τ =
      K.toHistory.stageMetric ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) τ :=
    K.stageMetric_final_P6M hfin hT hTs _ _
  rw [hmv]
  exact h

/-- **`hfinX` 搬运（final，`_FS`，PROVED）**：K 层基点到 seed 点的 edist 有限 ⇒ E 帧（`Tn^E = τ`）同形有限。 -/
theorem hfinX_final_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon) {T : ℝ}
    (hT : K.time (Fin.last K.eventCount) < T) (hTs : T < K.horizon)
    (E : ObservedHistory.{u}) (hE : E = (K.finalE_FS hfin hT hTs).toHistory)
    (τ : Icc (0 : ℝ) E.horizon) (τ' : Icc (0 : ℝ) K.toHistory.horizon) (hττ : (τ : ℝ) = τ')
    (yE : (E.stageAt τ).Carrier) (yK : (K.toHistory.stageAt τ').Carrier) (hy : HEq yE yK)
    (TnK aK : Icc (0 : ℝ) K.toHistory.horizon) (haTK : aK ≤ TnK) (hsTK : τ' ≤ TnK)
    (hasK : aK ≤ τ') (pTK : (K.toHistory.stageAt TnK).Carrier)
    (seedK : BackwardPointTrace K.toHistory (K.toHistory.activeStage aK)
      (K.toHistory.activeStage TnK) (K.toHistory.activeStage_mono haTK) pTK)
    (aE : Icc (0 : ℝ) E.horizon) (haTE : aE ≤ τ) (hsTE : τ ≤ τ) (hasE : aE ≤ τ)
    (pTE : (E.stageAt τ).Carrier)
    (seedE : BackwardPointTrace E (E.activeStage aE) (E.activeStage τ)
      (E.activeStage_mono haTE) pTE)
    (hseed : ∀ (v : Icc (0 : ℝ) E.horizon) (v' : Icc (0 : ℝ) K.toHistory.horizon),
      (v : ℝ) = v' →
      ∀ (h1 : E.activeStage aE ≤ E.activeStage v) (h2 : E.activeStage v ≤ E.activeStage τ)
        (h1' : K.toHistory.activeStage aK ≤ K.toHistory.activeStage v')
        (h2' : K.toHistory.activeStage v' ≤ K.toHistory.activeStage TnK),
        HEq (seedE.point (E.activeStage v) h1 h2)
          (seedK.point (K.toHistory.activeStage v') h1' h2'))
    (hfinK : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage τ') τ')
        (seedK.point (K.toHistory.activeStage τ') (K.toHistory.activeStage_mono hasK)
          (K.toHistory.activeStage_mono hsTK)) yK ≠ ⊤) :
    riemannianEDistOf (E.stageMetric (E.activeStage τ) τ)
        (seedE.point (E.activeStage τ) (E.activeStage_mono hasE) (E.activeStage_mono hsTE))
        yE ≠ ⊤ := by
  subst hE
  have hidxτ : @Eq (Fin (K.toHistory.eventCount + 1))
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) (K.toHistory.activeStage τ') :=
    K.activeStage_final_P6M hfin hT hTs τ τ' hττ
  have hmetτ : (K.finalE_FS hfin hT hTs).toHistory.stageMetric
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) τ' =
      K.toHistory.stageMetric ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) τ' :=
    K.stageMetric_final_P6M hfin hT hTs _ _
  have e2 := edist_congr_P6JA K.toHistory hidxτ τ' _ hmetτ
    (seedE.point ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ)
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage_mono hasE)
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage_mono hsTE)) yE _ yK
    (hseed τ τ' hττ _ _ (K.toHistory.activeStage_mono hasK)
      (K.toHistory.activeStage_mono hsTK)) hy
  have e3 := congrArg (fun w : ℝ => riemannianEDistOf
    ((K.finalE_FS hfin hT hTs).toHistory.stageMetric
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ) w)
    (seedE.point ((K.finalE_FS hfin hT hTs).toHistory.activeStage τ)
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage_mono hasE)
      ((K.finalE_FS hfin hT hTs).toHistory.activeStage_mono hsTE)) yE) hττ
  exact fun h => hfinK (e2.symm.trans (e3.symm.trans h))

/-- final slab 的导数界：`(Ctime, Q, 截断终点 min horizon Tmax)` ⇒ `(2 Ctime, 2 q)` 于 `T`
（`Q ≤ q`，`0 ≤ q`，`T ≤ horizon`，`T ≤ Tmax`）。 -/
theorem finalSlab_derivativeBound_FS (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {Ctime : ℝ≥0} {Q q T Tmax : ℝ} (hq : Q ≤ q) (hq0 : 0 ≤ q) (hT : T ≤ K.horizon)
    (hTm : T ≤ Tmax)
    (h : (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)).DerivativeBoundBefore Ctime Q
      (min K.horizon Tmax)) :
    (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)).DerivativeBoundBefore (2 * Ctime)
      (2 * q) T :=
  OrientedThreeStage.IncomingSlab.DerivativeBoundBefore.mono_JP _ h (by
      have : Ctime ≤ 2 * Ctime := by
        rw [two_mul]; exact le_self_add
      exact this) (by linarith) (le_min hT hTm)

end RetainedCoreHistory

namespace ObservedHistory

/-- **`hsepT` 桥（final，`_FS`，PROVED）**：K 帧 `hsep`（窗口内事件 `2·max(3/(1/100)², C·R) < scale`）⇒
E 帧 `hsepT`（`2·max(3/r², C·R) < scale`，records 取 `finalPrefixRecords_FS`）。 -/
theorem hsepT_final_FS {r : ℝ} (hr : 0 < r)
    (K : ℕ → RetainedCoreHistory.{u}) (tK : ℕ → ℝ)
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < tK n) (htK : ∀ n, tK n < (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (R : ℕ → ℝ) (hR1 : ∀ᶠ n in atTop, 1 ≤ R n)
    (ts : ∀ n, Icc (0 : ℝ)
      ((K n).finalE_FS ((htl n).trans (htK n)) (htl n) (htK n)).toHistory.horizon)
    (hσ : ∀ n, (ts n : ℝ) = σ n)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n))
    (hsepK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          ((recordsK n i hi).static b).neck.scale) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (e : Fin ((K n).finalE_FS ((htl n).trans (htK n)) (htl n) (htK n)).toHistory.eventCount)
        (he : T₀K n ≤ ((K n).finalE_FS ((htl n).trans (htK n)) (htl n) (htK n)).toHistory.time
          e.succ) b,
        (ts n : ℝ) - T / R n <
          ((K n).finalE_FS ((htl n).trans (htK n)) (htl n) (htK n)).toHistory.time e.succ →
        2 * max (3 / r ^ 2) (C * R n) <
          (((K n).finalPrefixRecords_FS ((htl n).trans (htK n)) (htl n) (htK n) (recordsK n) e
            he).static b).neck.scale := by
  intro T hT C hC
  filter_upwards [hsepK T hT (C + 3 / r ^ 2) (by positivity), hR1] with n hn hRn
  intro e he b hlt
  have hlt' : (σ n : ℝ) - T / R n <
      (K n).time (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) e).succ := by
    rw [← hσ n]
    exact hlt
  exact (two_max_r_le_HSX hr hC hRn).trans_lt
    (hn (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) e) he b hlt')

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
