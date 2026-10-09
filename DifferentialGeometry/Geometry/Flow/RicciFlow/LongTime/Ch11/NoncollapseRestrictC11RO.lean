import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedRecordPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapse.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCutoffRecordFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryNoncollapsePrefixC11RO

set_option autoImplicit false

/-!
# O-CH11-REPROVE-O (G5)：noncollapse 与 records 沿 `restrict` 回拉（S6 链的 observation 环节）

astra 的整数层 observation（`SH/PreparedSpatialChain.lean:56–70`）把 state history（horizon > n）
限制到时刻 n：noncollapse 用 `noncollapsedBefore_restrict`，records 用 `restrictRecords`
（`ST/CutoffRecordHistoryRestriction/Basic.lean`，197 行；C11-B2-LANDED 记为 FAIL：`open private`
的 helper 用了 dot-notation `H.volume_lower_bound_of_stage_index`，环境里找不到）。这里按 reference
在树内重证（两个私有 helper 在本文件重写，后缀 `_C11RO`）：

* `RetainedCoreHistory.noncollapsedBefore_restrict_C11RO`：`H.NoncollapsedBefore κ ρ t₀`、`a ≤ t₀`
  ⇒ `(H.restrict a).NoncollapsedBefore κ ρ a`（slice 与 crossed-terminal 两类控制都保留）。
* `RetainedCoreHistory.restrictRecords_C11RO` /
  `isCanonicalCutoffRecordFamily_restrict_C11RO`：records 与 canonical family 沿 `restrict` 保留
  （G3 的输入在 observation 上仍成立）。
* 与 G1 合起来（新，reference 没有单独陈述）：`noncollapsedBefore_of_extension_C11RO`
  （extension ⇒ prefix，直到 prefix 的 horizon）与
  `noncollapsedBefore_iff_of_isPrefixOf_C11RO`（`t₀ = H.horizon` 时 prefix 与 extension 等价）。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem rmBound_of_stage_eq_C11RO {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (B : BackwardPointTrace K first last hle x) {m m' : Fin (K.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v r : ℝ)
    (h : r ^ 4 * normSq0S (K.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (K.stageMetric m' v) (B.point m' h1' h2')) ≤ 1) :
    r ^ 4 * normSq0S (K.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (K.stageMetric m v) (B.point m h1 h2)) ≤ 1 := by
  subst hm
  exact h

private theorem volumeLowerBound_of_stageIndex_C11RO {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t₀)
    (τ : Icc (0 : ℝ) H.toHistory.horizon) (hτ : (τ : ℝ) ≤ t₀)
    (last : Fin (H.eventCount + 1)) (hlast : H.toHistory.activeStage τ = last)
    (p : (H.stage last).Carrier) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (a : Icc (0 : ℝ) H.toHistory.horizon) (hat : a ≤ τ) (ha : (a : ℝ) = (τ : ℝ) - r ^ 2)
    (first : Fin (H.eventCount + 1)) (hfirst : first ≤ H.toHistory.activeStage a)
    (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric last τ) p r,
      ∃ B : BackwardPointTrace H.toHistory first last hf x,
        (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ τ),
          r ^ 4 * normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) (hfirst.trans (H.toHistory.activeStage_mono hav))
              ((H.toHistory.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              (B.point (H.toHistory.activeStage v)
                (hfirst.trans (H.toHistory.activeStage_mono hav))
                ((H.toHistory.activeStage_mono hvt).trans hlast.le))) ≤ 1) ∧
        ∀ (i : Fin H.eventCount) (hi : H.toHistory.activeStage a ≤ i.castSucc)
          (hil : i.succ ≤ last),
          let y : (H.toHistory.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc (hfirst.trans hi) (i.castSucc_lt_succ.le.trans hil),
              (B.crossing i (hfirst.trans hi) hil).mem_terminalRegularRegion
                (H.toHistory.event i)⟩;
          r ^ 4 * normSq0S (H.toHistory.event i).terminal.metric y 4
            (metricRm04At (H.toHistory.event i).terminal.metric y) ≤ 1) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage last).Carrier
        (H.toHistory.stageMetric last τ)
        (riemannianBallOf (H.toHistory.stageMetric last τ) p r) := by
  subst hlast
  refine hH τ p r hτ hrρ ⟨hr, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  exact ⟨B.restrictFirst hfirst (H.toHistory.activeStage_mono hat), hobs,
    fun i hi hil => hseam i hi hil⟩

private def incomingBackwardNeck_restrict_C11RO
    (a : Icc (0 : ℝ) H.horizon) {i : Fin (H.restrict a).eventCount}
    {δ r : ℝ} {m : ℕ}
    {neck : NormalizedNeck ((H.restrict a).toHistory.event i).terminal.metric δ m}
    (N : IncomingBackwardNeck (H.prefixAt (H.toHistory.activeStage a)).toHistory i neck r) :
    IncomingBackwardNeck (H.restrict a).toHistory i neck r := by
  cases N
  constructor <;> assumption

/-- records 沿 `restrict` 保留：只改 backward-history 的索引；nominal radius、accuracy、order、
neck、cap 不变。 -/
def restrictRecords_C11RO (a : Icc (0 : ℝ) H.horizon) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) :
    ∀ i : Fin (H.restrict a).eventCount, GeometricCutoffRecord (H.restrict a).toHistory i p :=
  fun i => { H.prefixRecords (H.toHistory.activeStage a) records i with
    backward := fun α => H.incomingBackwardNeck_restrict_C11RO a
      ((H.prefixRecords (H.toHistory.activeStage a) records i).backward α) }

/-- canonical cutoff record family 沿 `restrict` 保留（同 `p₀ δ₀ ρ₀`）。 -/
theorem isCanonicalCutoffRecordFamily_restrict_C11RO (a : Icc (0 : ℝ) H.horizon)
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records) :
    (H.restrict a).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ (H.restrictRecords_C11RO a records) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrec
  exact ⟨h1, h2, h3, h4, h5,
    fun i b => h6 (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i) b,
    fun i => h7 (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i),
    fun i => h8 (Fin.castLE (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt) i)⟩

private theorem noncollapsedBefore_restrict_aux_C11RO (a : Icc (0 : ℝ) H.horizon)
    {κ ρ t₀ : ℝ} (hH : H.NoncollapsedBefore κ ρ t₀) (ha : (a : ℝ) ≤ t₀)
    (τ : Icc (0 : ℝ) (H.toHistory.restrict a).horizon)
    (p : ((H.toHistory.restrict a).stageAt τ).Carrier) (r : ℝ)
    (hτ : (τ : ℝ) ≤ a) (hr : r ≤ ρ)
    (hball : (H.toHistory.restrict a).isParabolicallyRmControlledBall τ p r) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel ((H.toHistory.restrict a).stageAt τ).Carrier
        ((H.toHistory.restrict a).stageMetric ((H.toHistory.restrict a).activeStage τ) τ)
        (riemannianBallOf
          ((H.toHistory.restrict a).stageMetric ((H.toHistory.restrict a).activeStage τ) τ)
          p r) := by
  let L := H.toHistory.restrict a
  let cast : Fin (L.eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (H.toHistory.activeStage a).isLt))
  have hmetric (v : Icc (0 : ℝ) L.horizon) :
      L.stageMetric (L.activeStage v) v =
        H.toHistory.stageMetric (cast (L.activeStage v)) v :=
    eq_of_heq (H.toHistory.restrict_stageMetric a _ v (L.activeStage_mem v))
  obtain ⟨hr0, b, hbt, hb, htr⟩ := hball
  let τ' : Icc (0 : ℝ) H.horizon := ⟨τ, τ.2.1, τ.2.2.trans a.2.2⟩
  let b' : Icc (0 : ℝ) H.horizon := ⟨b, b.2.1, b.2.2.trans a.2.2⟩
  have hAτ : cast (L.activeStage τ) = H.toHistory.activeStage τ' :=
    H.toHistory.restrict_activeStage a τ
  have hAb : cast (L.activeStage b) = H.toHistory.activeStage b' :=
    H.toHistory.restrict_activeStage a b
  have hkb := L.activeStage_mono hbt
  rw [hmetric]
  refine volumeLowerBound_of_stageIndex_C11RO H hH τ' (hτ.trans ha)
    (cast (L.activeStage τ)) hAτ.symm p hr0 hr b'
    hbt hb (cast (L.activeStage b)) hAb.le
    (Fin.le_def.mpr (Fin.le_def.mp hkb)) ?_
  intro x hx
  have hx' : x ∈ riemannianBallOf (L.stageMetric (L.activeStage τ) τ) p r := by
    rw [hmetric]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨H.backwardPointTraceOfPrefix (H.toHistory.activeStage a)
    ⟨A.point, A.endpoint_eq, A.crossing⟩, ?_, ?_⟩
  · intro v hbv hvt
    have hva : (v : ℝ) ≤ (a : ℝ) := (show (v : ℝ) ≤ τ from hvt).trans τ.2.2
    let vL : Icc (0 : ℝ) L.horizon := ⟨v, v.2.1, hva⟩
    have hAv : cast (L.activeStage vL) = H.toHistory.activeStage v :=
      H.toHistory.restrict_activeStage a vL
    have hbv' : b ≤ vL := show (b : ℝ) ≤ v from hbv
    have hvt' : vL ≤ τ := show (v : ℝ) ≤ τ from hvt
    have h := hA1 vL hbv' hvt'
    rw [hmetric] at h
    refine rmBound_of_stage_eq_C11RO _ (m' := cast (L.activeStage vL))
      (m := H.toHistory.activeStage v) hAv _ _
      (Fin.le_def.mpr (Fin.le_def.mp (L.activeStage_mono hbv')))
      (Fin.le_def.mpr (Fin.le_def.mp (L.activeStage_mono hvt'))) v r ?_
    exact h
  · intro i hi hil
    have hil' : i.val + 1 ≤ (L.activeStage τ).val := Fin.le_def.mp hil
    have hk : (L.activeStage τ).val < (H.toHistory.activeStage a).val + 1 :=
      (L.activeStage τ).isLt
    have hi' : (L.activeStage b).val ≤ i.val := by
      change (cast (L.activeStage b)).val ≤ i.val
      rw [hAb]
      exact Fin.le_def.mp hi
    exact hA2 ⟨i.val, by
        change i.val < (H.toHistory.activeStage a).val
        omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr hil')

/-- **noncollapse 沿 `restrict` 回拉**：系数与半径不变；regular-slice 与 crossed-terminal 控制都保留。
（证明在 `H.toHistory.restrict a` 上做，事件是 `H.event (castLE i)` 本身，避开
`RetainedCoreEvent.transport` 的展开。） -/
theorem noncollapsedBefore_restrict_C11RO (a : Icc (0 : ℝ) H.horizon) {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t₀) (ha : (a : ℝ) ≤ t₀) :
    (H.restrict a).NoncollapsedBefore κ ρ a :=
  fun τ p r hτ hr hball =>
    noncollapsedBefore_restrict_aux_C11RO H a hH ha τ p r hτ hr hball

/-- **extension ⇒ prefix**（G1 的反方向）：`J` 上直到 `t₀ ≥ H.horizon` 的 noncollapse 推出 prefix `H`
在其整个 horizon 之前的 noncollapse（`J.restrict ⟨H.horizon, _⟩` 与 `H` same presentation）。 -/
theorem noncollapsedBefore_of_extension_C11RO {H J : RetainedCoreHistory.{u}}
    (hp : H.toHistory.IsPrefixOf J.toHistory) {κ ρ t₀ : ℝ} (ht : H.horizon ≤ t₀)
    (hnc : J.NoncollapsedBefore κ ρ t₀) : H.NoncollapsedBefore κ ρ H.horizon :=
  (noncollapsedBefore_iff_of_samePresentation_C11RO hp.presentation).mp
    (J.noncollapsedBefore_restrict_C11RO ⟨H.horizon, H.horizon_nonneg, hp.horizon_le⟩ hnc ht)

/-- prefix 与 extension 在 prefix 的 horizon 之前的 noncollapse 等价（G1 + G5）。 -/
theorem noncollapsedBefore_iff_of_isPrefixOf_C11RO {H J : RetainedCoreHistory.{u}}
    (hp : H.toHistory.IsPrefixOf J.toHistory) {κ ρ : ℝ} :
    H.NoncollapsedBefore κ ρ H.horizon ↔ J.NoncollapsedBefore κ ρ H.horizon :=
  ⟨noncollapsedBefore_of_isPrefixOf_C11RO hp le_rfl,
    noncollapsedBefore_of_extension_C11RO hp le_rfl⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
