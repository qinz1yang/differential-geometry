import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SupplyRescaleP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotLocalP6HN

/-!
# 前缀 Dt 的 final 对应（tower 帧，阈值在 `Tn`；O-CH11-G9SHIFT G8，后缀 `_G9S`）

HNOT G5 `prefixDt_rescale_seq_P6HN`（event 中心）的 final 中心孪生：`TimeDerivativeSupply_C11E` 的 final 子句
（`hTD.2`）+ `ρ` 反单调 ⇒ 原尺度 `EventSlabsDerivative C (ρ(t)²)⁻¹ (Fin.last)` 与 final slab
`DerivativeBoundBefore`；重标度经 `eventSlabsDerivative_rescale_P6X3` /
`derivativeBoundBefore_rescale_P6X3`（final slab 的 `restrictIncoming` 与 `rescale` 可交换，`rfl`）；
阈值单调到 `max (n+1) ρ̂(Tn)⁻²`（同 `hpre_Tn_G9S`）。结论 = final G9″ 的 `hpre1 / hpre2` 槽。
无新分析、无新 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 原尺度 final 前缀 Dt（`_G9S`，PROVED）：观测时刻 `t > time last`、`t < horizon`。 -/
theorem prefixDt_final_G9S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {C : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius C)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (m : ℕ)
    (h0 : (F.tower.history m).time (Fin.last (F.tower.history m).eventCount) <
      (F.tower.history m).horizon) {t : ℝ}
    (htl : (F.tower.history m).time (Fin.last (F.tower.history m).eventCount) < t)
    (htK : t < (F.tower.history m).horizon) :
    (F.tower.history m).EventSlabsDerivative C ((q.neckRadius t ^ 2)⁻¹)
        (Fin.last (F.tower.history m).eventCount) ∧
      (((F.tower.history m).finalSlab h0).restrictIncoming le_rfl h0 le_rfl).DerivativeBoundBefore
        C ((q.neckRadius t ^ 2)⁻¹) t := by
  constructor
  · intro j' hj' y v hv hR
    have hle : j'.succ ≤ Fin.last (F.tower.history m).eventCount :=
      Fin.castSucc_lt_iff_succ_le.mp hj'
    have hv0 : 0 ≤ v :=
      ((F.tower.history m).toHistory.time_nonneg j'.castSucc).trans hv.1.le
    have hvt : v ≤ t :=
      (hv.2.le.trans ((F.tower.history m).time_strictMono.monotone hle)).trans htl.le
    exact hTD.1 m j' y v hv ((inv_sq_neckRadius_le_P6HN hanti hv0 hvt).trans_lt hR)
  · intro y v hv hR
    have hv0 : 0 ≤ v :=
      ((F.tower.history m).toHistory.time_nonneg (Fin.last _)).trans hv.1.le
    exact hTD.2 m h0 y v ⟨hv.1, hv.2.trans htK⟩
      ((inv_sq_neckRadius_le_P6HN hanti hv0 hv.2.le).trans_lt hR)

/-- **前缀 Dt，K 帧 final 中心，阈值在 `Tn`（`_G9S`，PROVED）**：`K n = (F.tower.history (ind n)).rescale_P6N
(c n)`，观测时刻 `t n ≤ Tn n` 落 final slab；`ρs n := fun _ => ρ̂(Tn n)` 处的 `hpre1 / hpre2`。 -/
theorem hpre_Tn_final_G9S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {Ctime : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {t : ℕ → ℝ}
    (hfin : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time
      (Fin.last ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount) <
      ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).horizon)
    (htl : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time
      (Fin.last ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount) < t n)
    (htK : ∀ n, t n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).horizon)
    (Tn : ℕ → ℝ) (htT : ∀ n, t n ≤ Tn n) :
    (∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).EventSlabsDerivative Ctime
        (max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
        (Fin.last ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)) ∧
    (∀ n, ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).finalSlab
        (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).DerivativeBoundBefore Ctime
        (max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (t n)) := by
  have hctl : ∀ n, (F.tower.history (ind n)).time (Fin.last (F.tower.history (ind n)).eventCount) <
      c n * t n := fun n => by
    have h := htl n
    change (F.tower.history (ind n)).time (Fin.last (F.tower.history (ind n)).eventCount) / c n <
      t n at h
    rwa [div_lt_iff₀ (hc n), mul_comm] at h
  have hctK : ∀ n, c n * t n < (F.tower.history (ind n)).horizon := fun n => by
    have h := htK n
    change t n < (F.tower.history (ind n)).horizon / c n at h
    rwa [lt_div_iff₀ (hc n), mul_comm] at h
  have h0 : ∀ n, (F.tower.history (ind n)).time (Fin.last (F.tower.history (ind n)).eventCount) <
      (F.tower.history (ind n)).horizon := fun n => (hctl n).trans (hctK n)
  have hle : ∀ n, c n * (q.neckRadius (c n * t n) ^ 2)⁻¹ ≤
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n => by
    have ht0 : 0 ≤ t n := by
      have := (hctl n).trans_le' ((F.tower.history (ind n)).toHistory.time_nonneg
        (Fin.last _))
      by_contra hneg
      push Not at hneg
      nlinarith [hc n, this]
    have heq : ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ =
        c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹ := by
      change ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ = _
      rw [div_pow, Real.sq_sqrt (hc n).le, inv_div, div_eq_mul_inv]
    rw [heq]
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left (inv_sq_neckRadius_le_P6HN hanti
      (mul_nonneg (hc n).le ht0) (mul_le_mul_of_nonneg_left (htT n) (hc n).le)) (hc n).le
  refine ⟨fun n e he => ?_, fun n => ?_⟩
  · obtain ⟨h1, -⟩ := prefixDt_final_G9S hTD hanti (ind n) (h0 n) (hctl n) (hctK n)
    exact derivativeBoundBefore_mono_qcan_P6SN _ (hle n)
      (((F.tower.history (ind n)).eventSlabsDerivative_rescale_P6X3 (hc n) h1) e he)
  · obtain ⟨-, h2⟩ := prefixDt_final_G9S hTD hanti (ind n) (h0 n) (hctl n) (hctK n)
    have h := (((F.tower.history (ind n)).finalSlab (h0 n)).restrictIncoming le_rfl (h0 n)
      le_rfl).derivativeBoundBefore_rescale_P6X3 (hc n) h2
    rw [mul_div_cancel_left₀ _ (hc n).ne'] at h
    exact derivativeBoundBefore_mono_qcan_P6SN _ (hle n) h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
