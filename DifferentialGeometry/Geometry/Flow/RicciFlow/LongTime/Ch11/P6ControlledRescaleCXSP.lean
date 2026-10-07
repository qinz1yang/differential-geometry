import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizeP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RmRescaleCXSP

set_option autoImplicit false

/-!
# CX-SPINE G5：实际 backward trace 的整史重标度

使用原 history 的同一 crossing 数据，在实际 rescaleTime / castRescale 端点上构造 trace。
曲率控制分别核对 stageMetric 与 crossed-terminal 两个部分；后者经真实 terminal open/metric
的 HEq 搬运，不能用 scalar 或单个 stage 的缩放代替。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem trace_transfer_point_CXSP {H : ObservedHistory.{u}}
    {f l f' l' : Fin (H.eventCount + 1)} (hf : f = f') (hl : l = l')
    {hle : f ≤ l} {hle' : f' ≤ l'} {x : (H.stage l).Carrier} {x' : (H.stage l').Carrier}
    (hx : HEq x x') (A : BackwardPointTrace H f l hle x) (j : Fin (H.eventCount + 1))
    (hfj : f ≤ j) (hjl : j ≤ l) (hfj' : f' ≤ j) (hjl' : j ≤ l') :
    (trace_transfer_P6X (Hh := H) hf hl (hle' := hle') hx A).point j hfj' hjl' =
      A.point j hfj hjl := by
  subst hf
  subst hl
  obtain rfl := eq_of_heq hx
  rfl

private theorem trace_point_heq_CXSP {H : ObservedHistory.{u}}
    {f l : Fin (H.eventCount + 1)} {hle : f ≤ l} {x : (H.stage l).Carrier}
    (A : BackwardPointTrace H f l hle x) {i j : Fin (H.eventCount + 1)} (hij : i = j)
    (hfi : f ≤ i) (hil : i ≤ l) (hfj : f ≤ j) (hjl : j ≤ l) :
    HEq (A.point i hfi hil) (A.point j hfj hjl) := by
  subst hij
  rfl

private theorem subtype_heq_of_val_eq_CXSP {M : Type*} [TopologicalSpace M]
    {U V : TopologicalSpace.Opens M} (hUV : U = V) (x : U) (y : V)
    (hxy : x.val = y.val) : HEq x y := by
  subst hUV
  exact heq_of_eq (Subtype.ext hxy)

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- 同一实际 trace 在重标度 history 上，首末时刻与端点均经既有 canonical maps 搬运。 -/
def rescaleTrace_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon} (hat : a ≤ t)
    {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p) :
    BackwardPointTrace (H.rescale_P6N c hc).toHistory
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a))
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc hat))
      (H.castRescale_P6X hc t p) :=
  trace_transfer_P6X (Hh := (H.rescale_P6N c hc).toHistory)
    (H.activeStage_rescaleTime_P6X hc a).symm
    (H.activeStage_rescaleTime_P6X hc t).symm (H.heq_castRescale_P6X hc t p).symm
    (H.traceToRescale_P6N c hc A)

private theorem rescaleTrace_point_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p) (j : Fin (H.eventCount + 1))
    (hf : H.toHistory.activeStage a ≤ j) (hl : j ≤ H.toHistory.activeStage t)
    (hf' : (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a) ≤ j)
    (hl' : j ≤ (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t)) :
    (H.rescaleTrace_CXSP hc hat A).point j hf' hl' = A.point j hf hl := by
  exact trace_transfer_point_CXSP (H := (H.rescale_P6N c hc).toHistory)
    (H.activeStage_rescaleTime_P6X hc a).symm
    (H.activeStage_rescaleTime_P6X hc t).symm (H.heq_castRescale_P6X hc t p).symm
    (H.traceToRescale_P6N c hc A) j hf hl hf' hl'

private theorem rescaleTrace_point_heq_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p)
    {i j : Fin (H.eventCount + 1)} (hij : i = j)
    (hf : H.toHistory.activeStage a ≤ j) (hl : j ≤ H.toHistory.activeStage t)
    (hf' : (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a) ≤ i)
    (hl' : i ≤ (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t)) :
    HEq ((H.rescaleTrace_CXSP hc hat A).point i hf' hl') (A.point j hf hl) := by
  have hfi : H.toHistory.activeStage a ≤ i := by simpa only [hij] using hf
  have hil : i ≤ H.toHistory.activeStage t := by simpa only [hij] using hl
  rw [H.rescaleTrace_point_CXSP hc hat A i hfi hil hf' hl']
  exact trace_point_heq_CXSP (H := H.toHistory) A hij hfi hil hf hl

/-- 对应中间时刻的 trace 点正是原 trace 点的 canonical cast。 -/
theorem rescaleTrace_point_at_time_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p)
    (s : Icc (0 : ℝ) H.toHistory.horizon) (has : a ≤ s) (hst : s ≤ t) :
    (H.rescaleTrace_CXSP hc hat A).point
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc s))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc has))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc hst)) =
      H.castRescale_P6X hc s (A.point (H.toHistory.activeStage s)
        (H.toHistory.activeStage_mono has) (H.toHistory.activeStage_mono hst)) := by
  apply eq_of_heq
  exact (H.rescaleTrace_point_heq_CXSP hc hat A (H.activeStage_rescaleTime_P6X hc s)
    (H.toHistory.activeStage_mono has) (H.toHistory.activeStage_mono hst)
    ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc has))
    ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc hst))).trans
    (H.heq_castRescale_P6X hc s _).symm

/-- 沿实际对应端点，将重标度历史的 trace 搬回原历史。 -/
def unscaleTrace_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon} (hat : a ≤ t)
    {p : (H.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace (H.rescale_P6N c hc).toHistory
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a))
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc hat))
      (H.castRescale_P6X hc t p)) :
    BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p :=
  H.traceOfRescale_P6N c hc (trace_transfer_P6X (Hh := (H.rescale_P6N c hc).toHistory)
    (H.activeStage_rescaleTime_P6X hc a) (H.activeStage_rescaleTime_P6X hc t)
    (hle' := H.toHistory.activeStage_mono hat) (H.heq_castRescale_P6X hc t p) B)

/-- 搬回再重标度保留给定 trace；使用真实 backward trace 的唯一性。 -/
theorem rescaleTrace_unscaleTrace_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (B : BackwardPointTrace (H.rescale_P6N c hc).toHistory
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc a))
      ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc t))
      ((H.rescale_P6N c hc).toHistory.activeStage_mono (H.rescaleTime_mono_P6X hc hat))
      (H.castRescale_P6X hc t p)) :
    H.rescaleTrace_CXSP hc hat (H.unscaleTrace_CXSP hc hat B) = B :=
  Subsingleton.elim _ _

/-- 重标度再搬回也保留原 trace。 -/
theorem unscaleTrace_rescaleTrace_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p) :
    H.unscaleTrace_CXSP hc hat (H.rescaleTrace_CXSP hc hat A) = A :=
  Subsingleton.elim _ _

/-- 在实际对应时刻与 trace 点，完整四阶加权 stage 曲率控制严格不变。 -/
theorem rescaleTrace_stage_weight_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p) (r : ℝ)
    (s : Icc (0 : ℝ) H.toHistory.horizon) (has : a ≤ s) (hst : s ≤ t) :
    let H' := (H.rescale_P6N c hc).toHistory
    let s' := H.rescaleTime_P6X hc s
    let x' := (H.rescaleTrace_CXSP hc hat A).point (H'.activeStage s')
      (H'.activeStage_mono (H.rescaleTime_mono_P6X hc has))
      (H'.activeStage_mono (H.rescaleTime_mono_P6X hc hst))
    (r / Real.sqrt c) ^ 4 *
        normSq0S (H'.stageMetric (H'.activeStage s') s') x' 4
          (metricRm04At (H'.stageMetric (H'.activeStage s') s') x') =
      r ^ 4 * normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage s) s)
        (A.point (H.toHistory.activeStage s) (H.toHistory.activeStage_mono has)
          (H.toHistory.activeStage_mono hst)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage s) s)
          (A.point (H.toHistory.activeStage s) (H.toHistory.activeStage_mono has)
            (H.toHistory.activeStage_mono hst))) := by
  intro H' s' x'
  have hmetric : H'.stageMetric (H'.activeStage s') s' =
      scaleMetric c⁻¹ (inv_pos.mpr hc)
        (H.toHistory.stageMetric (H'.activeStage s') s) := by
    exact (H.rescale_P6N_stageMetric c hc (H'.activeStage s') s').trans
      (congrArg (fun v => scaleMetric c⁻¹ (inv_pos.mpr hc)
        (H.toHistory.stageMetric (H'.activeStage s') v)) (H.mul_rescaleTime_P6X hc s))
  have hx : HEq x'
      (A.point (H.toHistory.activeStage s) (H.toHistory.activeStage_mono has)
        (H.toHistory.activeStage_mono hst)) :=
    H.rescaleTrace_point_heq_CXSP hc hat A (H.activeStage_rescaleTime_P6X hc s)
      (H.toHistory.activeStage_mono has) (H.toHistory.activeStage_mono hst)
      (H'.activeStage_mono (H.rescaleTime_mono_P6X hc has))
      (H'.activeStage_mono (H.rescaleTime_mono_P6X hc hst))
  calc
    _ = r ^ 4 * normSq0S (H.toHistory.stageMetric (H'.activeStage s') s) x' 4
        (metricRm04At (H.toHistory.stageMetric (H'.activeStage s') s) x') := by
      rw [hmetric]
      exact weighted_rm_sq_scale_inv_CXSP _ c hc r x'
    _ = _ := carrier_congr_P6X (S := H.stage)
      (fun j z _ => r ^ 4 * normSq0S (H.toHistory.stageMetric j s) z 4
        (metricRm04At (H.toHistory.stageMetric j s) z))
      (H.activeStage_rescaleTime_P6X hc s) hx hx

/-- 每次 crossed terminal 的实际 limit metric 与同一 trace 点也保留加权 Rm 控制。 -/
theorem rescaleTrace_terminal_weight_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    (hat : a ≤ t) {p : (H.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p) (r : ℝ)
    (i : Fin H.eventCount) (hf : H.toHistory.activeStage a ≤ i.castSucc)
    (hl : i.succ ≤ H.toHistory.activeStage t) :
    let H' := (H.rescale_P6N c hc).toHistory
    let hf' := (H.activeStage_rescaleTime_P6X hc a).trans_le hf
    let hl' := hl.trans_eq (H.activeStage_rescaleTime_P6X hc t).symm
    let x' : (H'.event i).incoming.terminalRegularOpen :=
      ⟨(H.rescaleTrace_CXSP hc hat A).point i.castSucc hf' (i.castSucc_lt_succ.le.trans hl'),
        ((H.rescaleTrace_CXSP hc hat A).crossing i hf' hl').mem_terminalRegularRegion (H'.event i)⟩
    let x : (H.toHistory.event i).incoming.terminalRegularOpen :=
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion (H.toHistory.event i)⟩
    (r / Real.sqrt c) ^ 4 * normSq0S (H'.event i).terminal.metric x' 4
        (metricRm04At (H'.event i).terminal.metric x') =
      r ^ 4 * normSq0S (H.toHistory.event i).terminal.metric x 4
        (metricRm04At (H.toHistory.event i).terminal.metric x) := by
  intro H' hf' hl' x' x
  have hx : HEq x' x := subtype_heq_of_val_eq_CXSP
    ((H.toHistory.event i).incoming.rescale_terminalRegularOpen c hc) x' x
    (H.rescaleTrace_point_CXSP hc hat A i.castSucc hf (i.castSucc_lt_succ.le.trans hl)
      hf' (i.castSucc_lt_succ.le.trans hl'))
  exact (H.toHistory.event i).terminal.weighted_rm_sq_rescale_CXSP c hc r x' x hx

variable {H} in
/-- 完整 isRmControlled 的双向重标度，包括全部 stage 时刻与全部 crossed-terminal 项。 -/
theorem isRmControlled_rescaleTrace_iff_CXSP {a t : Icc (0 : ℝ) H.toHistory.horizon}
    {hat : a ≤ t} {p : (H.toHistory.stageAt t).Carrier}
    {A : BackwardPointTrace H.toHistory (H.toHistory.activeStage a) (H.toHistory.activeStage t)
      (H.toHistory.activeStage_mono hat) p} {r : ℝ} :
    (H.rescaleTrace_CXSP hc hat A).isRmControlled
      (hat := H.rescaleTime_mono_P6X hc hat) (r / Real.sqrt c) ↔
      A.isRmControlled (hat := hat) r := by
  constructor
  · intro hA
    constructor
    · intro s has hst
      exact (H.rescaleTrace_stage_weight_CXSP hc hat A r s has hst).symm.le.trans
        (hA.1 (H.rescaleTime_P6X hc s) (H.rescaleTime_mono_P6X hc has)
          (H.rescaleTime_mono_P6X hc hst))
    · intro i hf hl
      exact (H.rescaleTrace_terminal_weight_CXSP hc hat A r i hf hl).symm.le.trans
        (hA.2 i ((H.activeStage_rescaleTime_P6X hc a).trans_le hf)
          (hl.trans_eq (H.activeStage_rescaleTime_P6X hc t).symm))
  · intro hA
    constructor
    · intro s' has' hst'
      obtain ⟨s, rfl⟩ : ∃ s, H.rescaleTime_P6X hc s = s' :=
        ⟨H.unscaleTime_P6X hc s', H.rescale_unscaleTime_P6X hc s'⟩
      have has : a ≤ s := (div_le_div_iff_of_pos_right hc).mp
        (show (a : ℝ) / c ≤ (s : ℝ) / c from has')
      have hst : s ≤ t := (div_le_div_iff_of_pos_right hc).mp
        (show (s : ℝ) / c ≤ (t : ℝ) / c from hst')
      exact (H.rescaleTrace_stage_weight_CXSP hc hat A r s has hst).le.trans (hA.1 s has hst)
    · intro i hf' hl'
      have hf : H.toHistory.activeStage a ≤ i.castSucc :=
        (H.activeStage_rescaleTime_P6X hc a).symm.trans_le hf'
      have hl : i.succ ≤ H.toHistory.activeStage t :=
        hl'.trans_eq (H.activeStage_rescaleTime_P6X hc t)
      exact (H.rescaleTrace_terminal_weight_CXSP hc hat A r i hf hl).le.trans (hA.2 i hf hl)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
