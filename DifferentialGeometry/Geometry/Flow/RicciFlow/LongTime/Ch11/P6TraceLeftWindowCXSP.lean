import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageLeftWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CrossingLeftWindowCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointCurvatureC11G

set_option autoImplicit false

/-!
# CX-SPINE G18：已有 trace pair 的真实跨 stage 左邻域

正 age 使用 actual closedPrefix 终端距离，birth 使用同一 trace 的 regular crossing
和仅当前 birth 时刻的 protected no-shortcut。输出保留 postmetric 顶点与严格 incoming 左窗，不制造 trace。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {p q : (H.stageAt t).Carrier}

/-- 同一完整时间窗上两条实际 trace 的切片距离，使用各时刻的 active-stage metric。 -/
def pairEDist_CXSP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t) : ℝ≥0∞ :=
  riemannianEDistOf (H.stageMetric (H.activeStage v) v)
    (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
    (B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))

private theorem pairEDist_eq_stage_CXSP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
    (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t)
    (hact : H.activeStage v = j) :
    A.pairEDist_CXSP (hat := hat) B v hav hvt =
      riemannianEDistOf (H.stageMetric j v) (A.point j hf hl) (B.point j hf hl) := by
  subst j
  rfl

/-- 受保护的实际 crossings 使任意严格 post 距离界向左延拓，允许顶点是 birth 或 horizon。 -/
theorem exists_left_pair_distance_window_CXSP
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) q)
    {params : CutoffParameters}
    (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params)
    (hOld : ∀ e : Fin H.eventCount,
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (hcan : ∀ e b, ((records e).static b).hasCanonicalWindow)
    (hacc : params.modelAccuracy ≤ 1 / 2)
    (hD : StandardCap.transitionEnd + 10 < params.modelRadius)
    (v : Icc (0 : ℝ) H.horizon) (hav : a < v) (hvt : v ≤ t)
    (hprot : ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
      (hl : e.succ ≤ H.activeStage t), H.time e.succ = (v : ℝ) → ∀ b,
      A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
          ((records e).static b).window ''
            {z : standardCapWindow params.modelRadius |
              ‖z.val‖ ≤ StandardCap.transitionEnd + 10})
    {X : ℝ≥0∞}
    (hpost : A.pairEDist_CXSP (hat := hat) B v hav.le hvt < X) :
    ∃ d ∈ Ico (a : ℝ) (v : ℝ),
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ t),
        d < (w : ℝ) → w < v → A.pairEDist_CXSP (hat := hat) B w haw hwt < X := by
  by_cases hage : H.time (H.activeStage v) < (v : ℝ)
  · obtain ⟨d, hd, hnear⟩ := H.exists_stage_left_window_CXSP v hage
      (A.point (H.activeStage v) (H.activeStage_mono hav.le) (H.activeStage_mono hvt))
      (B.point (H.activeStage v) (H.activeStage_mono hav.le) (H.activeStage_mono hvt)) hpost
    refine ⟨max (a : ℝ) d, ⟨le_max_left _ _, max_lt hav hd.2⟩, ?_⟩
    intro w haw hwt hdw hwv
    have hdw' : d < (w : ℝ) := (le_max_right _ _).trans_lt hdw
    have hact : H.activeStage w = H.activeStage v :=
      H.activeStage_eq_of_time_le_C11G w v (hd.1.trans hdw'.le) hwv.le
    rw [pairEDist_eq_stage_CXSP (hat := hat) A B w haw hwt _ _ _ hact]
    exact hnear w ⟨hdw', hwv⟩
  · have hbirth : H.time (H.activeStage v) = (v : ℝ) :=
      le_antisymm (H.activeStage_time_le v) (le_of_not_gt hage)
    have hnzero : H.activeStage v ≠ 0 := by
      intro hz
      have hvzero : (v : ℝ) = 0 := by simpa only [hz, H.time_zero] using hbirth.symm
      have hav' : (a : ℝ) < v := hav
      linarith [a.2.1]
    obtain ⟨e, he⟩ := Fin.exists_succ_eq_of_ne_zero hnzero
    have htime : H.time e.succ = (v : ℝ) := by rw [he]; exact hbirth
    have hf : H.activeStage a ≤ e.castSucc :=
      Fin.le_castSucc_iff.mpr (H.time_strictMono.lt_iff_lt.mp
        (((H.activeStage_time_le a).trans_lt hav).trans_eq htime.symm))
    have hl : e.succ ≤ H.activeStage t := he.le.trans (H.activeStage_mono hvt)
    have hpost' : riemannianEDistOf (H.stageMetric e.succ (H.time e.succ))
        (A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl)
        (B.point e.succ (hf.trans e.castSucc_lt_succ.le) hl) < X := by
      rw [htime]
      rwa [pairEDist_eq_stage_CXSP (hat := hat) A B v hav.le hvt e.succ _ _ he.symm] at hpost
    obtain ⟨d, hd, hnear⟩ := H.exists_left_window_of_protected_crossing_CXSP e
      (records e).static (hOld e) (hcan e) hacc hD (A.crossing e hf hl) (B.crossing e hf hl)
      (fun b => (hprot e hf hl htime b).1) (fun b => (hprot e hf hl htime b).2) hpost'
    have hdv : d < (v : ℝ) := hd.2.trans_eq htime
    refine ⟨max (a : ℝ) d, ⟨le_max_left _ _, max_lt hav hdv⟩, ?_⟩
    intro w haw hwt hdw hwv
    have hdw' : d < (w : ℝ) := (le_max_right _ _).trans_lt hdw
    have hwτ : (w : ℝ) < H.time e.succ := (show (w : ℝ) < v from hwv).trans_eq htime.symm
    have hact : H.activeStage w = e.castSucc :=
      H.activeStage_eq_castSucc_C11G e w (hd.1.trans hdw'.le) hwτ
    rw [pairEDist_eq_stage_CXSP (hat := hat) A B w haw hwt _ _ _ hact]
    exact hnear w ⟨hdw', hwτ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
