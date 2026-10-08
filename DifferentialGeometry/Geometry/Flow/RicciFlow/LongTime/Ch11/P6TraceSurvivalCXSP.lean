import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceProtectionCXSP

set_option autoImplicit false

/-!
# CX-SPINE G25：actual suffix 的出生标量界排除 trace 失效

不存在完整 trace 时，公开 cap capture 给一个实际 suffix 及其固定内区出生点。
同一 record 的 scale/2 下界与该 suffix 的出生标量≤2M 矛盾。
此处不要求失效 event 已被 suffix 穿越；出生标量仍须由消费端实际支付。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 同一 records 的 scale gap 与所有实际 suffix 的出生标量界生产完整 trace。 -/
theorem exists_trace_of_cap_scale_and_birth_bounds_CXSP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {params : CutoffParameters}
        (records : ∀ j, GeometricCutoffRecord H j params),
        params.modelAccuracy ≤ ε₀ → 2 ≤ params.modelOrder →
        (∀ j b, ((records j).static b).hasCanonicalWindow) →
        StandardCap.transitionEnd < params.modelRadius →
        ∀ {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
          (x : (H.stage last).Carrier) (M : ℝ),
        (∀ (j : Fin H.eventCount), first ≤ j.castSucc → j.succ ≤ last →
          ∀ b, 4 * M < ((records j).static b).neck.scale) →
        (∀ (j : Fin H.eventCount), first ≤ j.castSucc → ∀ hl : j.succ ≤ last,
          ∀ B : BackwardPointTrace H j.succ last hl x,
            metricScalarAt (H.stageMetric j.succ (H.time j.succ))
              (B.point j.succ le_rfl hl) ≤ 2 * M) →
        Nonempty (BackwardPointTrace H first last hle x) := by
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H params records hacc hord hcan hrad first last hle x M hscale hbound
  by_contra hnone
  have hempty : IsEmpty (BackwardPointTrace H first last hle x) := not_nonempty_iff.mp hnone
  obtain ⟨j, hf, hl, B, b, _z, z, _hno, _hcap, hnorm, hpoint⟩ :=
    H.exists_cap_capture records hcan hle x hempty
  have hR := hbound j hf hl B
  rw [H.stageMetric_succ_time_C11G, hpoint] at hR
  have hRlow := hlow (H.event j) hacc hord ((records j).static b) (hcan j b) z
    (hnorm.trans_lt hrad)
  linarith [hscale j hf hl b]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
