import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Outer.BlockStepDefsC11W

set_option autoImplicit false

/-!
# O-CH11-OUTER (G4)：restart datum 的识别引理（R-C11-3 D-2）

`c_X = X.history.time last`、`s_X = X.native.time last`。由 state 自带的
`affine : AffineEventPrefix native history shift offset (Fin.last native.eventCount)`：
`c_X = s_X + X.shift`，full / native 最后 stage 相同，最后 stage 的初始度量 HEq。
于是 `BlockLookahead_C11W.nextClass` 的类型索引（native 最后 stage / 初始度量）就是 full history
最后一个事件后的 post-metric；旧光滑 overlap `[c_X, b_j]` 由 `finalMetric_heq` 识别。
`PhysicalExtension_C11W` 的 `shift_eq` 给出 `Y.shift = c_X`。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow

namespace GC.LongTime.Ch11

universe u

variable {pBase : CutoffParameters} {C : ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- restart 识别：`c_X = s_X + shift`，最后 stage 相同，最后初始度量 HEq。 -/
theorem restart_ident_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j) :
    X.history.time (Fin.last X.history.eventCount) =
        X.native.time (Fin.last X.native.eventCount) + X.shift ∧
      X.history.stage (Fin.last X.history.eventCount) =
        X.native.stage (Fin.last X.native.eventCount) ∧
      HEq (X.history.initialMetric (Fin.last X.history.eventCount))
        (X.native.initialMetric (Fin.last X.native.eventCount)) := by
  have hc := X.affine.count_eq
  have ht := X.affine.time_eq (Fin.last X.native.eventCount)
  have hs := X.affine.stage_eq (Fin.last X.native.eventCount)
  have hm := X.affine.initialMetric_heq (Fin.last X.native.eventCount)
  have e1 : (⟨X.offset + (Fin.last X.native.eventCount).val, by simp [hc]⟩ :
      Fin (X.history.eventCount + 1)) = Fin.last X.history.eventCount :=
    Fin.ext (by simp [hc])
  have e2 : (Fin.last X.native.eventCount).castLE (le_refl _) =
      Fin.last X.native.eventCount := Fin.ext rfl
  rw [e1, e2] at ht hs hm
  exact ⟨ht, hs, hm⟩

/-- 同一 block extension 下，`Y.shift` 是 `X` 的 restart 时刻 `c_X = s_X + X.shift`。 -/
theorem shift_eq_restart_C11W {j : ℕ} {X : BlockState_C11W pBase C P g j}
    {Y : BlockState_C11W pBase C P g (j + 1)} {ℓ : BlockLookahead_C11W X}
    {req : BlockRequest_C11W} {d : ℝ} (hPE : PhysicalExtension_C11W X Y ℓ req d) :
    Y.shift = X.native.time (Fin.last X.native.eventCount) + X.shift :=
  hPE.shift_eq.trans (restart_ident_C11W X).1

/-- restart 时刻不晚于块端点：`c_X ≤ b_j`（旧光滑 overlap `[c_X, b_j]` 非退化方向）。 -/
theorem restart_le_horizon_C11W {j : ℕ} (X : BlockState_C11W pBase C P g j) :
    X.history.time (Fin.last X.history.eventCount) ≤ preparedSpatialHorizon j := by
  have h := X.history.toHistory.time_le_horizon_at (Fin.last X.history.eventCount)
  have hE : X.history.toHistory.horizon = preparedSpatialHorizon j := X.horizon_eq
  rw [hE] at h
  exact h

example {j : ℕ} (X : BlockState_C11W pBase C P g j) :
    X.native.time (Fin.last X.native.eventCount) + X.shift ≤ preparedSpatialHorizon j := by
  rw [← (restart_ident_C11W X).1]
  exact restart_le_horizon_C11W X

end GC.LongTime.Ch11
