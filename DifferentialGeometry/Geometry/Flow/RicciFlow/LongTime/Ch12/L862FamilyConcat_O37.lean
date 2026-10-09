import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862StepPieces_O37
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceConcat

/-!
# CH12-O37 G2b: backward extension of a traced family (plumbing of Sublemma 86.6, S3)

A traced family of `x` on `[a₁, top]` (trace `X`, a traced region at every `X(w)`) and a traced
family of the earlier point `X(a₁)` on `[a₂, a₁]` (trace `Y`) concatenate (`BackwardPointTrace.concat`)
to a traced family of `x` on `[a₂, top]`. In the uniform extension step of Sublemma 86.6 the second
family is supplied by a child at `(a₁, X(a₁), θ r)`; this is the `d ↦ d + c` step of the depth set.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

/-- Concatenation of traced families along the center trace. -/
theorem family_concat_O37 {H : ObservedHistory.{u}} {a₂ a₁ top : Icc (0 : ℝ) H.horizon}
    (ha : a₂ ≤ a₁) (hb : a₁ ≤ top) {x : (H.stageAt top).Carrier} {ρ τ K : ℝ}
    (X : BackwardPointTrace H (H.activeStage a₁) (H.activeStage top) (H.activeStage_mono hb) x)
    (hX : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a₁ ≤ w) (hwt : w ≤ top),
      H.isTracedRegion w (X.point (H.activeStage w) (H.activeStage_mono haw)
        (H.activeStage_mono hwt)) ρ τ K)
    (Y : BackwardPointTrace H (H.activeStage a₂) (H.activeStage a₁) (H.activeStage_mono ha)
      (X.point (H.activeStage a₁) le_rfl (H.activeStage_mono hb)))
    (hY : ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a₂ ≤ w) (hwa : w ≤ a₁),
      H.isTracedRegion w (Y.point (H.activeStage w) (H.activeStage_mono haw)
        (H.activeStage_mono hwa)) ρ τ K) :
    ∃ Z : BackwardPointTrace H (H.activeStage a₂) (H.activeStage top)
        (H.activeStage_mono (ha.trans hb)) x,
      ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a₂ ≤ w) (hwt : w ≤ top),
        H.isTracedRegion w (Z.point (H.activeStage w) (H.activeStage_mono haw)
          (H.activeStage_mono hwt)) ρ τ K := by
  refine ⟨X.concat Y, fun w haw hwt => ?_⟩
  by_cases hw : w ≤ a₁
  · have he : (X.concat Y).point (H.activeStage w) (H.activeStage_mono haw)
        (H.activeStage_mono hwt) =
        Y.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hw) :=
      BackwardPointTrace.concat_point_of_le X Y _ _ _ (H.activeStage_mono hw)
    rw [he]
    exact hY w haw hw
  · have hw' : a₁ ≤ w := le_of_lt (lt_of_not_ge hw)
    have he : (X.concat Y).point (H.activeStage w) (H.activeStage_mono haw)
        (H.activeStage_mono hwt) =
        X.point (H.activeStage w) (H.activeStage_mono hw') (H.activeStage_mono hwt) :=
      BackwardPointTrace.concat_point_of_ge X Y _ _ _ (H.activeStage_mono hw')
    rw [he]
    exact hX w hw' hwt

end GC.LongTime.Ch12
