import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65

set_option autoImplicit false

/-!
# CH12-S93 / G3a: the HEq clause at `r = t` of hWA (stage identification bookkeeping)

With `J p := cast (postStage_eq_stage_active_CPD2 …) (f p)` (transport of `f` to the active stage of `t`) and a
lift `φ` with `backwardSurvivorMap first last (φ p) = J p` at `first = activeStage t`, the survivor image of `φ p`
at the active stage of `t` is `HEq` to `f p`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

theorem heq_start_S93 (n : ℕ) (τ : Icc (0 : ℝ) (F.tower.history n).horizon) {X : Type u}
    (f : X → (postStage F.observation (τ : ℝ)).Carrier)
    (last : Fin ((F.tower.history n).eventCount + 1))
    (ordered : (F.tower.history n).toHistory.activeStage τ ≤ last)
    (φ : X → (F.tower.history n).toHistory.backwardSurvivorDomain
      ((F.tower.history n).toHistory.activeStage τ) last ordered) (p : X)
    (hφ : (F.tower.history n).toHistory.backwardSurvivorMap
        ((F.tower.history n).toHistory.activeStage τ) last ordered
        ((F.tower.history n).toHistory.activeStage τ) le_rfl ordered (φ p) =
      cast (congrArg OrientedThreeStage.Carrier
        (postStage_eq_stage_active_CPD2 F.observation n τ)) (f p))
    (hf : (F.tower.history n).toHistory.activeStage τ ≤
      (F.tower.history n).toHistory.activeStage τ)
    (hl : (F.tower.history n).toHistory.activeStage τ ≤ last) :
    HEq ((F.tower.history n).toHistory.backwardSurvivorMap
      ((F.tower.history n).toHistory.activeStage τ) last ordered
      ((F.tower.history n).toHistory.activeStage τ) hf hl (φ p)) (f p) :=
  (heq_of_eq hφ).trans (cast_heq _ _)

end GC.LongTime.Ch12
