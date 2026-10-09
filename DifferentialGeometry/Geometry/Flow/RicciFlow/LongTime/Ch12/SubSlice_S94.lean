import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TowerFamily_O28

/-!
# CH12-S94 G3: `sub86_3_S94`, the slice adapter for the traced-family output of `hsub86N`

`hsub86N_S94` (= `hsub86N_S74_shape`) produces its traced family in the slice's own tower history
`N := sliceTowerHistory_CX2 s` at `u = restrictTime_CX2 N cut (sliceTop_S8 s)` (`u = s.time`).
`sub86_3_S94` repackages that family as the `s.history`-form conclusion of the `hG2c` binder of
`hG2_of_kl82_kappa_O22` (via `tracedFamily_slice_of_tower_O28`): the left endpoint `a₁` of the tower
window is a time of `s.history` (it lies below `s.time`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem sub86_3_S94 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (s : RegularSlice F.observation) {x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier}
    {ρ τ K c : ℝ}
    (hwin : ∃ (a₁ : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
      (hat : a₁ ≤ restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s))
      (X' : BackwardPointTrace (sliceTowerHistory_CX2 s)
        ((sliceTowerHistory_CX2 s).activeStage a₁)
        ((sliceTowerHistory_CX2 s).activeStage
          (restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)))
        ((sliceTowerHistory_CX2 s).activeStage_mono hat)
        (restrictPoint_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s) x0)),
      (a₁ : ℝ) = c ∧
      ∀ (w : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon) (haw : a₁ ≤ w)
        (hwu : w ≤ restrictTime_CX2 (sliceTowerHistory_CX2 s) (sliceTowerTime_CX2 s) (sliceTop_S8 s)),
        (sliceTowerHistory_CX2 s).isTracedRegion w
          (X'.point ((sliceTowerHistory_CX2 s).activeStage w)
            ((sliceTowerHistory_CX2 s).activeStage_mono haw)
            ((sliceTowerHistory_CX2 s).activeStage_mono hwu)) ρ τ K) :
    ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
      (X : BackwardPointTrace s.history (s.history.activeStage a)
        (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
      (a : ℝ) = c ∧ ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u)
        (hut : u ≤ sliceTop_S8 s),
        s.history.isTracedRegion u (X.point (s.history.activeStage u)
          (s.history.activeStage_mono hau) (s.history.activeStage_mono hut)) ρ τ K := by
  obtain ⟨a₁, hat₁, X', hc, hfam⟩ := hwin
  have hle : (a₁ : ℝ) ≤ s.history.horizon := hat₁
  exact tracedFamily_slice_of_tower_O28 s (a := ⟨a₁.1, a₁.2.1, hle⟩) hat₁ hc X' hfam

end GC.LongTime.Ch12
