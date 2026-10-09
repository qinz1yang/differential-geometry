import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceGlueC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSplicePostCC12X

/-!
# Splice: the far-early branch, unconditional (C12X, S16 `hwin`; O-C12X-S16H G4e6)

* `exists_hwinFar_radial_C12X`: for `0 < ε < 1/11`, `1 < θ`, `0 < θ₀ < 1` there are `D₀ > 0`,
  `CS ≥ 1` with `HwinFar_C12X (RecordHypFar_C12X θ) ε θ₀ D₀ CS` (`hwinFar_of_splicePost_C12X`
  with the post-surgery closeness `RetainedCoreHistory.exists_splicePost_C12X` of S16J).
* `exists_hwinYoungDeep_theta_of_far_radial_C12X`: the S16G v2 window input `HwinYoungDeep_C12X`
  for the route-β′ record hypothesis `RecordHypFar_C12X θ` (main instance `θ = 5/4`).
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **Far-early branch** for the route-β′ record hypothesis. -/
theorem exists_hwinFar_radial_C12X {ε : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11) {θ : ℝ}
    (hθ : 1 < θ) {θ₀ : ℝ} (hθ₀ : θ₀ < 1) :
    ∃ D₀ CS : ℝ, 0 < D₀ ∧ 1 ≤ CS ∧ HwinFar_C12X (RecordHypFar_C12X.{u} θ) ε θ₀ D₀ CS :=
  hwinFar_of_splicePost_C12X hε hε11 hθ hθ₀ fun r _ hη _ hL =>
    RetainedCoreHistory.exists_splicePost_C12X hθ₀ r hη hL

/-- **hwin existence (v2) for `RecordHypFar_C12X θ`**, `1 < θ` (main instance `θ = 5/4`). -/
theorem exists_hwinYoungDeep_theta_of_far_radial_C12X {ε : ℝ} (hε : 0 < ε)
    (hε11 : ε < 1 / 11) {θ : ℝ} (hθ : 1 < θ) :
    ∃ D₀ θ₀ Cu : ℝ, 0 < D₀ ∧ 0 < θ₀ ∧ θ₀ < 1 ∧ 1 ≤ Cu ∧
      HwinYoungDeep_C12X (RecordHypFar_C12X.{u} θ) ε D₀ θ₀ Cu :=
  exists_hwinYoungDeep_of_far_C12X hε hε11 _ fun _ _ hθ₀ =>
    exists_hwinFar_radial_C12X hε hε11 hθ hθ₀

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
