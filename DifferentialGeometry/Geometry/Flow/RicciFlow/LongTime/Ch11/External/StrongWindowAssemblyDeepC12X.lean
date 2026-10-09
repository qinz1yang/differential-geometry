import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowAssemblyC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowDeepC12X

/-!
# `hwin` assembly, θ-parametrised deep backward necks (C12X, S16G G5)

Lead ruling on R1 (route β): the binder-v2 record hypothesis is the θ-parametrised deep backward
neck contract of S16H (`IncomingBackwardNeckDeep_C12X`, `StrongWindowDeepC12X`), for a fixed depth
factor `θ > 1`; main instance / producer contract `θ = 5/4` (ch8 produces it from the existing
depth-two history rows).  This file instantiates the generic `Deep` of
`StrongWindowAssemblyC12X` accordingly:

* `DeepBackwardNecks_C12X θ`: every cut neck `α` of every event `i` carries
  `IncomingBackwardNeckDeep_C12X H i (neck α) (nominalRadius α) θ`;
* `exists_hwinYoungDeep_theta_of_far_C12X`: for `1 < θ`, a far-early branch valid for every depth
  factor `θ' > 1` gives `∃ D₀ θ₀ Cu, HwinYoungDeep_C12X (DeepBackwardNecks_C12X θ) ε D₀ θ₀ Cu`;
* `exists_hwinYoungDeep_fiveQuarters_C12X`: the main instance `θ = 5/4`.

The far branch may choose its `δmax` depending on `θ` (it is quantified after `θ`): the consumer
`window_fits_of_depth_C12X` needs `1 ≤ θ R r²` with `R r² ≥ 1 − O(δ + η)`.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Route β record hypothesis with depth factor `θ`. -/
def DeepBackwardNecks_C12X (θ : ℝ) : RecordHyp_C12X.{u} :=
  fun H _ records => ∀ (i : Fin H.eventCount)
    (α : (H.toHistory.event i).transition.trace.tubes.Index),
    Nonempty (IncomingBackwardNeckDeep_C12X H.toHistory i ((records i).neck α)
      ((records i).nominalRadius ⟨α⟩) θ)

/-- **hwin existence (v2, θ-parametrised), conditional on the far-early branch.** -/
theorem exists_hwinYoungDeep_theta_of_far_C12X {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    {θ : ℝ} (hθ : 1 < θ)
    (hfar : ∀ θ' : ℝ, 1 < θ' → ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ < 1 →
      ∃ D₀ CS : ℝ, 0 < D₀ ∧ 1 ≤ CS ∧ HwinFar_C12X (DeepBackwardNecks_C12X.{u} θ') ε θ₀ D₀ CS) :
    ∃ D₀ θ₀ Cu : ℝ, 0 < D₀ ∧ 0 < θ₀ ∧ θ₀ < 1 ∧ 1 ≤ Cu ∧
      HwinYoungDeep_C12X (DeepBackwardNecks_C12X.{u} θ) ε D₀ θ₀ Cu :=
  exists_hwinYoungDeep_of_far_C12X hε hε' _ (hfar θ hθ)

/-- Main instance / producer contract: depth factor `θ = 5/4`. -/
theorem exists_hwinYoungDeep_fiveQuarters_C12X {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (hfar : ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ < 1 →
      ∃ D₀ CS : ℝ, 0 < D₀ ∧ 1 ≤ CS ∧
        HwinFar_C12X (DeepBackwardNecks_C12X.{u} (5 / 4)) ε θ₀ D₀ CS) :
    ∃ D₀ θ₀ Cu : ℝ, 0 < D₀ ∧ 0 < θ₀ ∧ θ₀ < 1 ∧ 1 ≤ Cu ∧
      HwinYoungDeep_C12X (DeepBackwardNecks_C12X.{u} (5 / 4)) ε D₀ θ₀ Cu :=
  exists_hwinYoungDeep_of_far_C12X hε hε' _ hfar

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
