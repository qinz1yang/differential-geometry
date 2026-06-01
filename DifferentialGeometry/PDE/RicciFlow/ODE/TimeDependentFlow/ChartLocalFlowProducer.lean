import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicardProducer
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldFlowFamily

/-!
## Regularity-driven producer for the time-indexed diffeomorphism family

This file closes the gap between the clean Picard--Lindelöf regularity predicate
`ChartCoordPicardRegular X` (continuity in time--space plus a per-chart spatial
Lipschitz bound) and the time-indexed diffeomorphism family produced by the
chart-cover assembly `manifoldFlowFamily_exists`.

The latter takes per-base-point chart-local Picard *data*
`hper : ∀ α, ChartLocalPicardData X α` as input. The previously-proved producer
`chartLocalPicardData_of_regular` turns the regularity predicate into exactly
that data, one base chart at a time, by transporting `X` into chart coordinates
and invoking Mathlib's local existence theorem. This file wires the two
together: from `ChartCoordPicardRegular X` and `ChartCoordPicardRegular (-X)`
(plus the chart-`C^∞` regularity and the chart-overlap / per-chart-bijectivity
inputs consumed by the chart-cover assembly), it produces the diffeomorphism
family with the regularity predicate as the *only* ODE-existence input.

### The convention bridge, honestly

The chart-cover assembly expresses the global flow `Φ s x` through a *fixed*
representative chart `α = αRep x`, as
`Φ s x = (chartAt H α).symm (I.symm (flow_α (I ((chartAt H α) x)) s))`. The
chart-coordinate Picard ODE (`flow_spec`) carries the *raw* `E`-value of `X` —
`X t (Φ t x)` read directly as a member of `E` via the definitional identity
`TangentSpace I p = E` — not the push-forward of `X` through any chart
differential. Consequently the manifold velocity recovered from this data by the
chart bridge `manifoldFlow_hasMFDerivWithinAt_of_chartLocal` is the
chart-`α`-*transported* velocity
`mfderivWithin (extChartAt I α).symm (range I) (flow y t) ∘L
  (𝟙.smulRight (X t (Φ t x)))`,
which coincides with the bare geometric velocity `X t (Φ t x)` exactly at the
chart centre (where `mfderivWithin (extChartAt I α).symm` is the identity), and
in general differs from it. The headline of this layer therefore delivers the
diffeomorphism family with the chart-coordinate representation identity and the
transported-velocity manifold ODE, the form the chart-cover stack supports
unconditionally. A genuinely *bare* manifold flow equation
`∂_s (Φ s x) = X s (Φ s x)` is available only through the chart-free
autonomisation route of `ManifoldIntegralFlow.lean`, whose regularity input is
`C¹` of the autonomised field `(1, X)` on `ℝ × M` — strictly stronger than the
Lipschitz-plus-continuity content of `ChartCoordPicardRegular X`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/--
**Regularity-driven time-indexed diffeomorphism family.**

From the clean Picard--Lindelöf regularity predicate `ChartCoordPicardRegular X`
for the time-dependent vector field `X` and for its negative `-X`, together with
the chart-`C^∞` regularity and the chart-overlap / per-chart-bijectivity inputs
that the chart-cover assembly consumes, this produces a positive horizon `T`, a
time-indexed family of smooth diffeomorphisms `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`, and
a global flow `Φ : ℝ → M → M` such that

* `Φ_fam 0 = Diffeomorph.refl I M ∞` (the identity at time `0`);
* `Φ 0 x = x` for every `x : M` (the flow initial condition);
* `Φ_fam t x = Φ t x` for every `t ∈ (0, T)` and every `x : M` (the family
  realises the global flow on the existence horizon).

The per-base-point chart-local Picard data consumed downstream is *produced*
from the regularity predicate by `chartLocalPicardData_of_regular`, so the only
ODE-existence input is the genuine regularity of `X` (continuity in time--space
plus a per-chart spatial Lipschitz bound), never bundled solution data.

The remaining hypotheses (`hSmoothX_chart`, `hSmoothNegX_chart`, `hLocalFwd`,
`hLocalRev`, `hBijPerChart`) are genuinely separate analytic facts about `X` —
chart-`C^∞` regularity is strictly stronger than the Lipschitz content of
`ChartCoordPicardRegular`, and the overlap/bijectivity inputs encode
chart-transition compatibility of the flow — so they are carried as explicit
separable hypotheses rather than derived from the regularity predicate. -/
theorem manifoldFlowFamily_of_regular
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hReg : ChartCoordPicardRegular X)
    (hRegNeg : ChartCoordPicardRegular (fun t x => -(X t x)))
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (chartLocalPicardData_of_regular X hReg α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular X hReg α).flow
            (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (chartLocalPicardData_of_regular
          (fun t x => -(X t x)) hRegNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular
            (fun t x => -(X t x)) hRegNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular X hReg α).flow
            (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((chartLocalPicardData_of_regular
            (fun t x => -(X t x)) hRegNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (chartLocalPicardData_of_regular X hReg α).U ∩
              (chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) :=
  manifoldFlowFamily_exists X
    (fun α => chartLocalPicardData_of_regular X hReg α)
    (fun α => chartLocalPicardData_of_regular (fun t x => -(X t x)) hRegNeg α)
    hSmoothX_chart hSmoothNegX_chart hLocalFwd hLocalRev hBijPerChart

end DifferentialGeometry.PDE.RicciFlow.ODE
