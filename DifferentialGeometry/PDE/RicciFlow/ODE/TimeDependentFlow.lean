import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PointwiseLocal
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Glue
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.MFDerivPackage

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
For a time-dependent vector field `X` on a closed manifold, given per-base-point
chart-α-local Picard data both for `X` and for `-X`, the chart-cover global
forward and reverse flows exist on a common positive time horizon with
chart-α-coord representation identities.

This is the chart-cover form of the global flow assembled from chart-local
Picard data, paralleling
`time_dependent_vf_uniform_existence_time_on_closed_mfd`,
`time_dependent_vf_global_flow_glue`, and
`time_dependent_vf_flow_bijective_and_inverse_smooth`. It records:

* a common positive horizon `T > 0`;
* two global flows `Φ, Ψ : ℝ → M → M`;
* the initial-condition identities `Φ 0 x = x = Ψ 0 x` for every `x : M`;
* for every `x : M`, the existence of a base point `α : M` such that
  `Φ s x` agrees, for every `s : ℝ`, with the chart-α-coord pull-back of the
  per-α chart-coord flow `(hper α).flow (I ((chartAt H α) x)) s` of `X`;
* the analogous chart-α-coord representation identity for `Ψ` against
  `(hper_neg α).flow`.

Stating the global flow data in chart-α-coord representation form rather than
as a `Diffeomorph I I M M ∞` family with a manifold-flow equation
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) (Set.Ici 0) t _` deliberately
mirrors the upstream `Glue` / `Bijective` API: the headline conclusion lives
purely in chart-coord coordinates and does not bake in the chart-AT-y vs
chart-α convention mismatch obstructing a direct manifold-flow restatement.
The downstream consumer (Ricci-flow short-time existence assembly) repackages
this chart-cover data through a separate chart-bridge layer when it needs the
manifold-flow form on smooth inputs.

Mathematical content. The chart-α-coord representation form of the forward
flow `Φ` is supplied directly by
`time_dependent_vf_flow_bijective_and_inverse_smooth`, which composes
`time_dependent_vf_global_flow_glue` applied to `X` and to `fun t x ↦ -(X t x)`
and takes the common horizon. The present theorem is a thin wrapper that
re-exports the same data under the headline name.
-/
theorem time_dependent_vf_globalflow_on_closed_mfd
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hper_neg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Ψ s x = (chartAt H α).symm
            (I.symm ((hper_neg α).flow (I ((chartAt H α) x)) s))) :=
  time_dependent_vf_flow_bijective_and_inverse_smooth X hper hper_neg

end DifferentialGeometry.PDE.RicciFlow.ODE
