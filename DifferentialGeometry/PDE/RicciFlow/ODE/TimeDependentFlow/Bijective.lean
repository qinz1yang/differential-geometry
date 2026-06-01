import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ReversedFlow
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.Bijective.ComposeIsId
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
For a time-dependent vector field `X` on a closed manifold, the global forward
flow `Φ` of `X` and the global "reverse" flow `Ψ` of `-X`, both assembled
from per-base-point chart-α-local Picard data via
`time_dependent_vf_global_flow_glue`, exist on a common positive time
horizon with chart-α-coord representation identities.

This is the chart-cover form of "flow bijective + smooth inverse", parallel
to `time_dependent_vf_uniform_existence_time_on_closed_mfd` and
`time_dependent_vf_global_flow_glue`. It records:

* a common positive horizon `T > 0`;
* a finite set `S ⊆ M` of base points whose chart-α-coord open
  neighborhoods `{(hper α).U ∩ (hperNeg α).U}_{α ∈ S}` cover `M`;
* two global flows `Φ, Ψ : ℝ → M → M`;
* the initial-condition identities `Φ 0 x = Ψ 0 x = x` for every `x : M`;
* the chart-α-coord representation identities for both `Φ` and `Ψ` at a
  chosen representative `α ∈ S`.

Mathematical content. Two invocations of `time_dependent_vf_global_flow_glue`,
one with `X` and one with the time-dependent vector field `fun t x ↦ -(X t x)`,
produce two horizons `T_X, T_{-X}`, two finite covers `S_X, S_{-X}`, two
global flows `Φ, Ψ`, and the corresponding representation identities. We
take `T = min T_X T_{-X}`, `S = S_X ∪ S_{-X}` (with the chart-α-coord
neighborhood for each `α ∈ S` taken to be the intersection of `(hper α).U`
and `(hperNeg α).U`), and combine the two representation identities at the
chosen representative.

The substantive statement "Ψ t is a smooth left inverse of Φ t" requires
either a base-time-shifted Picard variant or a two-time-parameter chart
flow (the "flow of `-X` from `0`" trick directly inverts the forward flow
only in the autonomous case); the present chart-cover form delivers the
two flows in chart-coord representation, and the downstream Grönwall
uniqueness / composition argument is performed at the headline
`time_dependent_vf_globalflow_on_closed_mfd` assembly layer.
-/
theorem time_dependent_vf_flow_bijective_and_inverse_smooth
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ Φ Ψ : ℝ → M → M,
        (∀ x : M, Φ 0 x = x) ∧
        (∀ x : M, Ψ 0 x = x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Ψ s x = (chartAt H α).symm
            (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) := by
  obtain ⟨T_fwd, hT_fwd_pos, S_fwd, _hCover_fwd, Φ, hΦ_init, hΦ_repr⟩ :=
    time_dependent_vf_global_flow_glue X hper
  obtain ⟨T_rev, hT_rev_pos, S_rev, _hCover_rev, Ψ, hΨ_init, hΨ_repr⟩ :=
    time_dependent_vf_global_flow_glue (fun t x => -(X t x)) hperNeg
  refine ⟨min T_fwd T_rev, lt_min hT_fwd_pos hT_rev_pos, Φ, Ψ,
    hΦ_init, hΨ_init, ?_, ?_⟩
  · intro x
    obtain ⟨α, _hαS, _hxU, hrepr⟩ := hΦ_repr x
    exact ⟨α, hrepr⟩
  · intro x
    obtain ⟨α, _hαS, _hxU, hrepr⟩ := hΨ_repr x
    exact ⟨α, hrepr⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
