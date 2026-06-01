import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Geometry.Manifold.MFDeriv.Basic
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
Global manifold flow assembled from chart-α-coord per-base-point Picard data,
in chart-cover form (parallel to
`time_dependent_vf_uniform_existence_time_on_closed_mfd`).

Given per-α chart-α-coord local Picard data `hper α : ChartLocalPicardData X α`
for every base point `α : M`, this theorem builds a single global flow
`Φ : ℝ → M → M` by:

* extracting a uniform horizon `T > 0` and a finite cover `S ⊆ M` whose
  chart-α-coord open neighborhoods `{(hper α).U}_{α ∈ S}` cover `M`
  (via `time_dependent_vf_uniform_existence_time_on_closed_mfd`);
* choosing, for each `x : M`, a representative `αRep x ∈ S` with
  `x ∈ (hper (αRep x)).U` (`Classical.choose`);
* defining `Φ s x` as the pull-back through `(chartAt H (αRep x)).symm ∘ I.symm`
  of the chart-α-coord flow value
  `(hper (αRep x)).flow (I ((chartAt H (αRep x)) x)) s`.

The conclusion records, for every `x : M`,
* the initial-condition identity `Φ 0 x = x` (from `flow_spec.1` together
  with the chart left-inverse identity), and
* the chart-α-coord representation of `Φ`: there exists `α ∈ S` with
  `x ∈ (hper α).U` such that for every time `s : ℝ`, `Φ s x` agrees with
  the chart-coord pull-back of the per-α chart-coord flow:
  `Φ s x = (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))`.

Stating the chart-coord ODE in terms of the per-α chart-coord flow
(via this representation identity together with `flow_spec.2` on
`UniformExistence`) rather than as a `HasMFDerivWithinAt` on `M`
deliberately avoids the chart-AT-y vs chart-α convention mismatch that
obstructs a direct manifold-flow restatement; the headline
`time_dependent_vf_globalflow_on_closed_mfd` packages this data into a full
manifold-flow diffeomorphism via the downstream smoothness / bijectivity /
chart-change layers.

Mathematical content. The global flow `Φ` is concrete and well-typed; the
representation identity holds definitionally per `αRep x`. The
initial-condition `Φ 0 x = x` reduces to `flow_spec.1` evaluated at the
chart-coord image of `x` (which is in the chart-coord open ball by
membership of `x` in `(hper α).U`) together with the chart and `I`
left-inverse identities. Independence of the choice on chart overlaps
(well-definedness of a chart-AT-y form) would require a chart-Lipschitz
hypothesis on `X` to invoke Grönwall; it is not asserted here.
-/
theorem time_dependent_vf_global_flow_glue
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α) :
    ∃ T : ℝ, 0 < T ∧
      ∃ S : Finset M, (⋃ α ∈ S, (hper α).U) = (Set.univ : Set M) ∧
        ∃ Φ : ℝ → M → M,
          (∀ x : M, Φ 0 x = x) ∧
          ∀ x : M, ∃ α ∈ S, x ∈ (hper α).U ∧
            ∀ s : ℝ,
              Φ s x = (chartAt H α).symm
                (I.symm ((hper α).flow (I ((chartAt H α) x)) s)) := by
  obtain ⟨T, hT_pos, S, hCoverEq, flow, hflow⟩ :=
    time_dependent_vf_uniform_existence_time_on_closed_mfd X hper
  have hMem : ∀ x : M, ∃ α ∈ S, x ∈ (hper α).U := by
    intro x
    have hx : x ∈ (⋃ α ∈ S, (hper α).U) := by
      rw [hCoverEq]; exact Set.mem_univ x
    rcases Set.mem_iUnion₂.mp hx with ⟨α, hαS, hxU⟩
    exact ⟨α, hαS, hxU⟩
  classical
  let αRep : M → M := fun x => (hMem x).choose
  have hαRep_S : ∀ x : M, αRep x ∈ S := fun x => (hMem x).choose_spec.1
  have hαRep_U : ∀ x : M, x ∈ (hper (αRep x)).U :=
    fun x => (hMem x).choose_spec.2
  have hxChart_closedBall :
      ∀ x : M, I ((chartAt H (αRep x)) x) ∈
        Metric.closedBall (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
    intro x
    have hxU := hαRep_U x
    have hball : I ((chartAt H (αRep x)) x) ∈
        Metric.ball (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
      have : (chartAt H (αRep x)) x ∈
          I ⁻¹' Metric.ball (I ((chartAt H (αRep x)) (αRep x))) (hper (αRep x)).r := by
        unfold ChartLocalPicardData.U at hxU
        exact hxU.2
      exact this
    exact Metric.ball_subset_closedBall hball
  have hxChart_source : ∀ x : M, x ∈ (chartAt H (αRep x)).source := by
    intro x
    have hxU := hαRep_U x
    unfold ChartLocalPicardData.U at hxU
    exact hxU.1
  let Φ : ℝ → M → M := fun s x =>
    (chartAt H (αRep x)).symm
      (I.symm ((hper (αRep x)).flow (I ((chartAt H (αRep x)) x)) s))
  have hΦ_init : ∀ x : M, Φ 0 x = x := by
    intro x
    obtain ⟨hinit, _⟩ :=
      (hper (αRep x)).flow_spec (I ((chartAt H (αRep x)) x)) (hxChart_closedBall x)
    change (chartAt H (αRep x)).symm
        (I.symm ((hper (αRep x)).flow (I ((chartAt H (αRep x)) x)) 0)) = x
    rw [hinit]
    have hI_left : I.symm (I ((chartAt H (αRep x)) x)) = (chartAt H (αRep x)) x :=
      I.left_inv ((chartAt H (αRep x)) x)
    rw [hI_left]
    exact (chartAt H (αRep x)).left_inv (hxChart_source x)
  refine ⟨T, hT_pos, S, hCoverEq, Φ, hΦ_init, ?_⟩
  intro x
  refine ⟨αRep x, hαRep_S x, hαRep_U x, ?_⟩
  intro s
  rfl

end DifferentialGeometry.PDE.RicciFlow.ODE
