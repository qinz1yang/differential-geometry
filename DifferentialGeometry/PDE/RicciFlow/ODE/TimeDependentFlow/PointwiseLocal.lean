import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
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
Pointwise chart-local flow for a time-dependent vector field on a closed
manifold, in the chart-α-local form output by Picard–Lindelöf. For any base
point `x₀ : M` with chart `chartAt H x₀` of source containing `x₀`, given
* continuity of the time–space uncurry of `X` on `ℝ × M`, and
* a chart-Lipschitz bound: a positive horizon `L`, a positive chart radius
  `r`, and a non-negative Lipschitz constant `K` such that for each
  `t ∈ [0, L]`, the chart pushforward `X t ∘ (chartAt H x₀).symm` is
  `K`-Lipschitz on the open ball of radius `r` around `(chartAt H x₀) x₀` in
  the model space `E`,

there exist a positive time horizon `T`, a positive chart radius `r'`, and a
chart-coordinate flow `flow : E → ℝ → E` defined on the closed ball of radius
`r'` around `(chartAt H x₀) x₀` in `E`, with `flow y 0 = y` and the chart-
coordinate ODE
`HasDerivWithinAt (flow y) (X t ((chartAt H x₀).symm (I.symm (flow y t)))) [0,T] t`
for every `y` in that closed ball and every `t ∈ [0, T]`.

This is the chart-α-local specialisation of
`time_dependent_vf_chart_local_picard_with_lipschitz` to the chart at a single
base point `x₀`. The "pointwise" naming refers to the localisation at one
base point; pulling the chart-α-local flow back to a manifold flow on an
open neighborhood `U ⊆ M` of `x₀` requires the chart-α-pushforward
conventions and is performed in downstream gluing modules (`Glue.lean`,
`UniformExistence.lean`). Stating the result in chart-α coordinates here
avoids the chart-AT-y vs chart-α convention mismatch that would otherwise
arise when expressing the right-hand velocity at a moving manifold point.
-/
theorem time_dependent_vf_pointwise_local_flow
    (X : ℝ → ∀ x : M, TangentSpace I x) (x₀ : M)
    (hCont :
      ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)))
    (hLip : ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H x₀).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H x₀) x₀)) r)) :
    ∃ T : ℝ, 0 < T ∧ ∃ r' : ℝ, 0 < r' ∧
      ∃ flow : E → ℝ → E,
        (∀ y ∈ Metric.closedBall (I ((chartAt H x₀) x₀)) r',
          flow y 0 = y ∧
          ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivWithinAt (flow y)
              ((X t ((chartAt H x₀).symm (I.symm (flow y t)))) : E)
              (Set.Icc (0 : ℝ) T) t) := by
  obtain ⟨T, hT_pos, r', hr'_pos, flow, hflow⟩ :=
    time_dependent_vf_chart_local_picard_with_lipschitz X x₀ hCont hLip
  exact ⟨T, hT_pos, r', hr'_pos, flow, hflow⟩

end DifferentialGeometry.PDE.RicciFlow.ODE
