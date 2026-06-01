import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.UniformExistence

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/--
Clean Picard–Lindelöf regularity hypothesis for a time-dependent vector field
`X` on a closed manifold, stated chart-by-chart in model-space coordinates.

`ChartCoordPicardRegular X` packages exactly the two ingredients Mathlib's
Picard–Lindelöf existence theorem consumes (no joint `C^∞` on `ℝ × M`, no
hidden ODE-solution data):

* **Continuity in time–space.** The uncurried field `(t, x) ↦ X t x` is
  continuous on `ℝ × M`. (Continuity uniform in `t` near `0` is what is
  actually used; continuity on the full product is the cleanest separable
  statement.)
* **Per-chart spatial Lipschitz bound.** For every base chart `α : M` there
  exist a positive time horizon `L`, a positive chart radius `r`, and a
  non-negative Lipschitz constant `K` such that, for each `t ∈ [0, L]`, the
  chart pushforward `y ↦ X t ((chartAt H α).symm (I.symm y))` is
  `K`-Lipschitz on the open ball of radius `r` around `I ((chartAt H α) α)`
  in the model space `E`.

This is strictly the regularity of `X`; it never mentions a solution flow.
The DeTurck specialisation supplies a witness of this predicate (from the
joint smoothness of the DeTurck vector field), and this file's producer turns
the predicate into `ChartLocalPicardData`. -/
def ChartCoordPicardRegular (X : ℝ → ∀ x : M, TangentSpace I x) : Prop :=
  ContinuousOn (Function.uncurry (fun t x => X t x)) (Set.univ : Set (ℝ × M)) ∧
    ∀ α : M, ∃ L K r : ℝ, 0 < L ∧ 0 < r ∧ 0 ≤ K ∧
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        LipschitzOnWith (Real.toNNReal K)
          (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
          (Metric.ball (I ((chartAt H α) α)) r)

/--
**Generic chart-local Picard-data producer.**

From a time-dependent vector field `X` that is Picard–Lindelöf regular
(`ChartCoordPicardRegular X`: continuous in time–space, spatially Lipschitz in
each chart), produce, for each base chart `α : M`, the bundled
`ChartLocalPicardData X α`.

The construction transports `X` into chart-`α` coordinates and invokes
Mathlib's local existence theorem
`IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt`
(via the chart-coordinate Picard theorem
`time_dependent_vf_chart_local_picard_with_lipschitz`). The resulting
chart-coordinate flow `flow : E → ℝ → E`, positive horizon `T`, and positive
radius `r'` are repackaged into the `ChartLocalPicardData` structure: the
`flow_spec` field is exactly the initial condition `flow y 0 = y` together
with the chart-coordinate ODE
`HasDerivWithinAt (flow y) (X t ((chartAt H α).symm (I.symm (flow y t)))) [0,T] t`
on the closed ball of radius `r'`, which is precisely the conclusion of the
local existence theorem.

This is the producer that `time_dependent_vf_flow_diffeomorph_on_closed_manifold`
takes as the hypothesis `hper : ∀ α, ChartLocalPicardData X α`; supplying it via
this theorem replaces that hypothesis by the genuine regularity of `X`. -/
noncomputable def chartLocalPicardData_of_regular
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hReg : ChartCoordPicardRegular X) (α : M) :
    ChartLocalPicardData X α :=
  let h := time_dependent_vf_chart_local_picard_with_lipschitz X α
    hReg.1 (hReg.2 α)
  { T := h.choose
    T_pos := h.choose_spec.1
    r := h.choose_spec.2.choose
    r_pos := h.choose_spec.2.choose_spec.1
    flow := h.choose_spec.2.choose_spec.2.choose
    flow_spec := h.choose_spec.2.choose_spec.2.choose_spec }

end DifferentialGeometry.PDE.RicciFlow.ODE
