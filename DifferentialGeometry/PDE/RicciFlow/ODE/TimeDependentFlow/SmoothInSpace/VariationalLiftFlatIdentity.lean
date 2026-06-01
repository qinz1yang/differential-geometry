import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftManifoldFlowOrbitODE
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatToCovariant
import DifferentialGeometry.Integral.Connection.ChristoffelCorrectionBasepoint

/-!
# The FLAT per-slot linearized-flow identity (dischargeable directly from the operator ODE)

The committed connector chain reduces the *covariant* per-slot variational identity
`RawVariationalIdentity g X Φ_fam t x v`
(`TimeDependentFlow/VariationalFlow.lean`) to the value equation `hsplit`, which equates the
operator-ODE derivative value `(T'.comp (chartCloseFderiv … t) + (chartCloseTriv … t).comp P') v`
with the trivialised-flat-plus-metric-Christoffel decomposition.  As the module docstring of
`SmoothInSpace/VariationalLiftManifoldFlowOrbitODE.lean` records (the residual identity (★)),
`hsplit` is **false in a general chart**: the genuine derivative of the orbit pushforward curve
`s ↦ mfderiv (Φ_fam s) x v`, read in Mathlib's *moving* target chart, is the **flat / Lie-type**
value `T' (dΦv) + P' v` — *not* the covariant value `-∇_{dΦv} X`.  The two differ by the metric
Christoffel contraction at the basepoint (entering only after the inner-product pairing of the
two slots, where metric-compatibility makes the metric-transport term appear).

This file exposes the genuinely-dischargeable object: the **flat** per-slot identity
`RawVariationalIdentityFlat`, asserting that the orbit pushforward curve has, at `t`, the
*flat* operator-ODE derivative value — the value that `chartCloseDop_hasDerivAt_clm_comp`
(`SmoothInSpace/VariationalLiftManifoldFlowOrbitODE.lean`) actually produces.  Unlike the
covariant `RawVariationalIdentity`, this identity is closed **directly** from the product-rule
operator ODE for `chartCloseDop` (no `hsplit`, no false `D²φ = Γ`), once the two factor
`HasDerivAt` data are supplied:

* `hT : HasDerivAt (chartCloseTriv Φ_fam α x) T' t` — the orbit-derivative of the moving
  inverse trivialisation (a smooth-structure chart-transition jet); and
* `hP : HasDerivAt (chartCloseFderiv Φ_fam α x) P' t` — the flat spatial-variational ODE.

Both are *chart-smoothness* data of the concrete DeTurck-field flow, taken here as explicit
inputs (the "F1" inputs), exactly as in the orbit-ODE assembly
`rawVariationalIdentity_of_orbitODE_factors`, but **without** the false metric value equation
`hsplit`.

## What is closed here, and the honest residual

* `RawVariationalIdentityFlat` — the predicate packaging the flat per-slot `HasDerivAt`.
* `rawVariationalIdentityFlat_of_orbitODE_factors` — its discharge from the two factor
  `HasDerivAt`s plus orbit-continuity, via `chartCloseDop_hasDerivAt_clm_comp` and the eventual
  reduction `chartCloseDop_eventuallyEq_mfderiv_orbit`.  No `hsplit`, no metric step.
* `rawVariationalIdentityFlat_iff_flat_value` — the flat identity is equivalent to the orbit
  pushforward curve carrying the *applied* operator-ODE derivative `T' (dΦv) + P' v`
  (`chartCloseDop_deriv_basepoint_apply`).

The residual that connects the flat value to the covariant value is **not** a per-slot
equation but the metric-Christoffel contraction at the basepoint; it is handled at the
*pairing* level (the symmetric `g.inner` two-slot pairing) in
`VariationalFlowFlatPairing.lean`, where metric-compatibility identifies it with the
metric-transport term.  No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style
hypothesis, no joint-`C^∞`-on-`ℝ × M` predicate, and **no** false `D²φ = Γ` identification
appears.  No hypothesis-packaging: the inputs are factor `HasDerivAt`s and a continuity datum,
none of which is — or trivially destructures to — the flat per-slot `HasDerivAt` conclusion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section FlatIdentity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The FLAT per-slot linearized-flow variational identity.**

For the genuine integral flow `Φ_fam` of `X`, the pushforward of a fixed tangent vector `v`
along the flow,

  `s ↦ (mfderiv (Φ_fam s) x v : E)`,

has at time `t` the *flat* vector-valued derivative

  `T' (mfderiv (Φ_fam t) x v) + P' v`,

i.e. the value produced by the product-rule operator ODE for the canonical chart operator
`chartCloseDop` (the orbit-derivative `T'` of the moving inverse trivialisation applied to the
basepoint pushforward, plus the flat spatial-variational value `P' v`).  This is the genuine
derivative of the orbit pushforward curve read in Mathlib's moving target chart — the
**flat / Lie-type** value, *not* the covariant `-∇_{dΦv} X`.  It is parametrised by the two
factor-ODE derivative values `T'`, `P'` (the chart-smoothness data of the concrete flow). -/
def RawVariationalIdentityFlat
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (T' P' : E →L[ℝ] E) : Prop :=
  HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
    (T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v) t

/-- **The flat identity is equivalent to the operator-ODE derivative carried by `chartCloseDop`.**

Under the eventual reduction of the operator-applied curve `s ↦ chartCloseDop … s v` to the
orbit pushforward curve `s ↦ mfderiv (Φ_fam s) x v`
(`chartCloseDop_eventuallyEq_mfderiv_orbit`), the flat identity
`RawVariationalIdentityFlat Φ_fam t x v T' P'` holds **iff** the operator-applied curve has, at
`t`, the applied product-rule derivative value `T' (dΦv) + P' v`.  The two `HasDerivAt`
statements are about eventually-equal functions and transfer by
`Filter.EventuallyEq.hasDerivAt_iff`. -/
theorem rawVariationalIdentityFlat_iff_flat_value
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (T' P' : E →L[ℝ] E)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P'
      ↔ HasDerivAt (fun s : ℝ => chartCloseDop (I := I) Φ_fam (Φ_fam t x) x s v)
          (T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v) t := by
  unfold RawVariationalIdentityFlat
  exact (Filter.EventuallyEq.hasDerivAt_iff
    (chartCloseDop_eventuallyEq_mfderiv_orbit (I := I) Φ_fam t x v hcontAt)).symm

/-- **Discharge of the flat per-slot identity from the two factor `HasDerivAt`s.**

Given the orbit-continuity datum `hcontAt` and the two factor `HasDerivAt` data

* `hT : HasDerivAt (chartCloseTriv Φ_fam α x) T' t` (moving inverse trivialisation jet), and
* `hP : HasDerivAt (chartCloseFderiv Φ_fam α x) P' t` (flat spatial-variational ODE),

with `α := Φ_fam t x`, the flat per-slot identity `RawVariationalIdentityFlat` holds.

The proof is the genuine, metric-free closing: the product-rule operator ODE
`chartCloseDop_hasDerivAt_clm_comp` gives the operator-valued `HasDerivAt`; applying the fixed
continuous-linear *evaluation-at-`v`* functional `ContinuousLinearMap.apply ℝ E v`
(`HasFDerivAt.comp_hasDerivAt`) turns it into the `E`-valued `HasDerivAt` of the
operator-applied curve `s ↦ chartCloseDop … s v`, with derivative the product-rule value
applied to `v`; the basepoint reading `chartCloseDop_deriv_basepoint_apply` rewrites that value
as `T' (dΦv) + P' v`; and the eventual reduction
(`rawVariationalIdentityFlat_iff_flat_value`) transfers it to the orbit pushforward curve.

No `hsplit`, no metric Christoffel step, no false `D²φ = Γ`.  No hypothesis-packaging: the
inputs are the two factor `HasDerivAt`s and a continuity datum, none of which is the flat
per-slot `HasDerivAt` conclusion. -/
theorem rawVariationalIdentityFlat_of_orbitODE_factors
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {T' P' : E →L[ℝ] E}
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x) P' t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v T' P' := by
  have hDchart := chartCloseDop_hasDerivAt_clm_comp (I := I) Φ_fam (Φ_fam t x) x t hT hP
  have hEvalv :
      HasDerivAt (fun s : ℝ => chartCloseDop (I := I) Φ_fam (Φ_fam t x) x s v)
        ((T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
            + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v) t := by
    have := (ContinuousLinearMap.apply ℝ E v).hasFDerivAt.comp_hasDerivAt t hDchart
    simpa using this
  rw [chartCloseDop_deriv_basepoint_apply (I := I) Φ_fam t x v T' P'] at hEvalv
  exact (rawVariationalIdentityFlat_iff_flat_value (I := I) Φ_fam t x v T' P' hcontAt).2 hEvalv

end FlatIdentity

end DifferentialGeometry.PDE.RicciFlow.ODE
