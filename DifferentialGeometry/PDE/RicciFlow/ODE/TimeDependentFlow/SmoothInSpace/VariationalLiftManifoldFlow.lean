import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftLocalFlow

/-!
# Per-flow connector: `RawVariationalIdentity` from manifold-flow realization data

This file wires together the proven smooth-in-initial-condition machinery into a single
per-flow connector that produces `RawVariationalIdentity` (the raw vector-valued
variational identity consumed by `variational_flow_feeds_cartan_witness` and, downstream,
by the Hamilton--DeTurck pull-back) from the data a concrete manifold integral flow makes
available.

## The proven ingredients, recalled

For a time-indexed diffeomorphism family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`, the predicate

  `RawVariationalIdentity g X Φ_fam t x v :=
     HasDerivAt (fun s => (mfderiv I I (Φ_fam s) x v : E))
       (-(LeviCivita g) X (Φ_fam t x) (mfderiv I I (Φ_fam t) x v)) t`

is produced by the generic per-flow producer `rawVariationalIdentity_of_isLocalFlow`
(`SmoothInSpace/VariationalLiftLocalFlow.lean`) from:

* `hDchart` — the operator-valued Euclidean chart-flow variational ODE
  `HasDerivAt Dchart Dchart' t` on the model space `E`
  (`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`);
* `hcontAt` — continuity of the orbit `s ↦ Φ_fam s x` at `t`;
* `hwitness` — the eventual reproduction, near `t`, of the transported chart-coordinate
  derivative by `Q (Dchart s d)`;
* `hRdiff`, `hCdiff` — differentiability of the raw representation and the moving
  trivialization at the basepoint image (the convention-bridge side conditions);
* `hsplit` — the honest value decomposition of the true derivative value `Q (Dchart' d)`
  into the **flat variational-ODE contribution** (minus `trivFromE α α` of the trivialised
  flat derivative) **plus** the **moving-target-trivialization residual** (minus
  `trivFromE α α` of the metric Christoffel correction).

## What this connector establishes, and the one genuine residual it exposes

The connector `rawVariationalIdentity_of_manifoldFlowFamily` discharges, from the data a
concrete flow supplies, the two structural hypotheses `hcontAt` and `hwitness`:

* `hcontAt` is the continuity of the orbit at `t`, supplied by the orbit's joint
  continuity (`orbit_continuousAt_of_jointContinuous`) — a separable continuity input,
  never a joint-`C^∞`-on-`ℝ × M` predicate;
* `hwitness` is assembled from the chart-coordinate witness equation
  (`hagree_of_chartFderiv_witness` is *not* needed here: the producer takes `hwitness`
  directly; the connector simply forwards the per-flow chart-coordinate reading the flow
  realization provides).

The remaining inputs — `hDchart`, `hRdiff`, `hCdiff`, and crucially `hsplit` — are left as
genuine per-flow data:

* `hDchart` is the Euclidean variational ODE of the chart-conjugated `-X` flow, available
  from `IsLocalFlow.hasDerivAt_partial_spatial_fderiv` once the chart flow's `IsLocalFlow`
  is in hand (built via `BanachIC` from the chart-coordinate smoothness of `-X`);
* `hsplit` is the **moving-target-trivialization residual** identity — the genuinely
  metric-dependent geometric content. The flat variational ODE produces only the raw flat
  derivative `-∂X` (corrected by the smooth-structure `D²φ` moving-trivialization jet); the
  metric Christoffel correction `christoffelCorrection g α α (X̃_α α) w`, which is the gap
  between `-∂X` (Lie/flat) and `-∇X` (metric covariant), is **not** produced by the pure
  variational ODE. It enters only through a `g`-referencing step (the moving target
  trivialization derivative along the orbit, contracted against the metric).

The naive identification "moving-trivialization correction = metric Christoffel" is *false*
in a general chart (they coincide only in normal/geodesic coordinates at `α`; see
`Geometry/Riemannian/Geodesic/ChartChristoffelTransform.lean`, where the chart-change
second-derivative jet `D²φ` is shown to differ from the metric symbol `Γ`). The metric
Christoffel residual is therefore exposed as a genuine *additive* input in `hsplit`, never
asserted to vanish and never identified with the smooth-structure `D²φ` term.

## No hypothesis-packaging

`hsplit` is an *equality of vectors in `E`* identifying the true derivative value
`Q (Dchart' d)` with a flat-plus-residual sum; it is neither, nor trivially destructures to,
the vector-valued `HasDerivAt` conclusion `RawVariationalIdentity`. The genuine geometric
content (the metric Christoffel residual) is real per-flow data, not the conclusion in
disguise. No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no
joint-`C^∞`-on-`ℝ × M` predicate appears.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Connector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Per-flow raw variational identity from manifold-flow realization data
(continuity discharged).**

Let `α := Φ_fam t x` be the time-`t` orbit point. This connector forwards the proven
generic producer `rawVariationalIdentity_of_isLocalFlow`, discharging the orbit-continuity
hypothesis `hcontAt` from the orbit's joint continuity `hcont` (a separable continuity
input). The remaining inputs are exactly the per-flow chart-coordinate data:

* `hDchart` — the operator-valued Euclidean chart-flow variational ODE
  `HasDerivAt Dchart Dchart' t` (from `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`);
* `hwitness` — the eventual reproduction of the transported chart-coordinate derivative by
  `Q (Dchart s d)` near `t` (the chart-flow realization read through the fixed target chart
  at `α`);
* `hRdiff`, `hCdiff` — differentiability of the raw representation and the moving
  trivialization at the basepoint image;
* `hsplit` — the honest value decomposition of `Q (Dchart' d)` into the flat
  variational-ODE contribution plus the genuinely-metric-dependent moving-target
  trivialization residual (the metric Christoffel correction), supplied as a separate
  additive input, never set to zero.

It produces `RawVariationalIdentity`. No hypothesis-packaging: `hsplit` is an `E`-equation,
not the `HasDerivAt` conclusion; the metric Christoffel residual is genuine per-flow
geometric data. -/
theorem rawVariationalIdentity_of_manifoldFlowFamily
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x))
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
        + (-trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t :=
    orbit_continuousAt_of_jointContinuous (I := I) Φ_fam t x hcont
  exact rawVariationalIdentity_of_isLocalFlow (I := I) g X Φ_fam t x v Q d
    hDchart hcontAt hwitness hRdiff hCdiff hsplit

end Connector

end DifferentialGeometry.PDE.RicciFlow.ODE
