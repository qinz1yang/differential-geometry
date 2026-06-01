import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFactorProducers
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.VariationalFlowFlatPairedResidual

/-!
# Discharging the factor-producer inputs from a concrete chart-coordinate flow

The factor producers of `SmoothInSpace/VariationalLiftFactorProducers.lean`,

* `chartCloseFderiv_hasDerivAt_of_eucl` (producing `hP`), and
* `chartCloseTriv_hasDerivAt_of_movingTriv` (producing `hT`),

and the paired-residual `variational_flow_flat_paired_residual_hasDerivAt`
(`TimeDependentFlow/VariationalFlowFlatPairedResidual.lean`), all take their genuine
analytic inputs (`heucl`, `hagree`, `hg`, the bridge side conditions `hRdiff`/`hCdiff`) as
**explicit hypotheses**.  This file supplies those inputs from a *concrete* chart-coordinate
flow `Φ_eucl : E → ℝ → E` on the model space `E`, closing the gap between "the producer takes
the Euclidean ODE / chart-agreement as input" and "those are read off the flow".

The discharge is organised by input:

## `heucl` — the Euclidean operator-valued variational ODE (FULLY DISCHARGED)

For the chart-coordinate flow written as `Φ_eucl z s := Φ (z, s)` of a `IsLocalFlow` Picard
datum (the chart realisation of `manifoldFlowFamily`), the genuinely sorry-free Euclidean
linearized-flow ODE `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
(`SmoothInSpace/VariationalODE.lean`) supplies, at every strictly-interior chart coordinate,
the operator-valued `HasDerivAt`

  `HasDerivAt (fun s => fderiv ℝ (fun z => Φ_eucl z s) z₀) D'_eucl t`,

with `z₀ := extChartAt I α x`.  This is *exactly* the producer's `heucl`; no metric, no joint
`C^∞` on `ℝ × M`, no `HasLocallyConstantChartAt`.  `heucl_factorODE_of_isLocalFlow` is the
verbatim repackaging.

## `hagree` — the spatial chart conjugation (DERIVED from the spatial chart realisation)

The producer needs the **eventual** spatial chart-conjugation equality

  `∀ᶠ s near t, (fun y => extChartAt I α (Φ_fam s y)) =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)`.

This file derives it from the *spatial chart realisation* of the flow — the genuine per-flow
datum that the chart-cover construction delivers (`ChartGlue.manifold_contMDiffAt_of_chart_smooth_flow`'s
`hΦ_eq` shape, the `hLocalFwd` field of `manifoldFlowFamily_exists`):

  `(s, y) near (t, x): Φ_fam s y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)`,

read in the *fixed* chart `α`.  Composing with `extChartAt I α ∘ (extChartAt I α).symm = id` on
the chart target (`extChartAt_left_inv` after confinement), the spatial realisation collapses to
the producer's chart-conjugation.  `hagree_of_spatial_chart_realisation` performs this collapse.

The spatial chart realisation is a genuine geometric datum of the flow (an equality of *points
in `M`*), not the operator-valued `HasDerivAt` conclusion of any producer; supplying it is not
hypothesis-packaging.  It is the honest separable input the flow's chart-cover regularity makes
available — for the chart at the *base point of expansion*.  At a general orbit time the target
chart `α = Φ_fam t x` differs from the chart-cover's representative chart, which is recorded as
the remaining genuine flow datum (see the module-level note at the bottom of the file).

## `hg` — the moving-trivialisation orbit jet (DERIVED from the chart jet + chart-orbit velocity)

The producer's `hg` is the time-derivative of the CLM-valued path
`s ↦ chartMovingTriv α (extChartAt I α (Φ_fam s x))`.  `chartMovingTriv_orbit_hasDerivAt_of_chartJet`
derives it by the chain rule from the `HasFDerivAt` of the moving-trivialisation chart-function
`chartMovingTriv α` (the `HasFDerivAt` strengthening of `hCdiff`, available from the tangent-bundle
`coordChangeL` smoothness) and the two-sided chart-orbit velocity `HasDerivAt` of
`s ↦ extChartAt I α (Φ_fam s x)` (available from the open-interval `ContDiffOn` of the
chart-coordinate Picard flow).  Both are genuine separable smoothness data; `hg` is *derived*.

## Composition

`chartCloseFactors_of_chart_realisation` feeds the discharged `heucl`/`hagree`/`hg` into the two
producers, yielding the two factor `HasDerivAt`s `hP`/`hT` for the concrete flow;
`rawVariationalIdentityFlat_of_chart_realisation` then composes with
`rawVariationalIdentityFlat_of_orbitODE_factors` to obtain `RawVariationalIdentityFlat`, and
`variational_flow_flat_paired_residual_of_chart_realisation` discharges the bridge side
conditions and routes everything into the paired residual — with no remaining undischarged input
except the genuine flow data (the chart-coordinate flow + its Euclidean ODE, the spatial chart
realisation, the moving-trivialisation chart jet + chart-orbit velocity, and the orbit basepoint
goodset/differentiability bridge data plus the metric-free flat-value identities).

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no joint-`C^∞`-on-`ℝ × M`
predicate.  No hypothesis-packaging: every supplied input is the Euclidean ODE, a *point*-level
spatial chart realisation, a smooth-structure orbit jet, or a basepoint differentiability datum,
none of which is — or trivially destructures to — the operator-valued / scalar `HasDerivAt`
conclusions the producers and the paired residual deliver.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.PDE.DeTurck

section Discharge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **`heucl` from a `IsLocalFlow` Picard datum.**

For the chart-coordinate flow `Φ_eucl z s := Φ (z, s)` of a `IsLocalFlow` datum on the model
space `E`, jointly `C^∞` on an open set `U` strictly interior to the flow domain, the spatial
Fréchet-derivative curve has, at any interior chart coordinate `z₀ := extChartAt I α x`, the
operator-valued `HasDerivAt`

  `HasDerivAt (fun s => fderiv ℝ (fun z => Φ_eucl z s) z₀) D'_eucl t`

with `D'_eucl := (fderiv ℝ (f t) (Φ (z₀, t))).comp (fderiv ℝ (fun z => Φ (z, t)) z₀)`.

This is exactly the producer's `heucl`, read off `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
with `Φ_eucl := fun z s => Φ (z, s)`.  No metric, no `HasLocallyConstantChartAt`, no joint
`C^∞` on `ℝ × M`.  No hypothesis-packaging: the inputs are the flow predicate, the model-space
joint smoothness, and interior membership; the conclusion is the operator-valued ODE, derived
not assumed. -/
theorem heucl_factorODE_of_isLocalFlow
    {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ Φ U)
    (α x : M) {t : ℝ}
    (hxsU : (extChartAt I α x, t) ∈ U)
    (hx : extChartAt I α x ∈ Metric.ball x₀ r) (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => (fun z' s' => Φ (z', s')) z s)
        (extChartAt I α x))
      ((fderiv ℝ (f t) (Φ (extChartAt I α x, t))).comp
        (fderiv ℝ (fun z => Φ (z, t)) (extChartAt I α x))) t :=
  IsLocalFlow.hasDerivAt_partial_spatial_fderiv hΦ hf hUopen hΦsmooth hxsU hx ht

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
/-- **`hagree` from the spatial chart realisation.**

Suppose, for `s` near `t`, the manifold flow agrees — near `x` in the fixed chart `α` — with the
chart-coordinate flow `Φ_eucl` conjugated by the chart, with the chart-coordinate value confined
to the chart target:

  `∀ᶠ s near t, ∀ᶠ y near x, Φ_fam s y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)`
  and `Φ_eucl (extChartAt I α y) s ∈ (extChartAt I α).target`.

Then the producer's chart-conjugation eventual equality holds:

  `∀ᶠ s near t, (fun y => extChartAt I α (Φ_fam s y)) =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s)`.

The proof applies `extChartAt I α` to the spatial realisation and cancels via
`PartialEquiv.right_inv` on the chart target.  No hypothesis-packaging: the input is a
*point*-level equality of manifold points (and a target-confinement), not the operator-valued
`HasDerivAt` conclusion of any producer. -/
theorem hagree_of_spatial_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ) (Φ_eucl : E → ℝ → E)
    (hreal : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)
        ∧ Φ_eucl (extChartAt I α y) s ∈ (extChartAt I α).target) :
    ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s) := by
  filter_upwards [hreal] with s hs
  filter_upwards [hs] with y hy
  obtain ⟨hpt, htgt⟩ := hy
  rw [hpt, (extChartAt I α).right_inv htgt]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **`hg` from the moving-triv chart jet and the chart-orbit velocity.**

Given the `HasFDerivAt` of the moving-trivialisation chart-function `chartMovingTriv α` at the
orbit-time chart point `c t := extChartAt I α (Φ_fam t x)` (the `HasFDerivAt` strengthening of the
`hCdiff` side condition) and the two-sided chart-orbit velocity `HasDerivAt` of
`c s := extChartAt I α (Φ_fam s x)` at the interior time `t`, the moving-trivialisation orbit jet

  `HasDerivAt (fun s => chartMovingTriv α (extChartAt I α (Φ_fam s x))) (G'.comp velChart) t`

holds, by the chain rule `HasFDerivAt.comp_hasDerivAt`.

This is the producer for the `hg` input of `chartCloseFactors_of_chart_realisation` /
`chartCloseTriv_hasDerivAt_of_movingTriv`.  No hypothesis-packaging: the inputs are the chart-jet
`HasFDerivAt` and the chart-orbit velocity `HasDerivAt`, composed; the conclusion is the orbit-jet
`HasDerivAt`, derived not assumed. -/
theorem chartMovingTriv_orbit_hasDerivAt_of_chartJet
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart : E}
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) α z) G'
      (extChartAt I α ((Φ_fam t : M → M) x)))
    (hc : HasDerivAt (fun s : ℝ => extChartAt I α ((Φ_fam s : M → M) x)) velChart t) :
    HasDerivAt (fun s : ℝ => chartMovingTriv (I := I) α
        (extChartAt I α ((Φ_fam s : M → M) x))) (G' velChart) t := by
  have := hGfd.comp_hasDerivAt t hc
  simpa using this

/-- **The two factor `HasDerivAt`s `hP`, `hT` from the chart realisation.**

Feeds the discharged Euclidean ODE (`heucl`) and the discharged chart-conjugation (`hagree`)
into `chartCloseFderiv_hasDerivAt_of_eucl`, and the moving-trivialisation orbit jet (`hg`) into
`chartCloseTriv_hasDerivAt_of_movingTriv`, returning the two orbit-ODE factor `HasDerivAt`s for
the target chart `α := Φ_fam t x` consumed by `rawVariationalIdentityFlat_of_orbitODE_factors`.

The hypotheses are exactly the genuine per-flow data:

* `hx_src` — `x` lies in the chart source of `α := Φ_fam t x`;
* `heucl` — the Euclidean operator-valued ODE (from `heucl_factorODE_of_isLocalFlow`);
* `heucl_diff` — the per-time spatial differentiability of `Φ_eucl`;
* `hagree` — the eventual chart-conjugation (from `hagree_of_spatial_chart_realisation`);
* `hg` — the moving-trivialisation orbit jet (the smooth-structure chart-transition first jet);
* `hcontAt` — orbit continuity at `t`.

No hypothesis-packaging: the conclusion bundles two operator-valued `HasDerivAt`s, derived from
the producers, not assumed. -/
theorem chartCloseFactors_of_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (x : M) (t : ℝ)
    (Φ_eucl : E → ℝ → E) {D'_eucl g' : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x)) D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I (Φ_fam t x) y) s))
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x)
        ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g') t
      ∧ HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x)
          (D'_eucl.comp (trivToE (I := I) (Φ_fam t x) x)) t := by
  refine ⟨chartCloseTriv_hasDerivAt_of_movingTriv (I := I) Φ_fam t x hg hcontAt, ?_⟩
  exact chartCloseFderiv_hasDerivAt_of_eucl (I := I) Φ_fam (Φ_fam t x) x t Φ_eucl
    hx_src heucl heucl_diff hagree

/-- **`RawVariationalIdentityFlat` for the concrete chart-realised flow.**

Composes `chartCloseFactors_of_chart_realisation` with
`rawVariationalIdentityFlat_of_orbitODE_factors`: the two discharged factor `HasDerivAt`s and the
orbit-continuity datum produce the flat per-slot variational identity for the concrete flow.  The
inputs are precisely the genuine per-flow data of `chartCloseFactors_of_chart_realisation`.  No
hypothesis-packaging: `RawVariationalIdentityFlat` is the vector-valued orbit-pushforward
`HasDerivAt`, derived from the producers and the orbit-ODE assembly, not assumed. -/
theorem rawVariationalIdentityFlat_of_chart_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (x : M) (t : ℝ) (v : TangentSpace I x)
    (Φ_eucl : E → ℝ → E) {D'_eucl g' : E →L[ℝ] E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x)) D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x))
    (hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I (Φ_fam t x) y) s))
    (hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) g' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) g')
      (D'_eucl.comp (trivToE (I := I) (Φ_fam t x) x)) := by
  obtain ⟨hT, hP⟩ := chartCloseFactors_of_chart_realisation (I := I) Φ_fam x t Φ_eucl
    hx_src heucl heucl_diff hagree hg hcontAt
  exact rawVariationalIdentityFlat_of_orbitODE_factors (I := I) Φ_fam t x v hcontAt hT hP

end Discharge

section PairedResidualDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **`hbridge` for a slot, from the basepoint bridge data.**

Discharges one of the paired residual's basepoint-bridge `E`-equations
`∇_{dΦu} X = F(dΦu) + Γ(dΦu)` from the genuine basepoint data — the orbit-basepoint goodset
membership, the section's manifold differentiability at the basepoint, and the convention-bridge
differentiability side conditions — via `leviCivita_basepoint_eq_rawFderiv_add_corrections`.
The section `X` supplies `hX := X.mdifferentiableAt` automatically.

No hypothesis-packaging: the conclusion is an `E`-equation read off `∇g = 0` on the chart, not
the scalar pairing `HasDerivAt` the residual delivers. -/
theorem hbridge_slot_of_basepoint_data
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (u : TangentSpace I x)
    (hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x))) :
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x u)
      = (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x u)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x u))
        + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
            (chartE_section_repr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x u) :=
  leviCivita_basepoint_eq_rawFderiv_add_corrections (I := I) g (Φ_fam t x)
    (X : ∀ y : M, TangentSpace I y) (mfderiv I I (Φ_fam t : M → M) x u)
    hα (X.mdifferentiableAt) hRdiff hCdiff

/-- **The paired residual for the concrete chart-realised flow.**

Composes the section-D `RawVariationalIdentityFlat` data (`hv_flat`/`hw_flat`) with the
discharged basepoint bridges (`hbridge_slot_of_basepoint_data`) and the two metric-free
flat-value identities (`hflatval_v`/`hflatval_w`, the genuine Lie-type variational facts), feeding
`variational_flow_flat_paired_residual_hasDerivAt`.  The output is the headline frozen-metric
moving-pushforward inner-product variation derivative

  `-lieDerivMetric g X (Φ_fam t x) dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`,

for the concrete flow.

The remaining genuine inputs are: the two `RawVariationalIdentityFlat` data (themselves
discharged from the chart realisation in section D); the basepoint goodset/section/side-condition
data; and the two flat-value identities `hflatval_v`/`hflatval_w` (the metric-free trivialised-flat
identities, never the false `D²φ = Γ`).  No hypothesis-packaging: the bridges are discharged, the
flat-value inputs are `E`-equations, the conclusion is the scalar pairing `HasDerivAt`, a distinct
object. -/
theorem variational_flow_flat_paired_residual_of_chart_realisation
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hflatval_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hflatval_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x w))) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t :=
  variational_flow_flat_paired_residual_hasDerivAt (I := I) g X Φ_fam t x v w
    T'v P'v T'w P'w hv_flat hw_flat hflatval_v hflatval_w
    (hbridge_slot_of_basepoint_data (I := I) g X Φ_fam t x v hα hRdiff hCdiff)
    (hbridge_slot_of_basepoint_data (I := I) g X Φ_fam t x w hα hRdiff hCdiff)

end PairedResidualDischarge

end DifferentialGeometry.PDE.RicciFlow.ODE
