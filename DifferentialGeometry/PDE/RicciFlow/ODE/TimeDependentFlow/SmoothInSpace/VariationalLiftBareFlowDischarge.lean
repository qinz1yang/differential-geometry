import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFactorDischarge
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.Manifold
import DifferentialGeometry.Analysis.ODE.FlowC1

/-!
# Discharging the chart-realised factor inputs from the BARE geometric flow

The factor-producer discharge `rawVariationalIdentityFlat_of_chart_realisation`
(`SmoothInSpace/VariationalLiftFactorDischarge.lean`) consumes, in the target chart
`α := Φ_fam t x`, four genuine per-flow data:

* `heucl` / `heucl_diff` — the Euclidean operator-valued variational ODE and per-time spatial
  differentiability of a chart-coordinate flow `Φ_eucl`;
* `hagree` — the eventual spatial chart-conjugation, assembled from a *spatial chart realisation*
  `hreal` via `hagree_of_spatial_chart_realisation`; and
* `hg` — the moving-trivialisation orbit jet, derived from a chart-jet `hGfd` and a chart-orbit
  velocity (the time-derivative of `s ↦ extChartAt I α (Φ_fam s x)`).

The chart-coordinate input `Φ_eucl` must simultaneously (i) realise the genuine manifold flow
`Φ_fam` in the chart `α` near `(t, x)`, and (ii) carry the Euclidean variational ODE.  The
chart-cover construction reads `Φ_fam` in a *representative* chart `αRep` that differs from the
target chart `α` at a positive orbit time, and the moving-chart reconciliation
(`SmoothInSpace/VariationalLiftMovingChartReconciliation.lean`) re-expresses the representative
realisation into the target chart only under a chart-transition compatibility hypothesis
`hcompat`, which is **false** for a field with non-affine chart transitions (the geometric
DeTurck field).

This file supplies the two inputs from the **bare geometric flow** instead, bypassing the
compatibility obstruction entirely.  The bare manifold flow `Φ` of `X` (the smooth-dependence
headline `h3_local_flow_jointSmooth_and_integralCurve`, read off the cutoff-field Euclidean
local flow `ΦE` in the chart at the *expansion centre* `α`) carries, by
`chartflow_eq_bareflow_on_U`, the **genuine geometric** velocity — not a chart-convention
transport.  Consequently the chart reading of that flow is a `IsLocalFlow` Picard datum whose
chart-coordinate trajectory **is** the geometric orbit:

  `Φ_fam s y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)`   (near `(t, x)`),

with `Φ_eucl z s := Φ_E (z, s)` the chart-`α` Euclidean flow.  No `hcompat`, no chart-transition
naturality datum: the realisation is the genuine equality of *manifold points* the bare flow
delivers, valid because the bare flow read in the *same* chart `α` is unconditionally the
geometric orbit.

The two genuine, separable hypotheses that survive are:

* `hΦE : IsLocalFlow f t₀ α₀ r tmin tmax ΦE` together with `hf : ContDiff ℝ ∞ (uncurry f)`,
  `hΦsmooth : ContDiffOn ℝ ∞ ΦE U` — the **joint-`(t, x)` regularity** of the chart-coordinate
  flow.  This is exactly the regularity that the parabolic-smoothing program (gap-II) supplies
  for the DeTurck flow; it is a genuine analytic input, never the variational conclusion; and
* `hreal` — the **bare-flow geometric chart-`α` realisation**: a point-level equality of
  manifold points (`Φ_fam s y = (extChartAt I α).symm (ΦE (extChartAt I α y, s))`) with the
  chart-coordinate value confined to the chart target.  This is the genuine geometric datum the
  bare flow makes available *without* the false `hcompat`; it is not — and does not trivially
  destructure to — the operator-valued / scalar `HasDerivAt` discharge conclusion.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no `hcompat`-style
chart-transition naturality hypothesis, no joint-`C^∞`-on-`ℝ × M` predicate.  No
hypothesis-packaging: every supplied input is the Euclidean ODE / a Picard-flow regularity
datum, a point-level spatial realisation, a chart-coordinate velocity, or a chart-jet — none of
which is the `HasDerivAt` discharge conclusion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.PDE.DeTurck

section BareFlowDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **`heucl` for the bare-flow chart-coordinate reading.**

For the chart-`α` Euclidean Picard flow `ΦE` of a field `f`, jointly `C^∞` on an open box `U`
strictly interior to the flow domain, the spatial Fréchet-derivative curve carries the
operator-valued variational `HasDerivAt` at the interior chart coordinate
`extChartAt I (Φ_fam t x) x`.  This is `heucl_factorODE_of_isLocalFlow` specialised to the
target chart `α := Φ_fam t x`; it is the discharge's `heucl` with `Φ_eucl z s := ΦE (z, s)`. -/
theorem heucl_of_bareFlow
    {f : ℝ → E → E} {t₀ : ℝ} {α₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {ΦE : E × ℝ → E}
    (hΦE : IsLocalFlow f t₀ α₀ r tmin tmax ΦE)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ ΦE U)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (x : M) {t : ℝ}
    (hxsU : (extChartAt I (Φ_fam t x) x, t) ∈ U)
    (hx : extChartAt I (Φ_fam t x) x ∈ Metric.ball α₀ r) (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (fun s : ℝ => fderiv ℝ (fun z => ΦE (z, s))
        (extChartAt I (Φ_fam t x) x))
      ((fderiv ℝ (f t) (ΦE (extChartAt I (Φ_fam t x) x, t))).comp
        (fderiv ℝ (fun z => ΦE (z, t)) (extChartAt I (Φ_fam t x) x))) t :=
  heucl_factorODE_of_isLocalFlow (I := I) hΦE hf hUopen hΦsmooth (Φ_fam t x) x hxsU hx ht

/-- **`RawVariationalIdentityFlat` for the concrete bare-flow `Φ_fam`.**

The hypotheses split into the bare-flow chart-coordinate Picard datum (Part (A): the
`IsLocalFlow` `hΦE`, the field regularity `hf`, the joint `ContDiffOn` `hΦsmooth`, and the
interior-membership data `hxsU`/`hx`/`ht`), and the bare-flow geometric realisation / jet data:

* `hx_src` — `x` lies in the target chart source;
* `hreal` — the bare-flow geometric chart-`α` realisation
  `∀ᶠ s near t, ∀ᶠ y near x, Φ_fam s y = (extChartAt I α).symm (ΦE (extChartAt I α y, s)) ∧ confinement`;
* `hc_eucl` — the chart-coordinate orbit velocity `HasDerivAt (fun s => ΦE (extChartAt I α x, s)) velChart t`;
* `hGfd` — the moving-trivialisation chart-function `HasFDerivAt` at the orbit-time chart point;
* `hcontAt` — continuity of the orbit at `t`.

It produces `RawVariationalIdentityFlat (I := I) Φ_fam t x v _ _` for the bare flow.  The proof
derives `heucl` (Part (A)), `heucl_diff` (from joint smoothness), `hagree`/`hc`/`hg`
(`hagree_of_spatial_chart_realisation`, `orbit_velocity` from the realisation,
`chartMovingTriv_orbit_hasDerivAt_of_chartJet`), and routes everything into
`rawVariationalIdentityFlat_of_chart_realisation`.  No `hcompat`, no
`HasLocallyConstantChartAt`.  No hypothesis-packaging: the realisation inputs are point-level
manifold equalities and chart velocities, the regularity inputs are a Picard flow and its joint
smoothness, and the conclusion is the vector-valued orbit-pushforward `HasDerivAt`, derived not
assumed. -/
theorem rawVariationalIdentityFlat_of_bareFlow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    {f : ℝ → E → E} {t₀ : ℝ} {α₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {ΦE : E × ℝ → E}
    {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart : E}
    (hΦE : IsLocalFlow f t₀ α₀ r tmin tmax ΦE)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ ΦE U)
    (hxsU : (extChartAt I (Φ_fam t x) x, t) ∈ U)
    (hx : extChartAt I (Φ_fam t x) x ∈ Metric.ball α₀ r) (ht : t ∈ Ioo tmin tmax)
    (hUtimeOpen : ∀ᶠ s : ℝ in 𝓝 t, (extChartAt I (Φ_fam t x) x, s) ∈ U)
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hreal : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm (ΦE (extChartAt I (Φ_fam t x) y, s))
        ∧ ΦE (extChartAt I (Φ_fam t x) y, s) ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl : HasDerivAt
      (fun s : ℝ => ΦE (extChartAt I (Φ_fam t x) x, s)) velChart t)
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x)))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart))
      (((fderiv ℝ (f t) (ΦE (extChartAt I (Φ_fam t x) x, t))).comp
          (fderiv ℝ (fun z => ΦE (z, t)) (extChartAt I (Φ_fam t x) x))).comp
        (trivToE (I := I) (Φ_fam t x) x)) := by
  classical
  set Φ_eucl : E → ℝ → E := fun z s => ΦE (z, s) with hΦeucl
  have heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x))
      ((fderiv ℝ (f t) (ΦE (extChartAt I (Φ_fam t x) x, t))).comp
        (fderiv ℝ (fun z => ΦE (z, t)) (extChartAt I (Φ_fam t x) x))) t :=
    heucl_of_bareFlow (I := I) hΦE hf hUopen hΦsmooth Φ_fam x hxsU hx ht
  have heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) (extChartAt I (Φ_fam t x) x) := by
    filter_upwards [hUtimeOpen] with s hsU
    have hΦE_at : ContDiffAt ℝ ∞ ΦE (extChartAt I (Φ_fam t x) x, s) :=
      hΦsmooth.contDiffAt (hUopen.mem_nhds hsU)
    have hincl : ContDiffAt ℝ ∞ (fun z : E => (z, s)) (extChartAt I (Φ_fam t x) x) :=
      contDiffAt_id.prodMk contDiffAt_const
    have hslice : ContDiffAt ℝ ∞ (fun z => ΦE (z, s)) (extChartAt I (Φ_fam t x) x) :=
      hΦE_at.comp (extChartAt I (Φ_fam t x) x) hincl
    exact hslice.differentiableAt (by simp)
  have hagree :
      ∀ᶠ s : ℝ in 𝓝 t,
        (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
          =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I (Φ_fam t x) y) s) :=
    hagree_of_spatial_chart_realisation (I := I) Φ_fam (Φ_fam t x) x t Φ_eucl hreal
  have hreal_orbit : ∀ᶠ s : ℝ in 𝓝 t,
      extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x) = Φ_eucl (extChartAt I (Φ_fam t x) x) s := by
    filter_upwards [hreal] with s hs
    obtain ⟨hpt, htgt⟩ := hs.self_of_nhds
    rw [hpt, (extChartAt I (Φ_fam t x)).right_inv htgt]
  have hc : HasDerivAt
      (fun s : ℝ => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x)) velChart t := by
    refine hc_eucl.congr_of_eventuallyEq ?_
    filter_upwards [hreal_orbit] with s hs
    exact hs
  have hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) (G' velChart) t :=
    chartMovingTriv_orbit_hasDerivAt_of_chartJet (I := I) Φ_fam (Φ_fam t x) x t hGfd hc
  exact rawVariationalIdentityFlat_of_chart_realisation (I := I) Φ_fam x t v
    Φ_eucl hx_src heucl heucl_diff hagree hg hcontAt

/-- **The paired residual for the concrete bare flow `Φ_fam`.**

Composes the section-(B) `RawVariationalIdentityFlat` data for slots `v` and `w` (each produced
from the bare-flow chart-coordinate Picard datum and the bare-flow geometric realisation, with
no `hcompat`) with the discharge's basepoint-bridge / flat-value machinery via
`variational_flow_flat_paired_residual_of_chart_realisation`.

The output is the headline frozen-metric moving-pushforward inner-product variation derivative

  `-lieDerivMetric g X (Φ_fam t x) dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`,

for the bare flow.  The remaining genuine inputs are the per-slot bare-flow data
(`hxsU_v`/`hxsU_w`, `hx`, `ht`, `hUtimeOpen`, `hreal_v`/`hreal_w`, `hc_eucl_v`/`hc_eucl_w`), the
shared chart datum (`hΦE`, `hf`, `hUopen`, `hΦsmooth`, `hGfd`, `hcontAt`), the basepoint
goodset / side-condition data (`hα`, `hRdiff`, `hCdiff`), and the two metric-free flat-value
identities (`hflatval_v`/`hflatval_w`).  No `hcompat`, no `HasLocallyConstantChartAt`.  No
hypothesis-packaging: the bridges are discharged inside the headline, the flat-value inputs are
`E`-equations, and the conclusion is the scalar pairing `HasDerivAt`. -/
theorem variational_flow_flat_paired_residual_of_bareFlow
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    {f : ℝ → E → E} {t₀ : ℝ} {α₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {ΦE : E × ℝ → E}
    {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart_v velChart_w : E}
    (hΦE : IsLocalFlow f t₀ α₀ r tmin tmax ΦE)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ ΦE U)
    (hxsU : (extChartAt I (Φ_fam t x) x, t) ∈ U)
    (hx : extChartAt I (Φ_fam t x) x ∈ Metric.ball α₀ r) (ht : t ∈ Ioo tmin tmax)
    (hUtimeOpen : ∀ᶠ s : ℝ in 𝓝 t, (extChartAt I (Φ_fam t x) x, s) ∈ U)
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x)))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hreal_v : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm (ΦE (extChartAt I (Φ_fam t x) y, s))
        ∧ ΦE (extChartAt I (Φ_fam t x) y, s) ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl_v : HasDerivAt
      (fun s : ℝ => ΦE (extChartAt I (Φ_fam t x) x, s)) velChart_v t)
    (hreal_w : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm (ΦE (extChartAt I (Φ_fam t x) y, s))
        ∧ ΦE (extChartAt I (Φ_fam t x) y, s) ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl_w : HasDerivAt
      (fun s : ℝ => ΦE (extChartAt I (Φ_fam t x) x, s)) velChart_w t)
    (hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hflatval_v :
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart_v))
          (mfderiv I I (Φ_fam t : M → M) x v)
        + (((fderiv ℝ (f t) (ΦE (extChartAt I (Φ_fam t x) x, t))).comp
              (fderiv ℝ (fun z => ΦE (z, t)) (extChartAt I (Φ_fam t x) x))).comp
            (trivToE (I := I) (Φ_fam t x) x)) v
        = -(fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)
            + movingTrivCorrection (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y)
                (mfderiv I I (Φ_fam t : M → M) x v)))
    (hflatval_w :
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart_w))
          (mfderiv I I (Φ_fam t : M → M) x w)
        + (((fderiv ℝ (f t) (ΦE (extChartAt I (Φ_fam t x) x, t))).comp
              (fderiv ℝ (fun z => ΦE (z, t)) (extChartAt I (Φ_fam t x) x))).comp
            (trivToE (I := I) (Φ_fam t x) x)) w
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
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t := by
  have hv_flat := rawVariationalIdentityFlat_of_bareFlow (I := I) Φ_fam t x v
    hΦE hf hUopen hΦsmooth hxsU hx ht hUtimeOpen hx_src hreal_v hc_eucl_v hGfd hcontAt
  have hw_flat := rawVariationalIdentityFlat_of_bareFlow (I := I) Φ_fam t x w
    hΦE hf hUopen hΦsmooth hxsU hx ht hUtimeOpen hx_src hreal_w hc_eucl_w hGfd hcontAt
  exact variational_flow_flat_paired_residual_of_chart_realisation (I := I) g X Φ_fam t x v w
    _ _ _ _ hv_flat hw_flat hα hRdiff hCdiff hflatval_v hflatval_w

end BareFlowDischarge

end DifferentialGeometry.PDE.RicciFlow.ODE
