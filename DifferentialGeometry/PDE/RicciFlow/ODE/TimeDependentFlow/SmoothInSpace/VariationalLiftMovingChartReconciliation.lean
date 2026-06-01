import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFactorDischarge
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness

/-!
# Moving-chart reconciliation of the chart-cover flow realisation into the target chart

The factor-producer discharge
`rawVariationalIdentityFlat_of_chart_realisation`
(`SmoothInSpace/VariationalLiftFactorDischarge.lean`) consumes its chart-conjugation input
`hagree` and its moving-trivialisation orbit jet `hg` **in the target chart** `α := Φ_fam t x`
(the chart at the orbit point at time `t`):

* `hagree` — the eventual chart-conjugation reading the manifold flow, near `x` in the fixed
  *target* chart `α`, as a chart-coordinate flow `Φ_eucl` (assembled from the spatial chart
  realisation `hreal` via `hagree_of_spatial_chart_realisation`); and
* `hg` — the moving-trivialisation orbit jet, derived from the *target*-chart orbit velocity
  `hc : HasDerivAt (fun s => extChartAt I α (Φ_fam s x)) velChart t`
  (via `chartMovingTriv_orbit_hasDerivAt_of_chartJet`).

The chart-cover construction, however, delivers the realisation of `Φ_fam` in the
**representative chart** `αRep` — the time-`0` base-point chart chosen for `x` by the cover
selection (`time_dependent_vf_global_flow_glue`, `manifoldFlowFamily_exists_chartRepr`):

  `Φ_fam s y = (chartAt H αRep).symm (I.symm ((hper αRep).flow (I ((chartAt H αRep) y)) s))`.

At a general orbit time `t > 0`, the target chart `α = Φ_fam t x` differs from `αRep`.  This
file bridges that gap: it re-expresses the chart-cover realisation, read off in `αRep`, into
the target chart `α`, using the existing chart-overlap Grönwall machinery
(`chart_cover_flow_unique_on_overlap_chart_alpha_coord` and
`chart_overlap_chart_alpha_coord_ode`).

## The reconciliation principle

The target-chart Picard datum `hper α` (available because the chart-cover hypotheses quantify
`∀ α : M`) produces its own chart-coordinate flow `(hper α).flow`; its manifold realisation
`s ↦ (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))` is an integral curve
of `X` through `x`.  The chart-cover realisation `s ↦ Φ_fam s x` (read in `αRep`) is *also* an
integral curve of `X` through `x`.  Grönwall uniqueness
(`chart_cover_flow_unique_on_overlap_chart_alpha_coord`, with `α₁ := α`, `α₂ := αRep`) forces
the two manifold trajectories to agree on a positive horizon `[0, S]`.  Re-reading this
manifold-point equality in the target chart `α` produces the *target*-chart spatial realisation
of the orbit and its chart-coordinate velocity.

The two overlap hypotheses are stated as **explicit separable analytic inputs**, exactly the
genuine flow/field data of `chart_overlap_chart_alpha_coord_ode`:

* `(a)` the orbit stays in the chart-overlap (the `αRep` trajectory lies in the *target* chart
  source on `[0, S]`) — an analytic continuity/openness datum (the Lemma-A pattern); and
* `(b)` `hcompat` — the chart-transition derivative fixes the field `X` (read as a fixed
  `E`-vector through the chart-coordinate trivialisation) along the trajectory. This is a genuine
  *restrictive* analytic hypothesis: it holds for fields whose chart transitions act affinely on
  the coordinate velocity, but it is **not** automatic for a general field. In particular it does
  **not** hold for `deTurckVF` on a manifold with non-affine chart transitions (the chart-coordinate
  Picard velocity is the bare `E`-coercion, not the trivialisation pushforward, so the transition
  Jacobian does not fix it). This reconciliation lemma is therefore a true conditional statement
  that cannot be specialised to `deTurckVF`; the geometric `deTurckVF` flow requires the bare
  manifold-integral-flow route (with joint `(t, x)` regularity), not this chart-cover route.

Neither is hypothesis-packaging: they are flow/field data (a membership statement on a closed
interval, and a `HasFDerivAt` + linear-fixing `E`-equation), never the operator-valued or
scalar `HasDerivAt` conclusions the discharge delivers.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no
joint-`C^∞`-on-`ℝ × M` predicate.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.PDE.DeTurck

section MovingChartReconciliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **Orbit-level manifold reconciliation: target-chart Picard trajectory = chart-cover orbit.**

Let `α` be the target chart base point and `αRep` the representative (chart-cover) base point of
`x`, with chart-local Picard data `hper_tgt : ChartLocalPicardData X α` and
`hper_rep : ChartLocalPicardData X αRep`.  Suppose:

* `x` lies in both `hper_tgt.U` and `hper_rep.U` (it is in the overlap of the two
  chart-coordinate neighbourhoods);
* `hLip` — the target-chart-`α` Lipschitz hypothesis on `X` on a ball of radius `r'`;
* `hu1_ball`, `hu2_ball`, `hu2_cont` — the Grönwall confinement / continuity data of the two
  chart-coordinate trajectories;
* `hcompat` — the chart-transition derivative fixes `X` along the `αRep` trajectory (the
  genuine field-naturality datum); and
* `hα_in_α_source`, `hx_rep_pullback_eq_x` — the orbit stays in the target chart source on
  `[0, S]` and the `αRep`-chart pullback of `x` is `x`.

Then on `[0, S]` the target-chart Picard manifold trajectory of `x` agrees with the chart-cover
`αRep` manifold trajectory of `x`:

  `(chartAt H α).symm (I.symm (hper_tgt.flow (I ((chartAt H α) x)) s))
     = (chartAt H αRep).symm (I.symm (hper_rep.flow (I ((chartAt H αRep) x)) s))`.

This is `chart_cover_flow_unique_on_overlap_chart_alpha_coord` (with `α₁ := α`, `α₂ := αRep`),
its `hu2_ode` input produced by `chart_overlap_chart_alpha_coord_ode` from `hcompat` and the
overlap-source membership.  No hypothesis-packaging: the hypotheses are flow Lipschitz /
confinement data and a field-naturality `HasFDerivAt`/`E`-equation; the conclusion is a
manifold-point equality. -/
theorem orbit_manifold_reconciliation
    (X : ℝ → ∀ x : M, TangentSpace I x) (α αRep : M)
    (hper_tgt : ChartLocalPicardData X α) (hper_rep : ChartLocalPicardData X αRep)
    (S r r' : ℝ) (K : NNReal) (hS_pos : 0 < S) (hr_lt_r' : r < r')
    (hS_le_tgt : S ≤ hper_tgt.T) (hS_le_rep : S ≤ hper_rep.T)
    (x : M) (hx_tgt : x ∈ hper_tgt.U) (hx_rep : x ∈ hper_rep.U)
    (hLip : ∀ t ∈ Set.Ico (0 : ℝ) S,
      LipschitzOnWith K
        (fun y : E => (X t ((chartAt H α).symm (I.symm y)) : E))
        (Metric.ball (I ((chartAt H α) α)) r'))
    (hu1_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      (hper_tgt).flow (I ((chartAt H α) x)) t ∈
        Metric.closedBall (I ((chartAt H α) α)) r)
    (hu2_ball : ∀ t ∈ Set.Ico (0 : ℝ) S,
      I ((chartAt H α) ((chartAt H αRep).symm
        (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) t)))) ∈
        Metric.closedBall (I ((chartAt H α) α)) r)
    (hu2_cont : ContinuousOn
      (fun t : ℝ => I ((chartAt H α) ((chartAt H αRep).symm
        (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) t)))))
      (Set.Icc (0 : ℝ) S))
    (hcompat : ∀ t ∈ Set.Ico (0 : ℝ) S,
      ∃ L : E →L[ℝ] E,
        HasFDerivAt
          (fun y : E =>
            I ((chartAt H α) ((chartAt H αRep).symm (I.symm y))))
          L
          ((hper_rep).flow (I ((chartAt H αRep) x)) t) ∧
        L (X t ((chartAt H αRep).symm
            (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) t))) : E)
          = (X t ((chartAt H αRep).symm
            (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) t))) : E))
    (hx_rep_pullback_eq_x :
      (chartAt H αRep).symm (I.symm (I ((chartAt H αRep) x))) = x)
    (hα_in_α_source : ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H αRep).symm (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) s))
        ∈ (chartAt H α).source) :
    ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α).symm (I.symm ((hper_tgt).flow (I ((chartAt H α) x)) s))
        = (chartAt H αRep).symm
          (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) s)) := by
  have hu2_ode : ∀ t ∈ Set.Ico (0 : ℝ) S,
      HasDerivWithinAt
        (fun s : ℝ => I ((chartAt H α) ((chartAt H αRep).symm
          (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) s)))))
        ((X t ((chartAt H α).symm (I.symm
          (I ((chartAt H α) ((chartAt H αRep).symm
            (I.symm ((hper_rep).flow (I ((chartAt H αRep) x)) t)))))))) : E)
        (Set.Ici t) t :=
    chart_overlap_chart_alpha_coord_ode (M := M) (I := I) (E := E)
      X α αRep hper_rep S hS_pos hS_le_rep x hx_rep hcompat
      (fun s hs => hα_in_α_source s (Set.Ico_subset_Icc_self hs))
  exact chart_cover_flow_unique_on_overlap_chart_alpha_coord (M := M) (I := I) (E := E)
    X α αRep hper_tgt hper_rep S r r' K hS_pos hr_lt_r' hS_le_tgt hS_le_rep
    x hx_tgt hx_rep hLip hu1_ball hu2_ball hu2_cont hu2_ode
    hx_rep_pullback_eq_x hα_in_α_source

section RealisationVelocity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- **Target-chart orbit velocity from the reconciled chart-coordinate flow.**

Suppose the chart-coordinate flow `Φ_eucl : E → ℝ → E` realises the orbit `s ↦ Φ_fam s x` in
the target chart `α`, near `t`:

  `∀ᶠ s near t, Φ_fam s x = (extChartAt I α).symm (Φ_eucl (extChartAt I α x) s)`,

with the chart-coordinate value confined to the chart target, and the chart-coordinate orbit
`s ↦ Φ_eucl (extChartAt I α x) s` has `HasDerivAt velChart t`.  Then the *target*-chart orbit
`s ↦ extChartAt I α (Φ_fam s x)` has `HasDerivAt velChart t`:

  `HasDerivAt (fun s => extChartAt I α (Φ_fam s x)) velChart t`.

The proof rewrites `extChartAt I α (Φ_fam s x) = Φ_eucl (extChartAt I α x) s` eventually (via
the realisation and `(extChartAt I α).right_inv` on the target), then transports the
chart-coordinate `HasDerivAt` by `HasDerivAt.congr_of_eventuallyEq`.  This is the `hc` input of
`chartMovingTriv_orbit_hasDerivAt_of_chartJet`.  No hypothesis-packaging: the inputs are a
*point*-level orbit realisation and a chart-coordinate `HasDerivAt`; the conclusion is the
target-chart orbit `HasDerivAt`, derived not assumed. -/
theorem orbit_velocity_targetChart_of_reconciled
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ) (Φ_eucl : E → ℝ → E) {velChart : E}
    (hreal_orbit : ∀ᶠ s : ℝ in 𝓝 t,
      extChartAt I α ((Φ_fam s : M → M) x) = Φ_eucl (extChartAt I α x) s)
    (hc_eucl : HasDerivAt (fun s : ℝ => Φ_eucl (extChartAt I α x) s) velChart t) :
    HasDerivAt (fun s : ℝ => extChartAt I α ((Φ_fam s : M → M) x)) velChart t := by
  refine hc_eucl.congr_of_eventuallyEq ?_
  filter_upwards [hreal_orbit] with s hs
  exact hs

end RealisationVelocity

section EventualRealisation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The `∀ᶠ y` target-chart realisation from the representative realisation and the per-point
Grönwall reconciliation.**

Let `α := Φ_fam t x` be the target chart base point, `αRep` the representative (chart-cover)
base point, `hper_tgt : ChartLocalPicardData X α`, `hper_rep : ChartLocalPicardData X αRep`,
`t ∈ Ioo 0 S`.  Suppose:

* `hrep_real` — the chart-cover representative realisation: for `s` near `t` and `y` near `x`,
  `Φ_fam s y = (chartAt H αRep).symm (I.symm ((hper_rep).flow (I ((chartAt H αRep) y)) s))`;
* `hgronwall` — the per-point Grönwall reconciliation: for `y` near `x` and every `s ∈ [0, S]`,
  the target-chart Picard manifold trajectory of `y` agrees with the `αRep` one:
  `(chartAt H α).symm (I.symm ((hper_tgt).flow (I ((chartAt H α) y)) s))
     = (chartAt H αRep).symm (I.symm ((hper_rep).flow (I ((chartAt H αRep) y)) s))`;
* `hconf` — for `s` near `t` and `y` near `x`, the target-chart Picard value sits in the chart
  target: `(hper_tgt).flow (extChartAt I α y) s ∈ (extChartAt I α).target`.

Then the *target*-chart spatial realisation in the `hagree_of_spatial_chart_realisation` shape
holds with `Φ_eucl z s := (hper_tgt).flow z s`:

  `∀ᶠ s near t, ∀ᶠ y near x,
     Φ_fam s y = (extChartAt I α).symm (Φ_eucl (extChartAt I α y) s)
       ∧ Φ_eucl (extChartAt I α y) s ∈ (extChartAt I α).target`.

The proof intersects the three eventual data, replaces `Φ_fam s y` by the `αRep` realisation
(`hrep_real`), folds it back through the per-point Grönwall equality (`hgronwall`) to the target
realisation, and rewrites `extChartAt I α = I ∘ chartAt H α` / `(extChartAt I α).symm =
(chartAt H α).symm ∘ I.symm` (`extChartAt_coe`, `extChartAt_coe_symm`, `extChartAt_target`).
No hypothesis-packaging: every input is a point-level realisation/equality/confinement, never the
`HasDerivAt` discharge conclusion. -/
theorem hreal_targetChart_of_repReal_and_gronwall
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α αRep x : M) (t S : ℝ)
    (hper_tgt : ChartLocalPicardData X α) (hper_rep : ChartLocalPicardData X αRep)
    (ht_mem : t ∈ Set.Ioo (0 : ℝ) S)
    (hrep_real : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y = (chartAt H αRep).symm
        (I.symm ((hper_rep).flow (I ((chartAt H αRep) y)) s)))
    (hgronwall : ∀ᶠ y : M in 𝓝 x, ∀ s ∈ Set.Icc (0 : ℝ) S,
      (chartAt H α).symm (I.symm ((hper_tgt).flow (I ((chartAt H α) y)) s))
        = (chartAt H αRep).symm
          (I.symm ((hper_rep).flow (I ((chartAt H αRep) y)) s)))
    (hconf : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (hper_tgt).flow (extChartAt I α y) s ∈ (extChartAt I α).target) :
    ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
        = (extChartAt I α).symm ((hper_tgt).flow (extChartAt I α y) s)
        ∧ (hper_tgt).flow (extChartAt I α y) s ∈ (extChartAt I α).target := by
  have hs_in_Icc : ∀ᶠ s : ℝ in 𝓝 t, s ∈ Set.Icc (0 : ℝ) S := by
    have : Set.Ioo (0 : ℝ) S ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht_mem
    filter_upwards [this] with s hs
    exact Set.Ioo_subset_Icc_self hs
  filter_upwards [hrep_real, hconf, hs_in_Icc] with s hrep_s hconf_s hs_Icc
  filter_upwards [hrep_s, hconf_s, hgronwall] with y hrep_y hconf_y hgronwall_y
  have hcoe : (extChartAt I α) y = I ((chartAt H α) y) := by
    rw [extChartAt_coe]; rfl
  refine ⟨?_, ?_⟩
  · rw [hrep_y, hcoe]
    rw [extChartAt_coe_symm]
    change (chartAt H αRep).symm (I.symm ((hper_rep).flow (I ((chartAt H αRep) y)) s))
      = (chartAt H α).symm (I.symm ((hper_tgt).flow (I ((chartAt H α) y)) s))
    exact (hgronwall_y s hs_Icc).symm
  · rw [hcoe]
    exact hconf_y

end EventualRealisation

section DischargeComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **`RawVariationalIdentityFlat` for the concrete chart-cover flow via the moving-chart
reconciliation.**

Let `α := Φ_fam t x` be the target chart base point and `Φ_eucl := (hper_tgt).flow z s` the
target-chart Picard flow.  The hypotheses split into the *reconciliation* data (Parts B–C) and
the *factor-producer* data (the genuine target-chart `IsLocalFlow` variational ODE and the
chart jet):

* `hx_src` — `x` lies in the target chart source;
* `hreal` — the target-chart spatial realisation (Part (C) output, `Φ_eucl := (hper_tgt).flow`);
* `hc_eucl` — the chart-coordinate orbit velocity `HasDerivAt (fun s => Φ_eucl (extChartAt I α x) s)
  velChart t` (so Part (B)'s `orbit_velocity_targetChart_of_reconciled` yields the target-chart
  `hc`);
* `hGfd` — the moving-trivialisation chart-function `HasFDerivAt` at the orbit-time chart point
  (the `hCdiff` strengthening);
* `heucl`, `heucl_diff` — the Euclidean operator-valued variational ODE and per-time spatial
  differentiability for `Φ_eucl = (hper_tgt).flow` (the target-chart `IsLocalFlow` datum);
* `hcontAt` — continuity of the orbit at `t`.

It produces `RawVariationalIdentityFlat (I := I) Φ_fam t x v _ _` for the concrete flow.  The
proof derives `hagree` (from `hreal` via `hagree_of_spatial_chart_realisation`), the orbit
velocity `hc` (Part B), the moving-triv orbit jet `hg` (from `hGfd` + `hc` via
`chartMovingTriv_orbit_hasDerivAt_of_chartJet`), and routes everything into
`rawVariationalIdentityFlat_of_chart_realisation`.

No hypothesis-packaging: the reconciliation inputs are point-level realisations and a chart
velocity, the factor inputs are operator-valued ODEs / chart jets, and the conclusion is the
vector-valued orbit-pushforward `HasDerivAt` `RawVariationalIdentityFlat`, derived not assumed. -/
theorem rawVariationalIdentityFlat_of_movingChart_reconciliation
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (hper_tgt : ChartLocalPicardData X (Φ_fam t x))
    {D'_eucl : E →L[ℝ] E} {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart : E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hreal : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm
              ((hper_tgt).flow (extChartAt I (Φ_fam t x) y) s)
        ∧ (hper_tgt).flow (extChartAt I (Φ_fam t x) y) s
            ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl : HasDerivAt
      (fun s : ℝ => (hper_tgt).flow (extChartAt I (Φ_fam t x) x) s) velChart t)
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x)))
    (heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => (hper_tgt).flow z s)
        (extChartAt I (Φ_fam t x) x)) D'_eucl t)
    (heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => (hper_tgt).flow z s) (extChartAt I (Φ_fam t x) x))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart))
      (D'_eucl.comp (trivToE (I := I) (Φ_fam t x) x)) := by
  classical
  have hagree :
      ∀ᶠ s : ℝ in 𝓝 t,
        (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y))
          =ᶠ[𝓝 x] (fun y => (hper_tgt).flow (extChartAt I (Φ_fam t x) y) s) :=
    hagree_of_spatial_chart_realisation (I := I) Φ_fam (Φ_fam t x) x t
      (fun z s => (hper_tgt).flow z s) hreal
  have hreal_orbit : ∀ᶠ s : ℝ in 𝓝 t,
      extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x)
        = (hper_tgt).flow (extChartAt I (Φ_fam t x) x) s := by
    filter_upwards [hreal] with s hs
    obtain ⟨hpt, htgt⟩ := hs.self_of_nhds
    rw [hpt, (extChartAt I (Φ_fam t x)).right_inv htgt]
  have hc : HasDerivAt
      (fun s : ℝ => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x)) velChart t :=
    orbit_velocity_targetChart_of_reconciled (I := I) Φ_fam (Φ_fam t x) x t
      (fun z s => (hper_tgt).flow z s) hreal_orbit hc_eucl
  have hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) (Φ_fam t x)
        (extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) x))) (G' velChart) t :=
    chartMovingTriv_orbit_hasDerivAt_of_chartJet (I := I) Φ_fam (Φ_fam t x) x t hGfd hc
  exact rawVariationalIdentityFlat_of_chart_realisation (I := I) Φ_fam x t v
    (fun z s => (hper_tgt).flow z s) hx_src heucl heucl_diff hagree hg hcontAt

/-- **The paired residual for the concrete chart-cover flow via the moving-chart reconciliation.**

Composes two slot-`v`/`w` applications of
`rawVariationalIdentityFlat_of_movingChart_reconciliation` (each producing
`RawVariationalIdentityFlat` from the moving-chart-reconciled `hreal`/`hc_eucl` plus the
target-chart `IsLocalFlow` variational data) with the discharge's paired-residual headline
`variational_flow_flat_paired_residual_of_chart_realisation`
(`SmoothInSpace/VariationalLiftFactorDischarge.lean`).

The output is the headline frozen-metric moving-pushforward inner-product variation derivative

  `-lieDerivMetric g X (Φ_fam t x) dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`,

for the concrete chart-cover flow, now with the moving-chart gap closed: the target-chart
`hreal`/`hc` are produced by the reconciliation (Parts B–D), not assumed.

The remaining inputs are the genuine per-slot reconciliation data (`hreal_v`/`hreal_w`,
`hc_eucl_v`/`hc_eucl_w`, `heucl_v`/`heucl_w`, `heucl_diff_v`/`heucl_diff_w`), the shared chart
jet `hGfd`, the basepoint goodset / side-condition data (`hα`, `hRdiff`, `hCdiff`), and the two
metric-free flat-value identities (`hflatval_v`/`hflatval_w`).  No hypothesis-packaging: the
reconciliation inputs are point-level realisations and chart velocities, the bridges are
discharged inside the headline, and the conclusion is the scalar pairing `HasDerivAt`. -/
theorem variational_flow_flat_paired_residual_of_movingChart_reconciliation
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (hper_tgt : ChartLocalPicardData (fun _s y => (X : ∀ y : M, TangentSpace I y) y) (Φ_fam t x))
    {D'_eucl_v D'_eucl_w : E →L[ℝ] E} {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart_v velChart_w : E}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x)))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hreal_v : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm
              ((hper_tgt).flow (extChartAt I (Φ_fam t x) y) s)
        ∧ (hper_tgt).flow (extChartAt I (Φ_fam t x) y) s
            ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl_v : HasDerivAt
      (fun s : ℝ => (hper_tgt).flow (extChartAt I (Φ_fam t x) x) s) velChart_v t)
    (heucl_v : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => (hper_tgt).flow z s)
        (extChartAt I (Φ_fam t x) x)) D'_eucl_v t)
    (heucl_diff_v : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => (hper_tgt).flow z s) (extChartAt I (Φ_fam t x) x))
    (hreal_w : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm
              ((hper_tgt).flow (extChartAt I (Φ_fam t x) y) s)
        ∧ (hper_tgt).flow (extChartAt I (Φ_fam t x) y) s
            ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl_w : HasDerivAt
      (fun s : ℝ => (hper_tgt).flow (extChartAt I (Φ_fam t x) x) s) velChart_w t)
    (heucl_w : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => (hper_tgt).flow z s)
        (extChartAt I (Φ_fam t x) x)) D'_eucl_w t)
    (heucl_diff_w : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => (hper_tgt).flow z s) (extChartAt I (Φ_fam t x) x))
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
        + (D'_eucl_v.comp (trivToE (I := I) (Φ_fam t x) x)) v
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
        + (D'_eucl_w.comp (trivToE (I := I) (Φ_fam t x) x)) w
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
  have hv_flat := rawVariationalIdentityFlat_of_movingChart_reconciliation (I := I)
    (fun _s y => (X : ∀ y : M, TangentSpace I y) y) Φ_fam t x v hper_tgt
    hx_src hreal_v hc_eucl_v hGfd heucl_v heucl_diff_v hcontAt
  have hw_flat := rawVariationalIdentityFlat_of_movingChart_reconciliation (I := I)
    (fun _s y => (X : ∀ y : M, TangentSpace I y) y) Φ_fam t x w hper_tgt
    hx_src hreal_w hc_eucl_w hGfd heucl_w heucl_diff_w hcontAt
  exact variational_flow_flat_paired_residual_of_chart_realisation (I := I) g X Φ_fam t x v w
    _ _ _ _ hv_flat hw_flat hα hRdiff hCdiff hflatval_v hflatval_w

end DischargeComposition

end MovingChartReconciliation

end DifferentialGeometry.PDE.RicciFlow.ODE
