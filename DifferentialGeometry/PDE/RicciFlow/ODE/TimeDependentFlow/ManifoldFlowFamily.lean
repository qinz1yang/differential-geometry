import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.HartmanAssembly
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
## Time-indexed diffeomorphism family and chart-bridge manifold flow ODE

Given the chart-local Picard data assembled into the Hartman diffeomorphism
output `time_dependent_vf_flow_diffeomorph_on_closed_manifold`, we package the
per-time smooth diffeomorphisms into a single time-indexed family
`manifoldFlowFamily : ℝ → (M ≃ₘ⟮I, I⟯ M)` (a genuine `ℝ`-indexed family of
diffeomorphisms), with the identity at time `0`.

We also provide the **chart-bridge** that transports the chart-coordinate ODE
(`HasDerivWithinAt` of the chart-coordinate flow, the field `flow_spec` of
`ChartLocalPicardData`) to a manifold-level `HasMFDerivWithinAt` for the
time-curve `s ↦ Φ s x`. The manifold velocity is the chart pull-back of the
chart-coordinate velocity through `mfderivWithin (extChartAt I α).symm`,
evaluated at the current chart-coordinate position.

The bridge requires the chart-coordinate trajectory to remain inside the chart
target near the time in question: this confinement is supplied as an explicit,
separable hypothesis (a `𝓝[Set.Ici 0]` membership), never as a joint smoothness
assumption on `ℝ × M`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Bundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/--
**Chart-to-manifold ODE bridge.** Let `u : ℝ → E` be a chart-coordinate
trajectory with manifold realisation `s ↦ (extChartAt I α).symm (u s)`. If `u`
has the (one-sided) derivative `vel` at `t` within `Set.Ici 0`, its current
value `u t` lies in the chart target, and the trajectory stays inside
`range I` for times near `t` within `Set.Ici 0`, then the manifold curve has a
manifold derivative at `t` with velocity the chart pull-back of `vel` through
`mfderivWithin (extChartAt I α).symm (range I) (u t)`.

This is the converse of `IsMIntegralCurveOn.hasDerivWithinAt`: it lifts a
chart-coordinate `HasDerivWithinAt` to a manifold `HasMFDerivWithinAt`. The
velocity comes out in **transported** form — the chart pull-back of the
chart-coordinate velocity — because the chart `α` used to express the
trajectory is fixed and need not equal the current manifold point
`(extChartAt I α).symm (u t)`. The two coincide exactly when
`u t = extChartAt I α α`, where `mfderivWithin (extChartAt I α).symm` is the
identity.
-/
theorem chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
    (α : M) (u : ℝ → E) (s : Set ℝ) (t : ℝ) (vel : E)
    (htgt_t : u t ∈ (extChartAt I α).target)
    (hconf : u ⁻¹' (Set.range I) ∈ 𝓝[s] t)
    (hd : HasDerivWithinAt u vel s t) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s' : ℝ => (extChartAt I α).symm (u s')) s t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight vel)) := by
  set s' : Set ℝ := s ∩ u ⁻¹' (Set.range I) with hs'
  have hu_mf : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u s' t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight vel) := by
    have h0 : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) u s t
        ((ContinuousLinearMap.id ℝ ℝ).smulRight vel) :=
      (by simpa using hd.hasFDerivWithinAt :
        HasFDerivWithinAt u _ _ _).hasMFDerivWithinAt
    exact h0.mono Set.inter_subset_left
  have hsymm_mf : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm
      (Set.range I) (u t)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) :=
    (mdifferentiableWithinAt_extChartAt_symm htgt_t).hasMFDerivWithinAt
  have hcomp : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      ((extChartAt I α).symm ∘ u) s' t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I) (u t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight vel)) :=
    HasMFDerivWithinAt.comp t hsymm_mf hu_mf Set.inter_subset_right
  exact (hasMFDerivWithinAt_inter' (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f := (extChartAt I α).symm ∘ u) (s := s)
    (t := u ⁻¹' Set.range I) hconf).mp hcomp

/--
**Time-indexed diffeomorphism family from chart-local Picard data.**

Given per-base-point chart-local Picard data for `X` and `-X`, plus the
chart-overlap / per-chart-bijectivity inputs consumed by Hartman's assembly,
this produces a single time-indexed family of smooth diffeomorphisms
`Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` on a positive horizon `T`, together with a global
flow `Φ : ℝ → M → M` such that:

* `Φ_fam 0 = Diffeomorph.refl I M ∞` (the identity at time `0`);
* `Φ_fam t x = Φ t x` for every `t ∈ (0, T)` and every `x : M` (the family
  realises the global flow on the existence horizon);
* `Φ 0 x = x` for every `x : M` (the flow initial condition).

The family is the chosen Hartman diffeomorphism on `(0, T)` and the identity
diffeomorphism elsewhere (time `0` and outside the horizon). All choices use
`Classical.choice`, so the statement remains a pure existence theorem mirroring
the upstream Hartman existential.
-/
theorem manifoldFlowFamily_exists
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  obtain ⟨T, hT, Φ, hΦ_init, _hΦ_repr_simple, hdiffeo⟩ :=
    time_dependent_vf_flow_diffeomorph_on_closed_manifold X hper hperNeg
      hSmoothX_chart hSmoothNegX_chart hLocalFwd hLocalRev hBijPerChart
  refine ⟨T, hT, fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    Φ, ?_, hΦ_init, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x

/--
**Time-indexed diffeomorphism family with the chart-coordinate realization of the
flow exposed.**

Strengthens `manifoldFlowFamily_exists` by carrying, in the conclusion, the
chart-coordinate representation of the underlying global flow `Φ` (the
`hΦ_repr_simple` datum that the Hartman assembly establishes internally but the
plain existence statement discards):

* `Φ_fam 0 = Diffeomorph.refl I M ∞`;
* `Φ 0 x = x`;
* `Φ_fam t x = Φ t x` for `t ∈ (0, T)`;
* for every `x`, a representative chart `α` with
  `Φ s x = (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))`
  for all `s`;
* the combined chart realization of the *family* itself on `(0, T)`:
  `Φ_fam t x = (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) t))`,
  obtained by composing the agreement `Φ_fam t x = Φ t x` with the chart
  representation of `Φ`.

The last conjunct is the per-flow chart-reading datum a downstream
chart-coordinate variational connector consumes: it identifies the orbit
`s ↦ Φ_fam s x` (on the horizon) with the chart pull-back of the Picard
chart-coordinate flow, the form through which the `mfderiv`-in-chart dictionary
(`mfderiv_flow_eq_chartFderiv_apply`, `flow_orbit_eventually_mem_chartAt_source`,
`hagree_of_chartFderiv_witness`) reads the manifold pushforward.  All choices use
`Classical.choice`, so the statement remains a pure existence theorem. -/
theorem manifoldFlowFamily_exists_chartRepr
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hper : ∀ α : M, ChartLocalPicardData X α)
    (hperNeg : ∀ α : M, ChartLocalPicardData (fun t x => -(X t x)) α)
    (hSmoothX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      (X t ((chartAt H α).symm (I.symm y)) : E)))
    (hSmoothNegX_chart : ∀ α : M, ContDiff ℝ ∞ (Function.uncurry fun t y =>
      ((-X t ((chartAt H α).symm (I.symm y))) : E)))
    (hLocalFwd : ∀ (Φ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hper α).U ∧
        ∀ s : ℝ, Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Φ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hLocalRev : ∀ (Ψ : ℝ → M → M) (T : ℝ), 0 < T →
      (∀ x : M, ∃ α : M, x ∈ (hperNeg α).U ∧
        ∀ s : ℝ, Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ x : M, ∃ (ρ : ℝ) (_ : 0 < ρ) (flow : E → ℝ → E),
        ContDiffOn ℝ ∞ (Function.uncurry flow)
          (Metric.ball (I ((chartAt H x) x)) ρ ×ˢ Set.Ioo 0 T) ∧
        (∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ y ∈ (chartAt H x).source,
          I ((chartAt H x) y) ∈ Metric.ball (I ((chartAt H x) x)) ρ →
          Ψ s y = (chartAt H x).symm (I.symm (flow (I ((chartAt H x) y)) s))) ∧
        (∀ t ∈ Set.Ioo (0 : ℝ) T,
          I.symm (flow (I ((chartAt H x) x)) t) ∈ (chartAt H x).target))
    (hBijPerChart : ∀ (Φ Ψ : ℝ → M → M),
      (∀ x, Φ 0 x = x) → (∀ x, Ψ 0 x = x) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Φ s x = (chartAt H α).symm
          (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) →
      (∀ x : M, ∃ α : M, ∀ s : ℝ,
        Ψ s x = (chartAt H α).symm
          (I.symm ((hperNeg α).flow (I ((chartAt H α) x)) s))) →
      ∀ α : M,
        ∃ S_α : ℝ, 0 < S_α ∧
          ∀ x ∈ (hper α).U ∩ (hperNeg α).U,
            ∀ s ∈ Set.Ico (0 : ℝ) S_α,
              Ψ s (Φ s x) = x ∧ Φ s (Ψ s x) = x) :
    ∃ (T : ℝ) (_ : 0 < T) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M),
        Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
        (∀ x : M, Φ 0 x = x) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) ∧
        (∀ x : M, ∃ α : M, ∀ s : ℝ,
          Φ s x = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) s))) ∧
        (∀ t : ℝ, 0 < t → t < T → ∀ x : M, ∃ α : M,
          (Φ_fam t x : M) = (chartAt H α).symm
            (I.symm ((hper α).flow (I ((chartAt H α) x)) t))) := by
  classical
  obtain ⟨T, hT, Φ, hΦ_init, hΦ_repr_simple, hdiffeo⟩ :=
    time_dependent_vf_flow_diffeomorph_on_closed_manifold X hper hperNeg
      hSmoothX_chart hSmoothNegX_chart hLocalFwd hLocalRev hBijPerChart
  refine ⟨T, hT, fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    Φ, ?_, hΦ_init, ?_, hΦ_repr_simple, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x
  · intro t ht htT x
    obtain ⟨α, hαrepr⟩ := hΦ_repr_simple x
    refine ⟨α, ?_⟩
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    have hfam_eq : ((if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose
        else Diffeomorph.refl I M ∞ : M ≃ₘ⟮I, I⟯ M) : M → M) x = Φ t x := by
      simp only [hguard, dif_pos, and_self]
      exact (hdiffeo t ht htT).choose_spec x
    rw [hfam_eq, hαrepr t]

/--
**Manifold flow ODE for a chart-α-represented flow.**

Let `Φ : ℝ → M → M` be a flow whose value at a base point `x` is realised
through a fixed chart `α` by the chart-coordinate flow of `ChartLocalPicardData`
for `X` at `α`, i.e. `Φ s x = (chartAt H α).symm (I.symm (flow y s))` with
`y = I ((chartAt H α) x)`. The `flow_spec` field of the Picard data supplies the
chart-coordinate ODE `HasDerivWithinAt (flow y) (X t (Φ t x)) (Icc 0 T) t`.

Provided the chart-coordinate trajectory `flow y` stays inside `range I` for
times near `t` within `Icc 0 T` (a separable confinement hypothesis, never joint
`C^∞` on `ℝ × M`) and its current value lies in the chart target, the time-curve
`s ↦ Φ s x` has a **manifold** derivative at `t`:
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (s ↦ Φ s x) (Icc 0 T) t (𝟙.smulRight (vel t x))`,
where the manifold velocity `vel t x` is the chart pull-back of `X t (Φ t x)`
through `mfderivWithin (extChartAt I α).symm (range I) (flow y t)`.

This is the honest chart-bridge: it transports the chart-coordinate ODE
`flow_spec` to the manifold without assuming the chart `α` is the current
manifold point. The velocity carries the change-of-coordinates derivative; it
equals the geometric `X t (Φ t x)` exactly at chart-coordinate positions where
`mfderivWithin (extChartAt I α).symm` is the identity (e.g. `Φ t x = α`).
-/
theorem manifoldFlow_hasMFDerivWithinAt_of_chartLocal
    (X : ℝ → ∀ x : M, TangentSpace I x) (α x : M)
    (hper : ChartLocalPicardData X α)
    (hxU : x ∈ hper.U)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) hper.T)
    (hconf : (hper.flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) hper.T] t)
    (htgt_t :
      hper.flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => (chartAt H α).symm
        (I.symm (hper.flow (I ((chartAt H α) x)) s)))
      (Set.Icc 0 hper.T) t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
          (hper.flow (I ((chartAt H α) x)) t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight
          (X t ((chartAt H α).symm
            (I.symm (hper.flow (I ((chartAt H α) x)) t)))))) := by
  set y : E := I ((chartAt H α) x) with hy
  set u : ℝ → E := hper.flow y with hu
  have hball : y ∈ Metric.closedBall (I ((chartAt H α) α)) hper.r :=
    picard_data_chart_coord_in_closedBall X α hper x hxU
  obtain ⟨_hinit, hode⟩ := hper.flow_spec y hball
  have hd : HasDerivWithinAt u
      (X t ((chartAt H α).symm (I.symm (u t))))
      (Set.Icc (0 : ℝ) hper.T) t := hode t ht
  have hrealise : (fun s : ℝ => (chartAt H α).symm (I.symm (u s))) =
      fun s : ℝ => (extChartAt I α).symm (u s) := by
    funext s; rw [extChartAt_coe_symm]; rfl
  rw [hrealise]
  exact chartCoord_hasDerivWithinAt_to_manifold_hasMFDerivWithinAt
    (I := I) α u (Set.Icc 0 hper.T) t
    (X t ((chartAt H α).symm (I.symm (u t)))) htgt_t hconf hd

end DifferentialGeometry.PDE.RicciFlow.ODE
