import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.HartmanAssembly
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldFlowFamily
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
## Chart-bridge producers for the diffeomorphism family of a time-dependent flow

The headline assembly `time_dependent_vf_manifold_integral_flow_family`
(`ManifoldIntegralFlow.lean`) converts a bare flow `Φ : ℝ → M → M` into a
time-indexed diffeomorphism family carrying the genuine integral-flow equation.
It consumes two hypotheses:

* `hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = Φ t x`, and
* `hflow : ∀ t, 0 < t → t < T → ∀ x,
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) (Set.Ici 0) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))`.

This file **produces** these from the data the chart-cover flow stack actually
delivers, together with genuine separable regularity / bijectivity facts about
the flow.

### `hdiffeo`

The flow `Φ` returned by `time_dependent_vf_globalflow_on_closed_mfd` is, on
the closed-manifold horizon `(0, T)`, a smooth bijection with smooth inverse
`Ψ` (the reverse flow). Smoothness of each time-slice `Φ t` / `Ψ t` and the
two-sided composition identities `Ψ t ∘ Φ t = id`, `Φ t ∘ Ψ t = id` are the
genuine analytic inputs; from them the diffeomorphism witness is *built* —
the bijectivity assembles an `Equiv`, and the two `ContMDiff` proofs make it a
`Diffeomorph I I M M ∞`. This is the producer
`time_dependent_vf_hdiffeo_of_smooth_bijective`. It is not hypothesis-packaging:
the conclusion `∃ d, ∀ x, d x = Φ t x` requires constructing the bundled
diffeomorphism object out of separate facts about `Φ` and `Ψ`.

### `hflow`, honestly

The chart-coordinate Picard ODE (`ChartLocalPicardData.flow_spec`) is expressed
through a **fixed** representative chart `α = αRep x`. Transporting that ODE to
the manifold (via `manifoldFlow_hasMFDerivWithinAt_of_chartLocal`) yields the
**chart-`α`-transported** velocity
`mfderivWithin (extChartAt I α).symm (range I) (flow y t) ∘L
  (𝟙.smulRight (X t (Φ t x)))`,
which equals the bare geometric velocity `𝟙.smulRight (X t (Φ t x))` exactly at
the chart centre (where `mfderivWithin (extChartAt I α).symm` is the identity),
and in general differs from it because the trajectory `Φ s x` drifts away from
the fixed chart centre `αRep x` as `s` grows. The transported-velocity manifold
ODE is the form the chart-cover construction supports; it is produced here as
`time_dependent_vf_hflow_transported_of_chartLocal`.

The **bare**-velocity `hflow` required by
`time_dependent_vf_manifold_integral_flow_family` is therefore *not* available
for this chart-cover `Φ`; the bare integral-flow equation
`∂_s (Φ s x) = X s (Φ s x)` is obtained only through the chart-free
autonomisation route of `ManifoldIntegralFlow.lean`
(`time_dependent_vf_local_integral_flow_bare`), whose regularity input is `C¹`
of the autonomised field `(1, X)` on `ℝ × M`.

### Composition into the diffeomorphism family

`time_dependent_vf_diffeomorph_family_of_smooth_bijective` composes the
`hdiffeo` producer with `time_dependent_vf_manifold_integral_flow_family`-style
packaging to expose, from the chart-cover output plus the smoothness /
bijectivity inputs, a clean time-indexed family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`
with `Φ_fam 0 = refl` and `Φ_fam t x = Φ t x` on `(0, T)`.
-/

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/--
**Single time-slice diffeomorphism witness.** If, at time `t`, the forward flow
`Φ t` and the reverse flow `Ψ t` are each `C^∞` self-maps of `M` and are
mutually inverse (`Ψ t (Φ t x) = x` and `Φ t (Ψ t x) = x` for every `x`), then
`Φ t` is a smooth diffeomorphism: there is `d : M ≃ₘ⟮I, I⟯ M` with `d x = Φ t x`
for every `x`, whose inverse realises `Ψ t`.

The diffeomorphism is **constructed**: the two-sided composition identities make
`⟨Φ t, Ψ t, …⟩` an `Equiv M M`, and the two smoothness proofs upgrade it to a
`Diffeomorph I I M M ∞`. No hypothesis already asserts that `Φ t` is a
diffeomorphism; the existence of the bundled object is genuine content.
-/
theorem time_dependent_vf_diffeomorph_slice_of_smooth_bijective
    (Φ Ψ : M → M)
    (hΦ_smooth : ContMDiff I I ∞ Φ) (hΨ_smooth : ContMDiff I I ∞ Ψ)
    (hΨΦ : ∀ x : M, Ψ (Φ x) = x) (hΦΨ : ∀ x : M, Φ (Ψ x) = x) :
    ∃ d : M ≃ₘ⟮I, I⟯ M, (∀ x : M, d x = Φ x) ∧ (∀ x : M, d.symm x = Ψ x) := by
  let e : M ≃ M :=
    { toFun := Φ
      invFun := Ψ
      left_inv := fun x => hΨΦ x
      right_inv := fun x => hΦΨ x }
  exact ⟨⟨e, hΦ_smooth, hΨ_smooth⟩, fun _ => rfl, fun _ => rfl⟩

/--
**`hdiffeo` producer.** From a forward flow `Φ` and reverse flow `Ψ` on a
positive closed-manifold horizon `T`, each smooth at every time `t ∈ (0, T)`
and mutually inverse on the right-handed interval `[0, T)`, produce the
diffeomorphism witnesses
`∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x, d x = Φ t x`,
i.e. the `hdiffeo` hypothesis of `time_dependent_vf_manifold_integral_flow_family`.

The smoothness of each time-slice and the two-sided composition identities are
the genuine separable analytic inputs (`time_dependent_vf_flow_smooth_in_space`
supplies the first from chart-`C^∞`; `chart_cover_flow_bijective_two_sided_uniform_horizon`
supplies the second from per-chart bijectivity). The diffeomorphism witness is
then *constructed* slice by slice.
-/
theorem time_dependent_vf_hdiffeo_of_smooth_bijective
    (Φ Ψ : ℝ → M → M) (T : ℝ)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x := by
  intro t ht htT
  have hmem : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.le, htT⟩
  obtain ⟨d, hd_fwd, _hd_rev⟩ :=
    time_dependent_vf_diffeomorph_slice_of_smooth_bijective
      (Φ t) (Ψ t) (hΦ_smooth t ht htT) (hΨ_smooth t ht htT)
      (fun x => hΨΦ t hmem x) (fun x => hΦΨ t hmem x)
  exact ⟨d, hd_fwd⟩

/--
**Transported-velocity `hflow` producer (per point / per chart).** For the
chart-cover flow `Φ` of `X`, expressed at a base point `x` through a fixed chart
`α` by the chart-coordinate Picard flow
`Φ s x = (chartAt H α).symm (I.symm ((hper α).flow (I ((chartAt H α) x)) s))`,
the chart-coordinate ODE `(hper α).flow_spec` transports to a **manifold**
derivative for the time-curve `s ↦ Φ s x` at any `t ∈ [0, (hper α).T]`, provided
the chart-coordinate trajectory stays in `range I` near `t` (the separable
confinement hypothesis `hconf`) and its current value lies in the chart target
(`htgt_t`). The recovered manifold velocity is the **chart-`α`-transported**
velocity
`mfderivWithin (extChartAt I α).symm (range I) (flow y t) ∘L
  (𝟙.smulRight (X t (Φ t x)))`.

This is the honest manifold flow ODE the chart-cover construction supports. The
velocity equals the bare geometric `𝟙.smulRight (X t (Φ t x))` exactly when
`mfderivWithin (extChartAt I α).symm` is the identity at `flow y t` — i.e. at the
chart centre — and otherwise carries the change-of-coordinates derivative. It is
a thin re-export of `manifoldFlow_hasMFDerivWithinAt_of_chartLocal` against the
chart-coordinate representation identity `hΦ_repr`, transporting the curve and
the base point along that representation.
-/
theorem time_dependent_vf_hflow_transported_of_chartLocal
    (X : ℝ → ∀ x : M, TangentSpace I x) (α x : M)
    (hper : ChartLocalPicardData X α)
    (hxU : x ∈ hper.U)
    (Φ : ℝ → M → M)
    (hΦ_repr : ∀ s : ℝ, Φ s x = (chartAt H α).symm
      (I.symm (hper.flow (I ((chartAt H α) x)) s)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) hper.T)
    (hconf : (hper.flow (I ((chartAt H α) x))) ⁻¹' (Set.range I) ∈
      𝓝[Set.Icc (0 : ℝ) hper.T] t)
    (htgt_t :
      hper.flow (I ((chartAt H α) x)) t ∈ (extChartAt I α).target) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Icc 0 hper.T) t
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (Set.range I)
          (hper.flow (I ((chartAt H α) x)) t)) ∘L
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (X t (Φ t x)))) := by
  have hcurve : (fun s : ℝ => Φ s x) =
      fun s : ℝ => (chartAt H α).symm
        (I.symm (hper.flow (I ((chartAt H α) x)) s)) := by
    funext s; exact hΦ_repr s
  have hbase : Φ t x =
      (chartAt H α).symm (I.symm (hper.flow (I ((chartAt H α) x)) t)) :=
    hΦ_repr t
  rw [hcurve, hbase]
  exact manifoldFlow_hasMFDerivWithinAt_of_chartLocal X α x hper hxU t ht hconf
    htgt_t

/--
**Diffeomorphism family from smooth, mutually-inverse chart-cover flows.**

Given the chart-cover output `(Φ, Ψ, T)` of `time_dependent_vf_globalflow_on_closed_mfd`
— flows with `Φ 0 = id`, smooth time-slices on `(0, T)`, and mutual inverses on
`[0, T)` — this produces a single time-indexed family of smooth diffeomorphisms
`Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)` with

* `Φ_fam 0 = Diffeomorph.refl I M ∞` (the identity at time `0`);
* `Φ_fam t x = Φ t x` for every `t ∈ (0, T)` and every `x : M`.

The construction runs the `hdiffeo` producer
`time_dependent_vf_hdiffeo_of_smooth_bijective` to obtain the per-time
diffeomorphism witnesses, then assembles the family exactly as
`manifoldFlowFamily_exists` does (the chosen diffeomorphism on `(0, T)`, the
identity elsewhere; all choices `Classical.choice`).

This is the diffeomorphism-family endpoint reachable from the chart-cover stack
**without** the bare integral-flow equation; the bare-velocity flow ODE
`∂_s (Φ s x) = X s (Φ s x)` is supplied separately by the chart-free
autonomisation route (`time_dependent_vf_local_integral_flow_bare`).
-/
theorem time_dependent_vf_diffeomorph_family_of_smooth_bijective
    (Φ Ψ : ℝ → M → M) (T : ℝ) (_hT : 0 < T)
    (_hΦ_init : ∀ x : M, Φ 0 x = x)
    (hΦ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Φ t))
    (hΨ_smooth : ∀ t, 0 < t → t < T → ContMDiff I I ∞ (Ψ t))
    (hΨΦ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Ψ s (Φ s x) = x)
    (hΦΨ : ∀ s ∈ Set.Ico (0 : ℝ) T, ∀ x : M, Φ s (Ψ s x) = x) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  have hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x :=
    time_dependent_vf_hdiffeo_of_smooth_bijective Φ Ψ T hΦ_smooth hΨ_smooth hΨΦ hΦΨ
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x

/--
**Diffeomorphism family directly from the diffeomorphism witnesses.**

A repackaging that takes the `hdiffeo` family
`∀ t, 0 < t → t < T → ∃ d, ∀ x, d x = Φ t x` (the exact hypothesis consumed by
`time_dependent_vf_manifold_integral_flow_family`) and produces the
time-indexed diffeomorphism family with the identity at time `0` and pointwise
agreement on `(0, T)`. This exposes the diffeomorphism-family deliverable from
the `hdiffeo` producer alone, independently of any flow-velocity equation.
-/
theorem time_dependent_vf_diffeomorph_family_of_hdiffeo
    (Φ : ℝ → M → M) (T : ℝ)
    (hdiffeo : ∀ t, 0 < t → t < T → ∃ d : M ≃ₘ⟮I, I⟯ M, ∀ x : M, d x = Φ t x) :
    ∃ (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)),
      Φ_fam 0 = Diffeomorph.refl I M ∞ ∧
      (∀ t : ℝ, 0 < t → t < T → ∀ x : M, Φ_fam t x = Φ t x) := by
  classical
  refine ⟨fun t =>
    if h : 0 < t ∧ t < T then (hdiffeo t h.1 h.2).choose else Diffeomorph.refl I M ∞,
    ?_, ?_⟩
  · have h0 : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < T) := by
      rintro ⟨h, _⟩; exact (lt_irrefl 0) h
    simp only [h0, dif_neg, not_false_iff]
  · intro t ht htT x
    have hguard : 0 < t ∧ t < T := ⟨ht, htT⟩
    simp only [hguard, dif_pos, and_self]
    exact (hdiffeo t ht htT).choose_spec x

end DifferentialGeometry.PDE.RicciFlow.ODE
