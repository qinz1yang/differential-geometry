import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFactorDischarge
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.ForwardIntegralCurveUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.Manifold
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.Analysis.ODE.FlowC1

/-!
# Moving-chart-local discharge of the chart-realised factor inputs at an interior time

The factor-producer discharge `rawVariationalIdentityFlat_of_chart_realisation`
(`SmoothInSpace/VariationalLiftFactorDischarge.lean`) consumes, in the *target* chart
`α := Φ_fam t x` (the orbit point at the interior time `t`), five data that are all **local
near `t`**:

* `heucl` / `heucl_diff` — the Euclidean operator-valued variational ODE and per-time spatial
  differentiability of a chart-coordinate flow `Φ_eucl : E → ℝ → E`;
* `hagree` — the eventual spatial chart-conjugation
  `∀ᶠ s near t, extChartAt I α (Φ_fam s ·) =ᶠ[𝓝 x] Φ_eucl (extChartAt I α ·) s`;
* `hg` — the moving-trivialisation orbit jet; and
* `hcontAt` — orbit continuity at `t`.

This file supplies those five data from the genuine *local-near-`t`* regularity of the flow,
**without** confining the whole orbit `{Φ_fam s x : s ∈ [0, t]}` to the single chart `α`.

## The flow-cocycle chart reading

The orbit of `Φ_fam` through a spatial point `y` is `s ↦ Φ_fam s y`, whose value at the
*interior* time `t` is `Φ_fam t y` (not `y`).  The local flow near `(t, α)` — the time-`t`
centred local flow `Ψ` of the bare field `X` (delivered by
`h3_local_flow_jointSmooth_and_integralCurve` at `t₀ := t`, `p₀ := α`, read in the chart `α`
as the time-`t` centred Euclidean Picard flow `ΦE` with `ΦE(·, t) = id`) — reproduces the orbit
*forward from time `t`*:

  `Φ_fam s y = Ψ s (Φ_fam t y)`   for `(s, y)` near `(t, x)`,

by forward integral-curve uniqueness (`bare_forward_flow_eqOn_of_jointC1`): both
`s ↦ Φ_fam s y` and `s ↦ Ψ s (Φ_fam t y)` solve the bare ODE of `X` and agree at `s = t`
(`Ψ t (Φ_fam t y) = Φ_fam t y`).  Reading this in the chart `α`,

  `extChartAt I α (Φ_fam s y) = ΦE (extChartAt I α (Φ_fam t y), s)`,

so the consumer's chart-coordinate flow is the time-`t` centred Picard flow **precomposed** with
the *fixed* (`s`-independent) chart reading of the time-`t` map `Φ_fam t`:

  `Φ_eucl z s := ΦE (extChartAt I α (Φ_fam t ((extChartAt I α).symm z)), s)`.

Because `ΦE` is centred at the interior time `t` (so `ΦE(·, t) = id`), no whole-orbit
confinement is needed: the realisation holds for `s` near `t` (where the orbit stays near `α`
by continuity) and the precomposition `z ↦ extChartAt I α (Φ_fam t ((extChartAt I α).symm z))`
is a *fixed* spatial diffeomorphism reading, never an orbit constraint.

The two genuine, separable, local-near-`t` hypotheses that survive are:

* `hΦE` / `hf` / `hΦsmooth` — the chart-`α` time-`t` centred Euclidean Picard flow of a globally
  `C^∞` field `f`, jointly `C^∞` on an interior box.  This is exactly the parabolic-regularity
  (gap-II) output: the solution metric is jointly smooth, hence the bare field is jointly smooth,
  hence its local flow near the interior `(t, α)` is a jointly-`C^∞` Picard flow.  It is an
  analytic regularity datum on the model space.
* `hrealΨ` — the *local-near-`t`* cocycle realisation: a point-level equality of manifold points
  `Φ_fam s y = (extChartAt I α).symm (ΦE (extChartAt I α (Φ_fam t y), s))` valid for `(s, y)`
  near `(t, x)`, with the chart-coordinate value confined to the chart target.  It is the genuine
  geometric datum the local flow makes available; it is a point-level equality of manifold points,
  distinct from the operator-valued / scalar `HasDerivAt` discharge conclusion.

The realisation constrains the orbit only for `s` near the interior time `t`, where the Picard flow
`ΦE` is centred (`ΦE(·, t) = id`); the precomposition `z ↦ extChartAt I α (Φ_fam t ((extChartAt I α).symm z))`
is a fixed spatial diffeomorphism reading, independent of `s`.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff NNReal
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.ODE.Flow

section LocalChartDischarge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- The chart reading of the time-`t` map `Φ_fam t`, as a map of model-space coordinates:
`precompMap Φ_fam t α z := extChartAt I α (Φ_fam t ((extChartAt I α).symm z))`. -/
def precompMap (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (α : M) (z : E) : E :=
  extChartAt I α ((Φ_fam t : M → M) ((extChartAt I α).symm z))

/-- The consumer's chart-coordinate flow built from the time-`t` centred Picard flow `ΦE` and the
fixed precomposition: `Φ_euclLocal ΦE Φ_fam t α z s := ΦE (precompMap Φ_fam t α z, s)`. -/
def Φ_euclLocal (ΦE : E × ℝ → E) (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (α : M)
    (z : E) (s : ℝ) : E :=
  ΦE (precompMap (I := I) Φ_fam t α z, s)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- The precomposition sends the chart point of `x` to the chart point of the orbit point `α`:
`precompMap Φ_fam t α (extChartAt I α x) = extChartAt I α (Φ_fam t x)`, provided `x` lies in the
chart source of `α` (so the chart round-trip cancels). -/
theorem precompMap_chartPoint
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (α x : M)
    (hx_src : x ∈ (extChartAt I α).source) :
    precompMap (I := I) Φ_fam t α (extChartAt I α x)
      = extChartAt I α ((Φ_fam t : M → M) x) := by
  unfold precompMap
  rw [(extChartAt I α).left_inv hx_src]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
/-- **`hagree` from the local-near-`t` cocycle realisation.**

For the consumer's chart-coordinate flow `Φ_euclLocal ΦE Φ_fam t α`, the eventual spatial
chart-conjugation equality holds, derived from the point-level cocycle realisation `hrealΨ`. -/
theorem hagree_of_cocycle_realisation
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ) (ΦE : E × ℝ → E)
    (hrealΨ : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I α).symm (ΦE (extChartAt I α ((Φ_fam t : M → M) y), s))
        ∧ ΦE (extChartAt I α ((Φ_fam t : M → M) y), s) ∈ (extChartAt I α).target)
    (hsrc_nhds : ∀ᶠ y : M in 𝓝 x, y ∈ (extChartAt I α).source) :
    ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_euclLocal (I := I) ΦE Φ_fam t α (extChartAt I α y) s) := by
  filter_upwards [hrealΨ] with s hs
  filter_upwards [hs, hsrc_nhds] with y hy hysrc
  obtain ⟨hpt, htgt⟩ := hy
  rw [hpt, (extChartAt I α).right_inv htgt]
  unfold Φ_euclLocal
  rw [precompMap_chartPoint (I := I) Φ_fam t α y hysrc]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **Operator-valued `HasDerivAt` through a fixed continuous-linear post-composition on the
right.**  (Local copy specialised to model space `E`; mirrors `hasDerivAt_clm_comp_right`.) -/
theorem hasDerivAt_clm_comp_right_local
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (R : E →L[ℝ] E) :
    HasDerivAt (fun s : ℝ => (A s).comp R) (A'.comp R) t := by
  have hcompR : HasFDerivAt (fun L : E →L[ℝ] E => L.comp R)
      ((ContinuousLinearMap.compL ℝ E E E).flip R) (A t) :=
    ((ContinuousLinearMap.compL ℝ E E E).flip R).hasFDerivAt
  simpa using hcompR.comp_hasDerivAt t hA

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **Spatial-fderiv factorisation of the precomposed flow.**

For `Φ_euclLocal ΦE Φ_fam t α z s = ΦE (precompMap z, s)`, with `ΦE (·, s)` differentiable at
`precompMap z₀` and `precompMap` differentiable at `z₀`, the spatial Fréchet derivative factors as
the Picard spatial derivative at `precompMap z₀` post-composed (on the right) with the fixed
precomposition derivative. -/
theorem spatial_fderiv_precomp_factor
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α : M) (t s : ℝ) (ΦE : E × ℝ → E) (z₀ : E)
    (hΦE_diff : DifferentiableAt ℝ (fun w => ΦE (w, s)) (precompMap (I := I) Φ_fam t α z₀))
    (hprecomp_diff : DifferentiableAt ℝ (precompMap (I := I) Φ_fam t α) z₀) :
    fderiv ℝ (fun z => Φ_euclLocal (I := I) ΦE Φ_fam t α z s) z₀
      = (fderiv ℝ (fun w => ΦE (w, s)) (precompMap (I := I) Φ_fam t α z₀)).comp
          (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀) := by
  have hcomp : (fun z => Φ_euclLocal (I := I) ΦE Φ_fam t α z s)
      = (fun w => ΦE (w, s)) ∘ (precompMap (I := I) Φ_fam t α) := rfl
  rw [hcomp, fderiv_comp z₀ hΦE_diff hprecomp_diff]

omit [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **`heucl` for the precomposed chart-coordinate flow.**

For the time-`t` centred chart-`α` Euclidean Picard flow `ΦE` of a globally `C^∞` field `f`,
jointly `C^∞` on an open box `U`, precomposed with the fixed reading `precompMap`, the spatial
Fréchet-derivative curve carries the operator-valued variational `HasDerivAt` at the chart
coordinate `z₀ := extChartAt I α x`, with value the Picard variational derivative at
`precompMap z₀` post-composed with the fixed precomposition derivative. -/
theorem heucl_precomp
    {f : ℝ → E → E} {t : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {ΦE : E × ℝ → E}
    (hΦE : IsLocalFlow f t x₀ r tmin tmax ΦE)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ ΦE U)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M)
    (hprecomp_smooth : DifferentiableAt ℝ (precompMap (I := I) Φ_fam t α)
      (extChartAt I α x))
    (hzsU : (precompMap (I := I) Φ_fam t α (extChartAt I α x), t) ∈ U)
    (hz : precompMap (I := I) Φ_fam t α (extChartAt I α x) ∈ Metric.ball x₀ r)
    (ht : t ∈ Ioo tmin tmax)
    (hΦsmooth_time : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun w => ΦE (w, s))
        (precompMap (I := I) Φ_fam t α (extChartAt I α x))) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ
        (fun z => Φ_euclLocal (I := I) ΦE Φ_fam t α z s) (extChartAt I α x))
      (((fderiv ℝ (f t) (ΦE (precompMap (I := I) Φ_fam t α (extChartAt I α x), t))).comp
          (fderiv ℝ (fun w => ΦE (w, t))
            (precompMap (I := I) Φ_fam t α (extChartAt I α x)))).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t α) (extChartAt I α x))) t := by
  set z₀ : E := extChartAt I α x with hz₀
  set w₀ : E := precompMap (I := I) Φ_fam t α z₀ with hw₀
  have hPicard : HasDerivAt (fun s : ℝ => fderiv ℝ (fun w => ΦE (w, s)) w₀)
      ((fderiv ℝ (f t) (ΦE (w₀, t))).comp (fderiv ℝ (fun w => ΦE (w, t)) w₀)) t :=
    IsLocalFlow.hasDerivAt_partial_spatial_fderiv hΦE hf hUopen hΦsmooth hzsU hz ht
  have hpost : HasDerivAt
      (fun s : ℝ => (fderiv ℝ (fun w => ΦE (w, s)) w₀).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀))
      (((fderiv ℝ (f t) (ΦE (w₀, t))).comp (fderiv ℝ (fun w => ΦE (w, t)) w₀)).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀)) t :=
    hasDerivAt_clm_comp_right_local hPicard
      (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀)
  have hev : (fun s : ℝ => fderiv ℝ
        (fun z => Φ_euclLocal (I := I) ΦE Φ_fam t α z s) z₀)
      =ᶠ[𝓝 t] (fun s : ℝ => (fderiv ℝ (fun w => ΦE (w, s)) w₀).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀)) := by
    filter_upwards [hΦsmooth_time] with s hsd
    exact spatial_fderiv_precomp_factor (I := I) Φ_fam α t s ΦE z₀ hsd hprecomp_smooth
  exact hpost.congr_of_eventuallyEq hev

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] in
/-- **`precompMap` is differentiable at the chart point of a source point.**

`precompMap = extChartAt I α ∘ Φ_fam t ∘ (extChartAt I α).symm`; read as a chart-coordinate map
it is `MDifferentiableWithinAt 𝓘(ℝ,E) 𝓘(ℝ,E) … (range I)`, and since `M` is boundaryless
(`I.Boundaryless`) `range I = univ`, so this is full `MDifferentiableAt`, i.e. Fréchet
differentiability of the model-space map. -/
theorem precompMap_differentiableAt
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (α x : M)
    (hx_src : x ∈ (extChartAt I α).source)
    (hΦtx_src : (Φ_fam t : M → M) x ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (precompMap (I := I) Φ_fam t α) (extChartAt I α x) := by
  set z₀ : E := extChartAt I α x with hz₀
  have hrange : (range I) = (univ : Set E) := I.range_eq_univ
  have htgt : z₀ ∈ (extChartAt I α).target := by
    rw [hz₀]; exact (extChartAt I α).map_source hx_src
  have hsymm : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z₀ :=
    mdifferentiableWithinAt_extChartAt_symm htgt
  have hround : (extChartAt I α).symm z₀ = x := (extChartAt I α).left_inv hx_src
  have hΦt : MDifferentiableAt I I (Φ_fam t : M → M) x :=
    (Φ_fam t).contMDiff.mdifferentiable (by simp) x
  have hext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) ((Φ_fam t : M → M) x) :=
    mdifferentiableAt_extChartAt hΦtx_src
  have hcomp1 : MDifferentiableWithinAt 𝓘(ℝ, E) I
      ((Φ_fam t : M → M) ∘ (extChartAt I α).symm) (range I) z₀ :=
    (hround ▸ hΦt).comp_mdifferentiableWithinAt z₀ hsymm
  have hcomp2 : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt I α ∘ ((Φ_fam t : M → M) ∘ (extChartAt I α).symm)) (range I) z₀ := by
    have hpt : ((Φ_fam t : M → M) ∘ (extChartAt I α).symm) z₀ = (Φ_fam t : M → M) x := by
      simp only [Function.comp_apply, hround]
    exact (hpt ▸ hext).comp_mdifferentiableWithinAt z₀ hcomp1
  have hmdW : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (precompMap (I := I) Φ_fam t α) (range I) z₀ := hcomp2
  have hmd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (precompMap (I := I) Φ_fam t α) z₀ :=
    hmdW.mdifferentiableAt (by rw [hrange]; exact univ_mem)
  rwa [mdifferentiableAt_iff_differentiableAt] at hmd

/-- **`RawVariationalIdentityFlat` for the concrete flow at an interior time, from the
local-near-`t` cocycle data.**

The hypotheses are exactly the genuine, separable, local-near-`t` data: the time-`t` centred
chart-`α` Picard flow `ΦE` of a globally `C^∞` field `f` (with `α := Φ_fam t x`), jointly `C^∞`
on an interior box; the membership data `hzsU`/`hz`/`ht`/`hUtime`; the local-near-`t` cocycle
realisation `hrealΨ`; the chart-coordinate orbit velocity `hc_eucl`; the moving-trivialisation
chart jet `hGfd`; and orbit continuity `hcontAt`.

It produces `RawVariationalIdentityFlat (I := I) Φ_fam t x v _ _` for the concrete flow.  The
realisation constrains the orbit only for `s` near the interior time `t`: the Picard flow `ΦE` is
centred there (`ΦE(·, t) = id`), so no orbit point at a non-infinitesimal time enters.  The
realisation inputs are point-level manifold equalities and chart velocities, the regularity inputs
are a Picard flow and its joint smoothness, and the conclusion is the vector-valued
orbit-pushforward `HasDerivAt`. -/
theorem rawVariationalIdentityFlat_of_localGeometricFlow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    {f : ℝ → E → E} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {ΦE : E × ℝ → E}
    {G' : E →L[ℝ] (E →L[ℝ] E)} {velChart : E}
    (hΦE : IsLocalFlow f t x₀ r tmin tmax ΦE)
    (hf : ContDiff ℝ ∞ (uncurry f))
    {U : Set (E × ℝ)} (hUopen : IsOpen U) (hΦsmooth : ContDiffOn ℝ ∞ ΦE U)
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hzsU : (precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x), t) ∈ U)
    (hz : precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x)
      ∈ Metric.ball x₀ r)
    (ht : t ∈ Ioo tmin tmax)
    (hUtime : ∀ᶠ s : ℝ in 𝓝 t,
      (precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x), s) ∈ U)
    (hrealΨ : ∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
      (Φ_fam s : M → M) y
          = (extChartAt I (Φ_fam t x)).symm
              (ΦE (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) y), s))
        ∧ ΦE (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) y), s)
            ∈ (extChartAt I (Φ_fam t x)).target)
    (hc_eucl : HasDerivAt
      (fun s : ℝ => ΦE (precompMap (I := I) Φ_fam t (Φ_fam t x)
        (extChartAt I (Φ_fam t x) x), s)) velChart t)
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x)))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    RawVariationalIdentityFlat (I := I) Φ_fam t x v
      ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
          (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart))
      ((((fderiv ℝ (f t) (ΦE (precompMap (I := I) Φ_fam t (Φ_fam t x)
              (extChartAt I (Φ_fam t x) x), t))).comp
            (fderiv ℝ (fun w => ΦE (w, t))
              (precompMap (I := I) Φ_fam t (Φ_fam t x)
                (extChartAt I (Φ_fam t x) x)))).comp
          (fderiv ℝ (precompMap (I := I) Φ_fam t (Φ_fam t x))
            (extChartAt I (Φ_fam t x) x))).comp
        (trivToE (I := I) (Φ_fam t x) x)) := by
  classical
  set α : M := Φ_fam t x with hα
  set z₀ : E := extChartAt I α x with hz₀
  set w₀ : E := precompMap (I := I) Φ_fam t α z₀ with hw₀
  have hx_src' : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  set Φ_eucl : E → ℝ → E := Φ_euclLocal (I := I) ΦE Φ_fam t α with hΦeucl
  have hΦtx_src : (Φ_fam t : M → M) x ∈ (chartAt H α).source := by
    rw [show (Φ_fam t : M → M) x = α from rfl]
    exact mem_chart_source H α
  have hprecomp_diff : DifferentiableAt ℝ (precompMap (I := I) Φ_fam t α) z₀ :=
    precompMap_differentiableAt (I := I) Φ_fam t α x hx_src' hΦtx_src
  have hΦsmooth_time : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun w => ΦE (w, s)) w₀ := by
    filter_upwards [hUtime] with s hsU
    have hΦE_at : ContDiffAt ℝ ∞ ΦE (w₀, s) := hΦsmooth.contDiffAt (hUopen.mem_nhds hsU)
    have hincl : ContDiffAt ℝ ∞ (fun w : E => (w, s)) w₀ :=
      contDiffAt_id.prodMk contDiffAt_const
    exact (hΦE_at.comp w₀ hincl).differentiableAt (by simp)
  have heucl : HasDerivAt
      (fun s : ℝ => fderiv ℝ (fun z => Φ_eucl z s) z₀)
      (((fderiv ℝ (f t) (ΦE (w₀, t))).comp (fderiv ℝ (fun w => ΦE (w, t)) w₀)).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t α) z₀)) t :=
    heucl_precomp (I := I) hΦE hf hUopen hΦsmooth Φ_fam α x hprecomp_diff hzsU hz ht
      hΦsmooth_time
  have heucl_diff : ∀ᶠ s : ℝ in 𝓝 t,
      DifferentiableAt ℝ (fun z => Φ_eucl z s) z₀ := by
    filter_upwards [hΦsmooth_time] with s hsd
    have hcomp : (fun z => Φ_eucl z s)
        = (fun w => ΦE (w, s)) ∘ (precompMap (I := I) Φ_fam t α) := rfl
    rw [hcomp]
    exact hsd.comp z₀ hprecomp_diff
  have hsrc_nhds : ∀ᶠ y : M in 𝓝 x, y ∈ (extChartAt I α).source :=
    Filter.eventually_iff.mpr ((isOpen_extChartAt_source α).mem_nhds hx_src')
  have hagree : ∀ᶠ s : ℝ in 𝓝 t,
      (fun y => extChartAt I α ((Φ_fam s : M → M) y))
        =ᶠ[𝓝 x] (fun y => Φ_eucl (extChartAt I α y) s) :=
    hagree_of_cocycle_realisation (I := I) Φ_fam α x t ΦE hrealΨ hsrc_nhds
  have hreal_orbit : ∀ᶠ s : ℝ in 𝓝 t,
      extChartAt I α ((Φ_fam s : M → M) x) = ΦE (w₀, s) := by
    have hself : ∀ᶠ s : ℝ in 𝓝 t,
        (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x = Φ_eucl (extChartAt I α x) s := by
      filter_upwards [hagree] with s hs
      exact hs.self_of_nhds
    filter_upwards [hself] with s hs
    simpa [hΦeucl, Φ_euclLocal, hz₀, hw₀] using hs
  have hc : HasDerivAt
      (fun s : ℝ => extChartAt I α ((Φ_fam s : M → M) x)) velChart t := by
    refine hc_eucl.congr_of_eventuallyEq ?_
    filter_upwards [hreal_orbit] with s hs
    simpa [hz₀, hw₀] using hs
  have hg : HasDerivAt
      (fun s : ℝ => chartMovingTriv (I := I) α (extChartAt I α ((Φ_fam s : M → M) x)))
      (G' velChart) t :=
    chartMovingTriv_orbit_hasDerivAt_of_chartJet (I := I) Φ_fam α x t hGfd hc
  exact rawVariationalIdentityFlat_of_chart_realisation (I := I) Φ_fam x t v
    Φ_eucl hx_src heucl heucl_diff hagree hg hcontAt

end LocalChartDischarge

section RealisationProducer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- **The local-near-`t` cocycle realisation from the bare field's joint smoothness.**

For the bare field `X` jointly `C^∞` (`hX`, with its autonomised field jointly `C¹` `hXauto`)
and a diffeomorphism family `Φ_fam` whose orbits solve the bare ODE of `X` on a uniform two-sided
window `Ioo (t - T₀) (t + T₀) ×ˢ W` near `(t, x)`, there is a time-`t` centred chart-`α := Φ_fam t x`
Euclidean Picard flow `ΦE` of a globally `C^∞` field `f` (jointly `C^∞` on an open box `U`) such
that:

* `precompMap Φ_fam t α (extChartAt I α x) ∈ ball x₀ r` and `(·, t) ∈ U` for `(precomp, ·)` near
  `t` (the membership data the variational discharge consumes); and
* the local-near-`t` cocycle realisation `hrealΨ` holds, with the chart value confined to the
  chart target.

The chart Picard flow is produced by `h3_local_flow_chartIsLocalFlow_and_realisation` at the
interior `(t, α)`; the cocycle realisation is the two-sided integral-curve uniqueness
`bare_integral_flow_eqOn_of_jointC1` identifying `s ↦ Φ_fam s y` with the chart flow's continuation
`s ↦ Φ (Φ_fam t y) s` on the uniform window (both solve the bare ODE and agree at `s = t`).  The
window is centred at the interior time `t`, so the realisation constrains the orbit only near `t`. -/
theorem exists_chartPicard_and_cocycle_realisation
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (hXauto : AutonomizedFieldJointC1 (I := I) X)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) {T₀ : ℝ} {W : Set M}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hT₀ : 0 < T₀) (hW : IsOpen W) (hxW : x ∈ W)
    (hΦfam_ode : ∀ y ∈ W, ∀ s ∈ Set.Ioo (t - T₀) (t + T₀),
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
        (Set.Ioo (t - T₀) (t + T₀)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) y))))
    (hcontAt_orbit : ContinuousAt (fun y : M => (Φ_fam t : M → M) y) x) :
    ∃ (x₀ : E) (r : ℝ≥0) (ε : ℝ) (ΦE : E × ℝ → E)
      (f : ℝ → E → E) (U : Set (E × ℝ)),
      ContDiff ℝ ∞ (Function.uncurry f) ∧
      IsLocalFlow f t x₀ r (t - ε) (t + ε) ΦE ∧
      IsOpen U ∧ ContDiffOn ℝ ∞ ΦE U ∧
      (precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x), t) ∈ U ∧
      precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x) ∈ Metric.ball x₀ r ∧
      t ∈ Set.Ioo (t - ε) (t + ε) ∧
      (∀ᶠ s : ℝ in 𝓝 t,
        (precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x), s) ∈ U) ∧
      (∀ᶠ s : ℝ in 𝓝 t, ∀ᶠ y : M in 𝓝 x,
        (Φ_fam s : M → M) y
            = (extChartAt I (Φ_fam t x)).symm
                (ΦE (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) y), s))
          ∧ ΦE (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) y), s)
              ∈ (extChartAt I (Φ_fam t x)).target) := by
  classical
  set α : M := Φ_fam t x with hα
  obtain ⟨U, hU_open, hp₀_U, T, hT_pos, Φ, f, x₀, r, ε, ΦE, hf, hx₀eq, hr_pos, hε_pos, hflow,
      ⟨ρE, TE, hρE_pos, hTE_pos, hΦE_smooth⟩, hΦinit, hΦreal, hΦconf, hΦsmoothOn, hΦbare⟩ :=
    h3_local_flow_chartIsLocalFlow_and_realisation (I := I) X hX t α
  set z₀ : E := extChartAt I α x with hz₀
  set w₀ : E := precompMap (I := I) Φ_fam t α z₀ with hw₀
  have hαα : extChartAt I α α = x₀ := hx₀eq.symm
  have hx_src' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hx_src
  have hw₀_eq : w₀ = x₀ := by
    rw [hw₀, precompMap_chartPoint (I := I) Φ_fam t α x hx_src']
    rw [show (Φ_fam t : M → M) x = α from rfl, hαα]
  set Ubox : Set (E × ℝ) := Metric.ball x₀ ρE ×ˢ Set.Ioo (t - TE) (t + TE) with hUbox
  have hUbox_open : IsOpen Ubox := (Metric.isOpen_ball).prod isOpen_Ioo
  have hw₀_ballρE : w₀ ∈ Metric.ball x₀ ρE := by rw [hw₀_eq]; exact Metric.mem_ball_self hρE_pos
  have hw₀_ballr : w₀ ∈ Metric.ball x₀ (r : ℝ) := by rw [hw₀_eq]; exact Metric.mem_ball_self hr_pos
  have hwtU : (w₀, t) ∈ Ubox := ⟨hw₀_ballρE, by constructor <;> linarith⟩
  have hUtime : ∀ᶠ s : ℝ in 𝓝 t, (w₀, s) ∈ Ubox := by
    have hopen : IsOpen {s : ℝ | (w₀, s) ∈ Ubox} := hUbox_open.preimage (by fun_prop)
    exact hopen.mem_nhds hwtU
  refine ⟨x₀, r, ε, ΦE, f, Ubox, hf, hflow, hUbox_open, hΦE_smooth, hwtU, hw₀_ballr,
    ⟨by linarith, by linarith⟩, hUtime, ?_⟩
  set T' : ℝ := min T T₀ with hT'
  have hT'_pos : 0 < T' := lt_min hT_pos hT₀
  have hT'_le_T : T' ≤ T := min_le_left _ _
  have hT'_le_T₀ : T' ≤ T₀ := min_le_right _ _
  have hsub_T : Set.Ioo (t - T') (t + T') ⊆ Set.Ioo (t - T) (t + T) :=
    Set.Ioo_subset_Ioo (by linarith) (by linarith)
  have hsub_T₀ : Set.Ioo (t - T') (t + T') ⊆ Set.Ioo (t - T₀) (t + T₀) :=
    Set.Ioo_subset_Ioo (by linarith) (by linarith)
  have hyU : ∀ᶠ y : M in 𝓝 x, (Φ_fam t : M → M) y ∈ U := by
    have : (Φ_fam t : M → M) x ∈ U := by rw [show (Φ_fam t : M → M) x = α from rfl]; exact hp₀_U
    exact hcontAt_orbit.eventually_mem (hU_open.mem_nhds this)
  have hyW : ∀ᶠ y : M in 𝓝 x, y ∈ W := hW.mem_nhds hxW
  have hcocycle : ∀ᶠ y : M in 𝓝 x, ∀ s ∈ Set.Ioo (t - T') (t + T'),
      (Φ_fam s : M → M) y = Φ ((Φ_fam t : M → M) y) s := by
    filter_upwards [hyU, hyW] with y hyU hyW
    have ht_mem' : t ∈ Set.Ioo (t - T') (t + T') := ⟨by linarith, by linarith⟩
    have hode_fam : ∀ s ∈ Set.Ioo (t - T') (t + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
          (Set.Ioo (t - T') (t + T')) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) y))) := by
      intro s hs
      exact (hΦfam_ode y hyW s (hsub_T₀ hs)).mono hsub_T₀
    have hode_chart : ∀ s ∈ Set.Ioo (t - T') (t + T'),
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ ((Φ_fam t : M → M) y) u)
          (Set.Ioo (t - T') (t + T')) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ ((Φ_fam t : M → M) y) s))) := by
      intro s hs
      exact (hΦbare ((Φ_fam t : M → M) y) hyU s (hsub_T hs)).hasMFDerivWithinAt
    have hstart : (Φ_fam t : M → M) y = Φ ((Φ_fam t : M → M) y) t :=
      (hΦinit ((Φ_fam t : M → M) y) hyU).symm
    exact bare_integral_flow_eqOn_of_jointC1 X hXauto
      (fun u p => (Φ_fam u : M → M) p) (fun u p => Φ p u) y ((Φ_fam t : M → M) y)
      ht_mem' hode_fam hode_chart hstart
  have hwindow : Set.Ioo (t - T') (t + T') ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  filter_upwards [hwindow] with s hs
  filter_upwards [hcocycle, hyU, hyW] with y hyc hyU hyW
  have hpt : (Φ_fam s : M → M) y
      = (extChartAt I α).symm (ΦE (extChartAt I α ((Φ_fam t : M → M) y), s)) := by
    rw [hyc s hs, hΦreal ((Φ_fam t : M → M) y) hyU s]
  refine ⟨hpt, ?_⟩
  exact hΦconf ((Φ_fam t : M → M) y) hyU s (hsub_T hs)

/-- **`RawVariationalIdentityFlat` for the concrete flow at an interior time, from the bare
field's joint smoothness.**

The substantive analytic inputs are the bare field `X`'s joint `C^∞` smoothness (`hX`), its
autonomised field's joint `C¹`-ness (`hXauto`), and the bare-flow ODE of `Φ_fam` on a uniform
two-sided window near `(t, x)` (`hΦfam_ode`).  From these, the time-`t` centred chart Picard flow
and the local-near-`t` cocycle realisation are *produced* (no confinement), and routed through the
moving-chart-local discharge.  The remaining smooth-structure side data (`hc_eucl`, `hGfd`,
`hcontAt`) are exactly those the consumer `rawVariationalIdentityFlat_of_chart_realisation`
requires; `hGfd`/`hc_eucl` are the smooth-structure jets (chart-transition first jet and
chart-orbit velocity), and the chart-orbit velocity is bound to the produced `ΦE` through the
existentially-quantified realisation, so the headline is stated with `ΦE`, the produced flow,
exposed.

The conclusion is the vector-valued orbit-pushforward `HasDerivAt`, obtained from the produced
Picard flow, the cocycle realisation, and the discharge. -/
theorem rawVariationalIdentityFlat_of_jointSmoothBareField
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (hXauto : AutonomizedFieldJointC1 (I := I) X)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) {T₀ : ℝ} {W : Set M}
    (hx_src : x ∈ (chartAt H (Φ_fam t x)).source)
    (hT₀ : 0 < T₀) (hW : IsOpen W) (hxW : x ∈ W)
    (hΦfam_ode : ∀ y ∈ W, ∀ s ∈ Set.Ioo (t - T₀) (t + T₀),
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) y)
        (Set.Ioo (t - T₀) (t + T₀)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) y))))
    (hcontAt_orbit : ContinuousAt (fun y : M => (Φ_fam t : M → M) y) x)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    {G' : E →L[ℝ] (E →L[ℝ] E)}
    (hGfd : HasFDerivAt (fun z => chartMovingTriv (I := I) (Φ_fam t x) z) G'
      (extChartAt I (Φ_fam t x) ((Φ_fam t : M → M) x))) :
    ∃ (ΦE : E × ℝ → E) (velChart : E) (P' : E →L[ℝ] E),
      HasDerivAt
        (fun s : ℝ => ΦE (precompMap (I := I) Φ_fam t (Φ_fam t x)
          (extChartAt I (Φ_fam t x) x), s)) velChart t ∧
      RawVariationalIdentityFlat (I := I) Φ_fam t x v
        ((-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E)
            (1 : E →L[ℝ] E) (1 : E →L[ℝ] E)) (G' velChart))
        (P'.comp (trivToE (I := I) (Φ_fam t x) x)) := by
  classical
  obtain ⟨x₀, r, ε, ΦE, f, U, hf, hΦE, hUopen, hΦsmooth, hzsU, hz, ht, hUtime, hrealΨ⟩ :=
    exists_chartPicard_and_cocycle_realisation (I := I) X hX hXauto Φ_fam t x
      hx_src hT₀ hW hxW hΦfam_ode hcontAt_orbit
  set w₀ : E := precompMap (I := I) Φ_fam t (Φ_fam t x) (extChartAt I (Φ_fam t x) x) with hw₀
  have hslice_diff : DifferentiableAt ℝ (fun s : ℝ => ΦE (w₀, s)) t := by
    have hΦE_at : ContDiffAt ℝ ∞ ΦE (w₀, t) := hΦsmooth.contDiffAt (hUopen.mem_nhds hzsU)
    have hincl : ContDiffAt ℝ ∞ (fun s : ℝ => (w₀, s)) t :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (hΦE_at.comp t hincl).differentiableAt (by simp)
  set velChart : E := deriv (fun s : ℝ => ΦE (w₀, s)) t with hvel
  have hc_eucl : HasDerivAt (fun s : ℝ => ΦE (w₀, s)) velChart t :=
    hslice_diff.hasDerivAt
  refine ⟨ΦE, velChart, ((fderiv ℝ (f t) (ΦE (w₀, t))).comp
      (fderiv ℝ (fun w => ΦE (w, t)) w₀)).comp
        (fderiv ℝ (precompMap (I := I) Φ_fam t (Φ_fam t x)) (extChartAt I (Φ_fam t x) x)),
      hc_eucl, ?_⟩
  exact rawVariationalIdentityFlat_of_localGeometricFlow (I := I) Φ_fam t x v
    hΦE hf hUopen hΦsmooth hx_src hzsU hz ht hUtime hrealΨ hc_eucl hGfd hcontAt

end RealisationProducer

end DifferentialGeometry.PDE.RicciFlow.ODE
