import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftCovariant
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.PushforwardSmooth

/-!
# The `mfderiv`-in-chart dictionary feeding the raw variational identity

The combinator `rawVariationalIdentity_of_chartFlow_innerCLM`
(`SmoothInSpace/VariationalLiftCovariant.lean`) produces `RawVariationalIdentity`
from three per-flow inputs:

* `hDchart` — an operator-valued Euclidean variational ODE on the model space `E`;
* `hagree` — an **eventual** (`=ᶠ[𝓝 t]`) equality reading the manifold pushforward
  `s ↦ (mfderiv I I (Φ_fam s) x v : E)` as a chart-coordinate expression `s ↦ Q (Dchart s d)`;
* `hQinner` — the flat-plus-Christoffel value equation at the orbit point.

This file supplies the **mfderiv-in-chart dictionary**: the precise relationship between
the manifold pushforward `mfderiv I I F x v : E` and a chart-coordinate Fréchet derivative,
through which `hagree` is constructed for a smooth flow read in a *fixed* target chart at the
orbit point `α := Φ_fam t x`.

## The honest content of the dictionary

`TangentSpace I b := E` definitionally for every base point `b`, so the value
`mfderiv I I F x v : E` is the *raw* fibre element read off in Mathlib's *moving* target chart
`extChartAt I (F x)`.  The trivialization at the *fixed* base point `α` reads it differently:
the two are reconciled by Mathlib's identities

* `TangentBundle.continuousLinearMapAt_trivializationAt`:
  `trivToE α y = mfderiv (extChartAt I α) y` on the chart source of `α`;
* `TangentBundle.symmL_trivializationAt`:
  `trivFromE α y = mfderivWithin (extChartAt I α).symm (range I) (extChartAt I α y)`.

Composed with `mfderiv_comp`, the first gives the genuine dictionary

  `trivToE α (F x) (mfderiv I I F x v) = mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v`,

valid whenever `F x ∈ (chartAt H α).source`.  Round-tripping with `trivFromE α (F x)` on the
trivialization base set yields the raw-value form

  `(mfderiv I I F x v : E)
     = trivFromE α (F x) (mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v)`.

For the moving flow `F = Φ_fam s`, the orbit point `Φ_fam s x` lies in the *fixed* chart
source of `α := Φ_fam t x` for all `s` near `t` (continuity of the orbit at `t`, where
`Φ_fam t x = α`), so the raw-value form holds *eventually* — exactly the shape of `hagree`,
with `Q s := trivFromE α (Φ_fam s x)` and `Dchart s d := mfderiv (extChartAt I α ∘ Φ_fam s) x v`.

Because `hagree` in the combinator requires a *single, time-independent* `Q`, this file
exposes the dictionary in two layers:

* the per-time **chart-reading equality** `mfderiv_flow_eq_chartFderiv_apply` (an honest
  pointwise `E`-equation, no eventual quantifier), and
* the **eventual chart membership** `flow_orbit_eventually_mem_chartAt_source` of the moving
  orbit point, from which the `=ᶠ[𝓝 t]` family used by `hagree` is assembled.

No joint-`C^∞`-on-`ℝ × M` predicate is used: every smoothness fact is the per-time spatial
smoothness of `Φ_fam s` (a diffeomorphism) plus the continuity of the orbit in `s`.  No
`HasLocallyConstantChartAt`, no hypothesis-packaging: the conclusions are genuine
chart-calculus identities, never the `HasDerivAt` target itself.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Dictionary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Trivialized pushforward equals chart-coordinate Fréchet derivative.**

For a self-map `F : M → M` manifold-differentiable at `x`, a base point `α` whose chart source
contains the image `F x`, and a tangent vector `v`, the chart-`α` trivialization
`trivToE α (F x)` of the pushforward `mfderiv I I F x v` equals the chart-coordinate
spatial derivative `mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v`.

The proof rewrites `trivToE α (F x)` as `mfderiv (extChartAt I α) (F x)` via
`TangentBundle.continuousLinearMapAt_trivializationAt`, then applies the chain rule
`mfderiv_comp`. -/
theorem trivToE_mfderiv_eq_chartFderiv_apply
    (F : M → M) (α : M) {x : M} (v : TangentSpace I x)
    (hF : MDifferentiableAt I I F x)
    (hFx : F x ∈ (chartAt H α).source) :
    trivToE (I := I) α (F x) (mfderiv I I F x v)
      = mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v := by
  have htriv : trivToE (I := I) α (F x)
      = mfderiv I 𝓘(ℝ, E) (extChartAt I α) (F x) :=
    TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hFx
  have hext : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) (F x) :=
    mdifferentiableAt_extChartAt (I := I) hFx
  have hchain :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α ∘ F) x
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I α) (F x)).comp (mfderiv I I F x) :=
    mfderiv_comp x hext hF
  rw [htriv]
  have happ := congrArg (fun L : TangentSpace I x →L[ℝ] _ => L v) hchain
  simpa [ContinuousLinearMap.comp_apply, Function.comp] using happ.symm

/-- **Raw pushforward value as transported chart-coordinate derivative
(`mfderiv_flow_eq_chartFderiv_apply`).**

For a self-map `F : M → M` differentiable at `x` with `F x` in the chart source of `α`, the raw
fibre value `(mfderiv I I F x v : TangentSpace I (F x) = E)` equals the chart-coordinate
spatial derivative `mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v` transported by the inverse target
trivialization `trivFromE α (F x)`:

  `mfderiv I I F x v = trivFromE α (F x) (mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ F) x v)`.

This is the round-trip `trivFromE α (F x) ∘ trivToE α (F x) = id` (valid because
`F x ∈ (chartAt H α).source = (trivializationAt …).baseSet`) applied to the dictionary
`trivToE_mfderiv_eq_chartFderiv_apply`. -/
theorem mfderiv_flow_eq_chartFderiv_apply
    (F : M → M) (α : M) {x : M} (v : TangentSpace I x)
    (hF : MDifferentiableAt I I F x)
    (hFx : F x ∈ (chartAt H α).source) :
    mfderiv I I F x v
      = trivFromE (I := I) α (F x)
          (mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v) := by
  have hbase : F x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hFx
  have hdict := trivToE_mfderiv_eq_chartFderiv_apply (I := I) F α v hF hFx
  calc
    mfderiv I I F x v
        = trivFromE (I := I) α (F x)
            (trivToE (I := I) α (F x) (mfderiv I I F x v)) :=
          (trivFromE_trivToE (I := I) α hbase (mfderiv I I F x v)).symm
    _ = trivFromE (I := I) α (F x)
            (mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α (F y)) x v) := by
          rw [hdict]

/-- **Continuity of the orbit at a fixed time.**

For a time-indexed diffeomorphism family `Φ_fam`, the orbit map `s ↦ Φ_fam s x` is
continuous in `s` at `t`, *provided* the joint orbit `(s, x) ↦ Φ_fam s x` is continuous (the
genuinely separable continuity input — never joint `C^∞`).  This is the hypothesis the flow's
own regularity package supplies. -/
theorem orbit_continuousAt_of_jointContinuous
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M)
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x)) :
    ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t :=
  hcont.continuousAt

/-- **Eventual chart membership of the moving orbit point
(`flow_orbit_eventually_mem_chartAt_source`).**

If the orbit `s ↦ Φ_fam s x` is continuous at `t` and `Φ_fam t x = α` with `α` in its own
chart source (automatic), then for `s` near `t` the orbit point `Φ_fam s x` lies in the chart
source of `α`.  This is the membership condition that activates
`mfderiv_flow_eq_chartFderiv_apply` for all `s` in a neighbourhood of `t`. -/
theorem flow_orbit_eventually_mem_chartAt_source
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t) :
    ∀ᶠ s : ℝ in 𝓝 t, (Φ_fam s : M → M) x ∈ (chartAt H (Φ_fam t x)).source := by
  have hsrc_mem : (chartAt H (Φ_fam t x)).source ∈ 𝓝 (Φ_fam t x) :=
    (chartAt H (Φ_fam t x)).open_source.mem_nhds (mem_chart_source H (Φ_fam t x))
  exact hcontAt.eventually_mem hsrc_mem

/-- **The eventual chart-reading agreement from a chart-coordinate witness.**

Suppose, for `s` near `t`, the caller's chart-coordinate data `Q`, `d`, `Dchart` reproduces the
transported chart-coordinate derivative:

  `Q (Dchart s d) = trivFromE α (Φ_fam s x) (mfderiv (extChartAt I α ∘ Φ_fam s) x v)`
  eventually in `s`,

with `α := Φ_fam t x`.  Then the manifold pushforward reading `hagree` of
`rawVariationalIdentity_of_chartFlow_innerCLM` holds:

  `(fun s => (mfderiv I I (Φ_fam s) x v : E)) =ᶠ[𝓝 t] (fun s => Q (Dchart s d))`.

The proof intersects the eventual chart membership (Part 3) with the witness, then rewrites the
manifold pushforward by `mfderiv_flow_eq_chartFderiv_apply` (Part 2) at each `s`. -/
theorem hagree_of_chartFderiv_witness
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E) (Dchart : ℝ → (E →L[ℝ] E))
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d))) :
    (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)) := by
  have hmem := flow_orbit_eventually_mem_chartAt_source (I := I) Φ_fam t x hcontAt
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hstep : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v)) := by
    filter_upwards [hmem] with s hs
    exact mfderiv_flow_eq_chartFderiv_apply (I := I) (Φ_fam s : M → M) (Φ_fam t x) v
      ((Φ_fam s).mdifferentiable hinfty x) hs
  exact hstep.trans hwitness

end Dictionary

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Per-flow raw variational identity from chart-coordinate witnesses.**

Bundles the two genuinely-missing pieces into the combinator
`rawVariationalIdentity_of_chartFlow_innerCLM`.  The caller supplies, on the model space `E`
only:

* `hDchart` — the operator-valued Euclidean variational ODE `HasDerivAt Dchart Dchart' t`;
* `hcontAt` — continuity of the orbit `s ↦ Φ_fam s x` at `t` (separable continuity input);
* `hwitness` — the eventual reproduction of the transported chart-coordinate derivative by
  `Q (Dchart s d)` (the BanachIC / trivialization convention reading, near `t`);
* `hQinner` — the flat-plus-Christoffel value equation at the orbit point.

The conclusion is `RawVariationalIdentity`.  `hagree` is produced by `hagree_of_chartFderiv_witness`
(Parts 2–3); the connection content of `hQinner` is discharged inside the combinator.  No joint
`C^∞`-on-`ℝ × M`, no `HasLocallyConstantChartAt`, no hypothesis-packaging. -/
theorem rawVariationalIdentity_of_chartFderiv_witness
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hcontAt : ContinuousAt (fun s : ℝ => (Φ_fam s : M → M) x) t)
    (hwitness : (fun s : ℝ =>
        trivFromE (I := I) (Φ_fam t x) ((Φ_fam s : M → M) x)
          (mfderiv I 𝓘(ℝ, E)
            (fun y => extChartAt I (Φ_fam t x) ((Φ_fam s : M → M) y)) x v))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hagree :=
    hagree_of_chartFderiv_witness (I := I) Φ_fam t x v Q d Dchart hcontAt hwitness
  exact rawVariationalIdentity_of_chartFlow_innerCLM (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQinner

end Producer

end DifferentialGeometry.PDE.RicciFlow.ODE
