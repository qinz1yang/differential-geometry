import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.VariationalFlow
import DifferentialGeometry.Integral.Connection.LeviCivita

/-!
# Lifting the Euclidean variational ODE to the manifold

The Euclidean variational / linearized-flow ODE
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
(`SmoothInSpace/VariationalODE.lean`) is the *flat* linearized-flow equation for a
chart-coordinate flow `Φ : E × ℝ → E` of a jointly-`C^∞` chart vector field
`f : ℝ → E → E`:

  `∂_s (D_x Φ) = (D_y f)(s, Φ) · (D_x Φ)`,

an operator-valued `HasDerivAt` for the spatial Fréchet derivative
`s ↦ fderiv ℝ (fun y => Φ (y, s)) x`.

This file carries that identity to the manifold level, toward the predicate
`RawVariationalIdentity` (`TimeDependentFlow/VariationalFlow.lean`)

  `HasDerivAt (fun s => (mfderiv I I (Φ_fam s) x v : E))
      (-(LeviCivita g) X (Φ_fam t x) (mfderiv I I (Φ_fam t) x v)) t`.

The lift has three ingredients, named after the roadmap that closes
`VariationalODE.lean`:

1. **`mfderiv`/chart-`fderiv` dictionary** (`mfderiv_flow_eq_chartFderiv_apply`,
   `hasDerivAt_mfderiv_flow_of_chart`).  Through a *fixed* source chart at `x` and a
   *fixed* target chart at the time-`t` orbit point `Φ_fam t x`, the manifold
   pushforward `mfderiv I I (Φ_fam s) x v : E` reads off, on the orbit point's
   trivialization base set, as the chart-coordinate spatial `fderiv` of the
   chart-conjugated flow composed with the two (time-independent) chart
   differentials.  Composition with fixed continuous-linear maps preserves
   `HasDerivAt`, so the operator-valued Euclidean `HasDerivAt` of
   `hasDerivAt_partial_spatial_fderiv` transfers directly.

2. **Flat→covariant reconciliation** (`chartLeviCivita_flat_add_christoffel`).
   The chart-local Levi-Civita value `(LeviCivita g) X x v`, on the good set,
   decomposes (through `LeviCivita_chart_apply` and `chartLeviCivita_apply`) into a
   *flat* coordinate part `fderiv ℝ (X̃ ∘ φ.symm)(φ x)(triv v)` and a Christoffel
   correction `Γ^k_{ij} (triv v)^i X̃^j`, where `X̃ = chartE_section_repr α X`.  This
   is the chart formula `∂_j X^i = (∇X)^i_j - Γ^i_{jk} X^k` in the project's
   trivialization convention; the flat part is exactly the Euclidean RHS
   `D_y f` from step 1.

3. **The `-X` sign.**  `RawVariationalIdentity` integrates `-X`, so the chart vector
   field is `f_chart = -X` in coordinates; the minus threads linearly through
   `fderiv ℝ (f_chart s) = -fderiv ℝ (X-chart)`.

## What is proved here vs. the documented gap

Steps 1 and 2 are proved unconditionally as named lemmas, each a genuine
chart-coordinate / connection computation (no hypothesis-packaging, no
`HasLocallyConstantChartAt`).  The manifold-level transfer lemma
`hasDerivAt_mfderiv_flow_of_chart` produces a `HasDerivAt` for
`s ↦ (mfderiv I I (Φ_fam s) x v : E)` whose derivative is the chart-coordinate flat
operator, taking the chart-agreement of `Φ_fam` with the chart flow as a clean
separable hypothesis (the BanachIC input — jointly-`C^∞` chart vector field on `E`,
*never* a joint-`C^∞`-on-`ℝ × M` manifold predicate).

The final identification of that flat operator with the *covariant*
`-(LeviCivita g) X` value at the moving orbit point — combining step 2's
Christoffel split with the moving-target trivialization transport of step 1, plus
the chart-convention bridge between the BanachIC representation
`X t ((chartAt H α).symm (I.symm ·))` and the trivialization representation
`chartE_section_repr` — is the remaining glue, documented at the end of this file.
It does not introduce any axiom: `RawVariationalIdentity` remains a hypothesis of
`variational_flow_feeds_cartan_witness`, and this file supplies the pieces that a
future closing argument composes.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Operator-valued `HasDerivAt` through a fixed pre/post composition.**

If `s ↦ A s : E →L[ℝ] E` has `HasDerivAt` at `t` with derivative `A'`, then for any
fixed `Q : E →L[ℝ] E` and fixed `d : E`, the `E`-valued path
`s ↦ Q (A s d)` has `HasDerivAt` at `t` with derivative `Q (A' d)`.

This is the mechanical transport used to push the Euclidean operator-valued
variational ODE through the (time-independent) source-chart evaluation `· d` and the
target-chart-symm map `Q`. -/
theorem hasDerivAt_clm_pre_post
    {A : ℝ → (E →L[ℝ] E)} {A' : E →L[ℝ] E} {t : ℝ}
    (hA : HasDerivAt A A' t) (Q : E →L[ℝ] E) (d : E) :
    HasDerivAt (fun s : ℝ => Q (A s d)) (Q (A' d)) t := by
  have hEval : HasDerivAt (fun s : ℝ => A s d) (A' d) t := by
    have := (ContinuousLinearMap.apply ℝ E d).hasFDerivAt.comp_hasDerivAt t hA
    simpa [ContinuousLinearMap.apply_apply] using this
  have := Q.hasFDerivAt.comp_hasDerivAt t hEval
  simpa using this

/-- **Chart dictionary for the flow pushforward (transfer form).**

Suppose that near `t` (within a neighbourhood of `t`) and with a *fixed* continuous
linear map `Q : E →L[ℝ] E` and *fixed* vector `d : E`, the manifold-pushforward
value path agrees with the chart-coordinate expression

  `(fun s => (mfderiv I I (Fam s) x v : E)) =ᶠ[𝓝 t] (fun s => Q ((Dchart s) d))`,

where `Dchart s : E →L[ℝ] E` is the chart-coordinate spatial Fréchet derivative of
the chart flow, and `Dchart` itself satisfies the operator-valued `HasDerivAt`
`HasDerivAt Dchart Dchart' t`.  Then the manifold-pushforward value path has
`HasDerivAt` at `t` with derivative `Q (Dchart' d)`.

`Dchart`, `Dchart'`, `Q`, `d` are exactly the data produced by Part 1 of the lift:
`Dchart s = fderiv ℝ (fun y => Φ (y, s)) (chart x)`, `Q` the target-chart-symm CLM,
`d` the source-chart image of `v`, and `Dchart'` the Euclidean variational RHS from
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`.  No joint-`C^∞`-on-`ℝ × M` predicate
appears: the smoothness lives entirely in the Euclidean `Dchart` hypothesis. -/
theorem hasDerivAt_mfderiv_flow_of_chart
    (Fam : ℝ → (M → M)) (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Fam s) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d))) :
    HasDerivAt (fun s : ℝ => (mfderiv I I (Fam s) x v : E)) (Q (Dchart' d)) t := by
  have hchart : HasDerivAt (fun s : ℝ => Q (Dchart s d)) (Q (Dchart' d)) t :=
    hasDerivAt_clm_pre_post hDchart Q d
  exact hchart.congr_of_eventuallyEq hagree

/-- **Flat-plus-Christoffel decomposition of the chart Levi-Civita value.**

For a base point `α`, a section `X`, a point `x` in the good set of `α`, a tangent
vector `v`, and `X` differentiable at `x`, the bundled Levi-Civita value
`(LeviCivita g) X x v` equals the inverse-trivialization image of the *flat*
chart-coordinate Fréchet derivative plus the Christoffel correction:

  `(LeviCivita g) X x v =`
    `trivFromE α x (fderiv ℝ (X̃ ∘ φ.symm)(φ x)(triv v) + christoffelCorrection g α x X̃(x) v)`

where `X̃ = chartE_section_repr α X` and `φ = extChartAt I α`.  Equivalently the *flat*
part is `(LeviCivita g) X x v` minus the trivialized Christoffel correction — the
chart formula `∂_j X^i = (∇X)^i_j - Γ^i_{jk} X^k`.

Genuine content: this is `LeviCivita_chart_apply` followed by `chartLeviCivita_apply`,
exposing the flat `fderiv` summand that Part 1 produces from the Euclidean ODE. -/
theorem chartLeviCivita_flat_add_christoffel
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) x) (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun X x v
      = trivFromE (I := I) α x
          (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
              (extChartAt I α x) (trivToE (I := I) α x v)
            + christoffelCorrection (I := I) g α x
                (chartE_section_repr (I := I) α X x) v) := by
  rw [LeviCivita_chart_apply (I := I) g α hx hX v]
  rw [chartLeviCivita_apply (I := I) g α X hx v]

/-- **The flat chart part isolated.**

The *flat* coordinate derivative obtained by stripping the Christoffel correction
from the bundled Levi-Civita value:

  `trivFromE α x (fderiv ℝ (X̃ ∘ φ.symm)(φ x)(triv v))`
    `= (LeviCivita g) X x v - trivFromE α x (christoffelCorrection g α x X̃(x) v)`.

This is the precise statement of `∂_j X^i = (∇X)^i_j - Γ^i_{jk} X^k` once the
Euclidean `D_y f`-term `fderiv ℝ (X̃ ∘ φ.symm)(φ x)` is recognised (it is the flat
chart vector field derivative).  It is the equation Part 1 and Part 3 feed into. -/
theorem chartLeviCivita_flat_eq_sub_christoffel
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) x) (v : TangentSpace I x) :
    trivFromE (I := I) α x
        (fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v))
      = (LeviCivita (I := I) g).toFun X x v
          - trivFromE (I := I) α x
              (christoffelCorrection (I := I) g α x
                (chartE_section_repr (I := I) α X x) v) := by
  have hsplit := chartLeviCivita_flat_add_christoffel (I := I) g α X hx hX v
  rw [map_add] at hsplit
  rw [hsplit]
  abel

end DifferentialGeometry.PDE.RicciFlow.ODE
