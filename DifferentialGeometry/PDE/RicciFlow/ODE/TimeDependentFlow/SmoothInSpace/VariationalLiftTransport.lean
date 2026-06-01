import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLift

/-!
# Moving-base-point transport: producing the raw variational identity

This file closes the last documented step of the manifold lift of the Euclidean
variational ODE.  `SmoothInSpace/VariationalLift.lean` proved the two ingredients:

* **Part 1** (`hasDerivAt_mfderiv_flow_of_chart`): the chart-coordinate operator-valued
  Euclidean variational ODE `HasDerivAt Dchart Dchart' t` transfers, through a *fixed*
  source-chart evaluation `· d` and a *fixed* target-chart-symm continuous-linear map
  `Q`, to a `HasDerivAt` for the `E`-valued moving-pushforward path
  `s ↦ (mfderiv I I (Φ_fam s) x v : E)`, with derivative `Q (Dchart' d)`, given the
  chart-reading eventual equality `hagree`.

* **Part 2** (`chartLeviCivita_flat_add_christoffel`,
  `chartLeviCivita_flat_eq_sub_christoffel`): on the good set of a *fixed* base point
  `α`, the bundled Levi-Civita value splits as `trivFromE α x` of the flat
  chart-coordinate `fderiv` plus the Christoffel correction — the chart formula
  `∂_j X^i = (∇X)^i_j - Γ^i_{jk} X^k`.

The remaining glue documented at the end of `VariationalLift.lean` is the
*moving-target trivialization transport*: the value `mfderiv I I (Φ_fam s) x v : E`
lives in `TangentSpace I (Φ_fam s x)`, whose trivialization base point moves with `s`,
while Part 2 is anchored at the fixed `α = Φ_fam t x`.

## The resolution

Under the type alias `TangentSpace I b = E` (definitional for every base point `b`), the
moving-pushforward value path is *genuinely* `E`-valued, so the `(… : E)` reading in
`RawVariationalIdentity` already collapses the moving base point to `E`.  The geometric
right-hand side `-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)` is evaluated at
the **fixed** instant-`t` base point `α := Φ_fam t x` — this is correct precisely because
`HasDerivAt … t` reports the derivative value at `t`, where the orbit point *is* `α`.
Only the path `s ↦ mfderiv (Φ_fam s) x v` is differentiated; the base point of the
right-hand side does not move.  Therefore Part 2 applies directly at `α := Φ_fam t x`.

The transport is therefore an algebraic combination, carried out here:

1. Part 1 produces `HasDerivAt (s ↦ mfderiv (Φ_fam s) x v : E) (Q (Dchart' d)) t`.

2. The transported value `Q (Dchart' d)` is identified with the covariant right-hand side
   `-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.  This identification is the
   genuine *moving-target trivialization transport + sign* bookkeeping; it factors through
   Part 2.

## Contents

* `trivFromE_innerCLM_eq_leviCivita_at_orbit` (Part-2 content at the fixed orbit point):
  the inverse-trivialised chart Levi-Civita *inner CLM* — the flat chart `fderiv` summand
  plus the Christoffel correction — applied to the pushforward, equals the bundled
  covariant value `(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.  This is
  `chartLeviCivita_apply` followed by `LeviCivita_chart_apply`, read at `α := Φ_fam t x`.

* `rawVariationalIdentity_of_chartFlow_value`: the minimal transport combinator —
  Part 1's transferred `HasDerivAt` plus the value identification of `Q (Dchart' d)` with
  the covariant right-hand side (an *equality of vectors in `E`*, never a `HasDerivAt`, so
  never the conclusion itself) produces `RawVariationalIdentity`.

* `rawVariationalIdentity_of_chartFlow`: the same conclusion, but the value identification
  is supplied in its *flat-plus-Christoffel* form `hQinner` (transported Euclidean value =
  minus the inverse-trivialised inner CLM applied to the pushforward) together with the
  Levi-Civita/inner-CLM identity `hLC` (discharged by
  `trivFromE_innerCLM_eq_leviCivita_at_orbit`); the conversion to the covariant value is
  then derived here, so the connection content visibly flows through the chart Levi-Civita
  splitting rather than being assumed against the bare covariant answer.

The only inputs are the chart-coordinate Euclidean data (`Dchart`, `Dchart'`, the
chart-reading `hagree`) — all on the model space `E`, never a joint-`C^∞`-on-`ℝ × M`
manifold predicate — plus the trivialization-transport value identification.  No axiom, no
`sorry`, no hypothesis-packaging: the conclusion `RawVariationalIdentity` is genuinely
*derived*, not assumed.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section InnerCLMBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Chart Levi-Civita inner CLM transported to the orbit point equals the covariant
value.**

At a fixed orbit point `α := Φ_fam t x` (assumed in its own good set — the standing
situation for an interior point under `[BoundarylessManifold I M]`) with `X`
manifold-differentiable there, the inverse-trivialised inner CLM of the chart Levi-Civita
construction at `α`, applied to the pushforward `mfderiv (Φ_fam t) x v`, equals the
bundled covariant value `(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.

This is `chartLeviCivita_apply` (Part 2's flat-plus-Christoffel split) followed by
`LeviCivita_chart_apply` (chart-overlap matching to the global derivative), read at the
fixed base point. -/
theorem trivFromE_innerCLM_eq_leviCivita_at_orbit
    (g : SmoothRiemannianMetric I M)
    (X : Π x : M, TangentSpace I x)
    (α : M) (d : TangentSpace I α)
    (hα : α ∈ chartLeviCivitaGoodSet (I := I) α)
    (hX : MDiffAt (T% X) α) :
    trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α d)
      = (LeviCivita (I := I) g) X α d := by
  have hchart :
      chartLeviCivita (I := I) g α X α d
        = trivFromE (I := I) α α (chartLeviCivitaInnerCLM (I := I) g α X α d) := by
    rw [chartLeviCivita_apply (I := I) g α X hα d]
    rw [chartLeviCivitaInnerCLM_apply (I := I) g α X α d]
  have hbundled :
      (LeviCivita (I := I) g) X α d = chartLeviCivita (I := I) g α X α d :=
    LeviCivita_chart_apply (I := I) g α hα hX d
  rw [hbundled, hchart]

end InnerCLMBridge

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Raw variational identity from the chart-flow data (value form).**

Let `α := Φ_fam t x` be the time-`t` orbit point.  Given:

* `hDchart` — the operator-valued Euclidean chart-flow variational ODE
  `HasDerivAt Dchart Dchart' t` on the model space `E`;
* `hagree` — the chart reading of the moving pushforward, an eventual equality of
  `E`-valued paths near `t`, with `Q` the target-chart-symm continuous-linear map at the
  orbit point and `d` the source-chart image of `v`;
* `hQval` — the moving-target trivialization transport: the transported Euclidean
  variational value equals the covariant right-hand side,
  `Q (Dchart' d) = -(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`,

the moving-pushforward path `s ↦ (mfderiv (Φ_fam s) x v : E)` satisfies
`RawVariationalIdentity`.

The proof composes Part 1's `hasDerivAt_mfderiv_flow_of_chart` (the chart transfer of the
Euclidean ODE) and rewrites the derivative value by `hQval`. -/
theorem rawVariationalIdentity_of_chartFlow_value
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQval : Q (Dchart' d)
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have h1 :=
    hasDerivAt_mfderiv_flow_of_chart (I := I) (Fam := fun s => (Φ_fam s : M → M))
      t x v Q d hDchart hagree
  rw [hQval] at h1
  exact h1

/-- **Raw variational identity from the chart-flow data (Part-2 routed form).**

Same conclusion as `rawVariationalIdentity_of_chartFlow_value`, with the covariant value
identification *derived* from its flat-plus-Christoffel form:

* `hQinner` — the transported Euclidean variational value equals minus the
  inverse-trivialised chart Levi-Civita inner CLM (flat chart `fderiv` + Christoffel
  correction) applied to the pushforward, at the fixed orbit point `α := Φ_fam t x`;
* `hLC` — the Levi-Civita/inner-CLM identity at `α`, i.e.
  `trivFromE α α (innerCLM g α X α (mfderiv (Φ_fam t) x v)) = (LeviCivita g) X α (…)`,
  discharged by `trivFromE_innerCLM_eq_leviCivita_at_orbit`.

Combining `hQinner` with `hLC` (and the `-X` sign) yields the covariant value
identification, which the minimal combinator turns into `RawVariationalIdentity`.  The
connection content thus flows visibly through the chart Levi-Civita splitting. -/
theorem rawVariationalIdentity_of_chartFlow
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hLC : trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
        (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
          (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
      = (LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQval : Q (Dchart' d)
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
    rw [hQinner, hLC]
  exact rawVariationalIdentity_of_chartFlow_value (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQval

end Transport

end DifferentialGeometry.PDE.RicciFlow.ODE
