import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftTransport

/-!
# Covariant-value closure of the variational-lift transport

`SmoothInSpace/VariationalLiftTransport.lean` proves two transport combinators that
turn the chart-coordinate Euclidean variational data of the manifold flow into the
predicate `RawVariationalIdentity`:

* `rawVariationalIdentity_of_chartFlow_value` — takes the covariant value identification
  `Q (Dchart' d) = -(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)` *ready-made*;
* `rawVariationalIdentity_of_chartFlow` — takes the value identification in its
  *flat-plus-Christoffel* form `hQinner` (transported Euclidean value = minus the
  inverse-trivialised chart Levi-Civita inner CLM applied to the pushforward) **together
  with** a separately-supplied Levi-Civita / inner-CLM identity `hLC` at the orbit point.

The second combinator therefore still forces the caller to discharge `hLC` by hand —
i.e. to invoke `trivFromE_innerCLM_eq_leviCivita_at_orbit` with the good-set membership of
the orbit point `Φ_fam t x` and the manifold-differentiability of the generating field
`X` there.  Both of those facts are *automatic* for the data actually in play:

* the orbit point lies in its own chart Levi-Civita good set
  (`self_mem_chartLeviCivitaGoodSet`, available unconditionally under
  `[BoundarylessManifold I M]`), and
* a bundled smooth section `X : Cₛ^∞⟮I; E, TangentSpace I⟯` is manifold-differentiable at
  every point.

This file closes that loose end.  It proves, at the orbit point, the connection-content
identification with the good-set / smoothness obligations discharged internally, and then
re-exports a single combinator that takes only the *flat-plus-Christoffel* value reading
`hQinner` (an equality of vectors in the model fibre `E`) plus the chart-coordinate
Euclidean ODE and chart-reading agreement, and produces `RawVariationalIdentity`.

## The instance bookkeeping (two `E`-norm worlds)

`trivFromE_innerCLM_eq_leviCivita_at_orbit` lives in the world where `E` carries both a
standalone `[NormedSpace ℝ E]` (needed for the tangent-bundle charted space underlying the
`T% X` section-differentiability `MDiffAt (T% X) (Φ_fam t x)`) and `[InnerProductSpace ℝ E]`.
The predicate `RawVariationalIdentity`, by contrast, is elaborated in the
`[InnerProductSpace ℝ E]`-only world (the standing world of the variational-flow file), and
does not typecheck once a *separate* `[NormedSpace ℝ E]` instance is in scope.

The two worlds are bridged by an *equality of vectors in `E`* — never by a `HasDerivAt` —
so the connection content is proved in the two-instance world as a pure `E`-equation
(`negCovariant_value_of_innerCLM_value`), and the `RawVariationalIdentity` assembly that
consumes it runs in the single-instance world (`rawVariationalIdentity_of_chartFlow_innerCLM`),
calling the equation across the boundary.  `InnerProductSpace.toNormedSpace` supplies the
standalone normed-space instance the equation's signature needs, so the cross-world call is
clean.

## What is and is not proved here

The conclusion `RawVariationalIdentity` is the *vector-valued* `HasDerivAt` for the
pushforward path; the hypotheses are the operator-valued Euclidean ODE `hDchart`, the
chart-reading **eventual** agreement `hagree` (an `=ᶠ[𝓝 t]` equality, valid precisely
because the orbit `s ↦ Φ_fam s x` stays in the fixed target chart for `s` near `t`; it is
*not* asserted globally), and the flat-plus-Christoffel value reading `hQinner` (an
`E`-equation).  None of these is, or trivially yields, the `HasDerivAt` conclusion, so no
hypothesis-packaging occurs.  The genuinely new content is the connection-content
identification at the orbit point with the good-set / smoothness side conditions discharged
internally — the chart formula `∂_j X^i = (∇X)^i_j - Γ^i_{jk} X^k` matched to the bundled
covariant value through `trivFromE_innerCLM_eq_leviCivita_at_orbit`.

What is *not* closed here (and is not introduced as any axiom): the construction of the
concrete chart-flow data `Dchart`, `Q`, `d` for a specific `Φ_fam`, and the proof of the
chart-convention bridge that yields `hQinner` from the BanachIC-representation Euclidean
variational value.  Those remain inputs, supplied per-flow.  No `sorry`, no `axiom`, no
`HasLocallyConstantChartAt`-style hypothesis appears anywhere in this file.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Orbit-point Levi-Civita / inner-CLM identity (side conditions discharged).**

At the orbit point `α := Φ_fam t x`, the inverse-trivialised chart Levi-Civita inner CLM
(flat chart `fderiv` summand plus Christoffel correction) of a bundled smooth section `X`,
applied to the pushforward `mfderiv (Φ_fam t) x v`, equals the bundled covariant value
`(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.

This is `trivFromE_innerCLM_eq_leviCivita_at_orbit` with its two side conditions discharged
internally:

* the good-set membership `Φ_fam t x ∈ chartLeviCivitaGoodSet (Φ_fam t x)` is automatic from
  `self_mem_chartLeviCivitaGoodSet` (every point lies in its own chart Levi-Civita good set
  under `[BoundarylessManifold I M]`);
* the manifold-differentiability `MDiffAt (T% X) (Φ_fam t x)` is automatic for the bundled
  smooth section `X` via `X.contMDiff`. -/
theorem leviCivita_orbit_value_eq
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) :
    trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
        (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
          (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v))
      = (LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
  have hα : (Φ_fam t x) ∈ chartLeviCivitaGoodSet (I := I) (Φ_fam t x) :=
    self_mem_chartLeviCivitaGoodSet (I := I) (Φ_fam t x)
  have hX : MDiffAt (T% (X : ∀ x : M, TangentSpace I x)) (Φ_fam t x) :=
    (X.contMDiff (Φ_fam t x)).mdifferentiableAt (by simp)
  exact trivFromE_innerCLM_eq_leviCivita_at_orbit (I := I) g
    (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v) hα hX

/-- **Flat-plus-Christoffel value reading ⇒ covariant value.**

Given a value `val : E` identified with *minus* the inverse-trivialised chart Levi-Civita
inner CLM of a bundled smooth section `X`, applied to the pushforward `mfderiv (Φ_fam t) x v`
at the orbit point (the flat chart `fderiv` summand plus the Christoffel correction —
`hQinner`), `val` equals minus the bundled covariant value
`-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`.

This combines `hQinner` with `leviCivita_orbit_value_eq`, threading the `-X` sign through
linearly.  The result is an `E`-equation — the value identification consumed by the
variational-lift transport combinator. -/
theorem negCovariant_value_of_innerCLM_value
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) (val : E)
    (hQinner : val
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    val
      = -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v) := by
  rw [hQinner, leviCivita_orbit_value_eq (I := I) g X Φ_fam t x v]

end OrbitValue

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Raw variational identity from chart-flow data, Christoffel-routed, side conditions
discharged.**

Let `α := Φ_fam t x` be the time-`t` orbit point.  Given:

* `hDchart` — the operator-valued Euclidean chart-flow variational ODE
  `HasDerivAt Dchart Dchart' t` on the model space `E`;
* `hagree` — the chart reading of the moving pushforward, an **eventual** equality of
  `E`-valued paths near `t` (`=ᶠ[𝓝 t]`, valid because the orbit stays in the fixed target
  chart for `s` near `t`; *not* a global identity), with `Q` the target-chart-symm
  continuous-linear map at the orbit point and `d` the source-chart image of `v`;
* `hQinner` — the transported Euclidean variational value equals minus the
  inverse-trivialised chart Levi-Civita inner CLM (flat chart `fderiv` summand plus
  Christoffel correction) applied to the pushforward, at the orbit point,

the moving-pushforward path `s ↦ (mfderiv (Φ_fam s) x v : E)` satisfies
`RawVariationalIdentity`.

This is the counterpart of `rawVariationalIdentity_of_chartFlow` that **does not** require
the caller to supply the Levi-Civita / inner-CLM identity `hLC`: that identity is discharged
internally by `negCovariant_value_of_innerCLM_value` (which routes through
`leviCivita_orbit_value_eq`, automatically discharging the good-set membership and the
section's manifold-differentiability at the orbit point).  The connection content thus flows
visibly through the chart Levi-Civita flat-plus-Christoffel splitting.

The conclusion `RawVariationalIdentity` is a *vector-valued* `HasDerivAt`; the hypotheses are
the operator-valued ODE `hDchart`, the chart-reading agreement `hagree`, and the
`E`-equation `hQinner`.  None is, or trivially yields, the `HasDerivAt` conclusion, so no
hypothesis-packaging occurs. -/
theorem rawVariationalIdentity_of_chartFlow_innerCLM
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (d : E)
    {Dchart : ℝ → (E →L[ℝ] E)} {Dchart' : E →L[ℝ] E}
    (hDchart : HasDerivAt Dchart Dchart' t)
    (hagree : (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
      =ᶠ[𝓝 t] (fun s : ℝ => Q (Dchart s d)))
    (hQinner : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (chartLeviCivitaInnerCLM (I := I) g (Φ_fam t x)
            (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
            (mfderiv I I (Φ_fam t : M → M) x v))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hQval := negCovariant_value_of_innerCLM_value (I := I) g X Φ_fam t x v
    (Q (Dchart' d)) hQinner
  exact rawVariationalIdentity_of_chartFlow_value (I := I) g X Φ_fam t x v Q d
    hDchart hagree hQval

end Assembly

end DifferentialGeometry.PDE.RicciFlow.ODE
