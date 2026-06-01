import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftChartDictionary

/-!
# The trivialization-convention bridge for the chart-coordinate variational data

The combinator `rawVariationalIdentity_of_chartFderiv_witness`
(`SmoothInSpace/VariationalLiftChartDictionary.lean`) produces `RawVariationalIdentity`
from chart-coordinate Euclidean variational data once a single value equation `hQinner`
is supplied:

  `Q (Dchart' d)
    = -trivFromE α α (chartLeviCivitaInnerCLM g α X α (mfderiv I I (Φ_fam t) x v))`,

with `α := Φ_fam t x`.  The right-hand side's inner CLM splits, by definition
(`chartLeviCivitaInnerCLM_apply`), as

  `chartLeviCivitaInnerCLM g α X α w
     = fderiv ℝ (X̃_α ∘ φ.symm) (φ α) (trivToE α α w)
       + christoffelCorrection g α α (X̃_α α) w`,

where `φ := extChartAt I α` and `X̃_α := chartE_section_repr α X` is the **trivialised**
chart representation of the section, `X̃_α y = trivToE α y (X y)`.

This file isolates the genuinely-new chart-calculus content needed to relate the
*Euclidean* variational right-hand side — built from the **raw-fibre** chart
representation of the vector field — to that trivialised flat summand.

## The two chart representations of the generating vector field

The Euclidean variational ODE `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
(`SmoothInSpace/VariationalODE.lean`) is run on the chart flow of the **raw-fibre**
representation

  `R(z) := (X (φ.symm z) : E)`        (`chartRawRepr`),

i.e. the value `X (φ.symm z) : TangentSpace I (φ.symm z) = E`, read with **no**
trivialization applied (this is exactly the `f_chart` consumed by
`ChartLocalPicardData.contDiffOn_top` in `BanachIC.lean`).  The chart Levi-Civita
inner CLM, by contrast, is built from the **trivialised** representation

  `T(z) := X̃_α (φ.symm z) = trivToE α (φ.symm z) (X (φ.symm z))`   (`chartTrivRepr`).

The two are reconciled by the *moving* trivialization CLM
`C(z) := trivToE α (φ.symm z)`:

  `T(z) = C(z) (R(z))`.

Differentiating, the product rule (`HasFDerivAt.clm_apply` / `fderiv_clm_apply`) gives,
at the basepoint image `z₀ := φ α` (where `C(z₀) = trivToE α α`):

  `fderiv ℝ T z₀ h = (trivToE α α).comp (fderiv ℝ R z₀) h + (fderiv ℝ C z₀ h) (R z₀)`.

The first summand is the trivialization-image of the **raw** flat derivative
`fderiv ℝ R z₀` — the operator the Euclidean variational ODE actually produces.  The
second summand,

  `(fderiv ℝ C z₀ h) (R z₀)`,

is the genuine **moving-trivialization correction**: the derivative of the tangent-bundle
chart change `z ↦ trivToE α (φ.symm z)` (a smooth-structure object, the chart-transition
first jet — see `extChartAt_transition_hasFDerivWithinAt_on_overlap_image` and
`trivToE_trivFromE_eq_fderiv_chartChange`), applied to the raw fibre value `R(z₀) = X(α)`.

## What this file proves, and the honest accounting of the remaining gap

The product-rule decomposition `chartTrivRepr_fderiv_eq` is proved unconditionally as a
genuine chart-calculus identity (no hypothesis-packaging, no `HasLocallyConstantChartAt`):
it exposes precisely how the trivialised flat derivative differs from the raw flat
derivative.  It is the exact convention bridge between the Euclidean variational
right-hand side (raw representation) and the flat summand of `chartLeviCivitaInnerCLM`
(trivialised representation).

The decomposition makes the obstruction to `hQinner` explicit and verifiable:

* the Euclidean variational ODE produces the **raw flat** derivative `fderiv ℝ R z₀`;
* `chartLeviCivitaInnerCLM` requires the **trivialised flat** derivative `fderiv ℝ T z₀`
  **plus** the *metric* Christoffel correction `christoffelCorrection g α α (X̃_α α)`
  (the symbol `Γ^i_{jk}` built from `g`, `chartChristoffel`);
* the two flat derivatives differ by the **moving-trivialization correction**
  `(fderiv ℝ C z₀ ·) (R z₀)`, which is the *chart-transition* first-jet derivative — the
  classical second-derivative-of-the-chart-change term `D²φ`, see
  `chartChristoffelContraction_chart_transform` in
  `Geometry/Riemannian/Geodesic/ChartChristoffelTransform.lean`.

Consequently the moving-trivialization correction is a **smooth-structure** object,
metric-independent, and is *not equal* to the metric `christoffelCorrection` in a general
chart (they coincide only in normal/geodesic coordinates at `α`).  The value equation
`hQinner` — which equates the variational correction with the metric
`christoffelCorrection` — therefore cannot be obtained from the BanachIC raw-fibre
Euclidean variational ODE alone: the metric Christoffel can enter only through a step that
references `g`, which the pure variational ODE never does.  The reconciliation
`-∇X` (metric covariant) vs. `-∂X` (flat / Lie-type) is the classical fact that the
pushforward variation `∂_s (dΦ_s v)` produces the **Lie-type** derivative, the metric
covariant value emerging only after contraction with `g` via metric-compatibility
(downstream, in `cartan_cancellation_value_identity`).

No axiom, no `sorry`, no hypothesis-packaging is introduced: this file ships the one
genuinely-true chart-calculus identity (`chartTrivRepr_fderiv_eq`) that the closing
argument needs, stated correctly with the moving-trivialization correction in place of the
(false) metric-Christoffel correction.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The **raw-fibre** chart representation of a section: `R(z) = (X (φ.symm z) : E)`, the
value of `X` at the chart-coordinate point `z`, read with no trivialization applied (the
`TangentSpace I (φ.symm z) = E` defeq). -/
def chartRawRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  (X ((extChartAt I α).symm z) : E)

/-- The **trivialised** chart representation pulled back to the model space:
`T(z) = chartE_section_repr α X (φ.symm z) = trivToE α (φ.symm z) (X (φ.symm z))`.  This is
the map whose Fréchet derivative is the flat summand of `chartLeviCivitaInnerCLM`. -/
def chartTrivRepr (α : M) (X : Π y : M, TangentSpace I y) (z : E) : E :=
  chartE_section_repr (I := I) α X ((extChartAt I α).symm z)

/-- The **moving trivialization** CLM as a function of the chart coordinate:
`C(z) = trivToE α (φ.symm z) : TangentSpace I (φ.symm z) →L[ℝ] E`.  Under the defeq
`TangentSpace I (φ.symm z) = E` this is an `E →L[ℝ] E`. -/
def chartMovingTriv (α : M) (z : E) : E →L[ℝ] E :=
  trivToE (I := I) α ((extChartAt I α).symm z)

/-- The trivialised representation factors through the moving trivialization applied to the
raw representation: `T(z) = C(z) (R(z))`.  This is just the definition of
`chartE_section_repr` as `trivToE α (·) (X (·))`, unfolded. -/
lemma chartTrivRepr_eq_movingTriv_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (z : E) :
    chartTrivRepr (I := I) α X z
      = chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) := by
  unfold chartTrivRepr chartMovingTriv chartRawRepr
  rfl

/-- At the basepoint image `z₀ = φ α`, the moving trivialization is the identity:
`C(φ α) = trivToE α α = 1`, because the tangent-bundle coordChange from the chart at `α`
to itself, evaluated at `α`, is the identity.  This is `continuousLinearMapAt_model`-style
self-coordChange triviality routed through `trivFromE_trivToE`. -/
lemma chartMovingTriv_basepoint
    (α : M) (v : E) :
    chartMovingTriv (I := I) α (extChartAt I α α) v = v := by
  unfold chartMovingTriv
  have hself : (extChartAt I α).symm (extChartAt I α α) = α :=
    (extChartAt I α).left_inv (mem_extChartAt_source (I := I) α)
  rw [hself]
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

/-- **Convention bridge: trivialised flat derivative = raw flat derivative + moving-
trivialization correction.**

At the basepoint image `z₀ := φ α` (where the moving trivialization is the identity), the
Fréchet derivative of the trivialised chart representation `chartTrivRepr α X` decomposes
as

  `fderiv ℝ (chartTrivRepr α X) z₀ h
     = fderiv ℝ (chartRawRepr α X) z₀ h
       + (fderiv ℝ (fun z => chartMovingTriv α z) z₀ h) (chartRawRepr α X z₀)`,

i.e. the **raw** flat derivative (the operator produced by the Euclidean variational ODE)
plus the **moving-trivialization correction** `(D C · h)(R z₀)`.

The correction term is the derivative of the tangent-bundle chart change
`z ↦ trivToE α (φ.symm z)` applied to the raw fibre value `R(z₀) = X(α)`; it is a
*smooth-structure* object (the chart-transition first jet), **not** the metric Christoffel
symbol `christoffelCorrection` — see the module docstring for the consequence for the value
equation `hQinner`.

Genuine content: the bilinear product rule `fderiv_clm_apply` applied to the factorisation
`T(z) = C(z)(R(z))` (`chartTrivRepr_eq_movingTriv_rawRepr`), with the basepoint
simplification `C(φ α) = 1` (`chartMovingTriv_basepoint`).  No hypothesis-packaging: the
conclusion is an equation of `E`-vectors derived from the product rule, never the
`HasDerivAt`/`hQinner` target itself. -/
theorem chartTrivRepr_fderiv_eq
    (α : M) (X : Π y : M, TangentSpace I y) (h : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartTrivRepr (I := I) α X) (extChartAt I α α) h
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) h
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) h)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  classical
  set z₀ : E := extChartAt I α α with hz₀
  have hTeq : chartTrivRepr (I := I) α X
      = fun z => chartMovingTriv (I := I) α z (chartRawRepr (I := I) α X z) :=
    funext (fun z => chartTrivRepr_eq_movingTriv_rawRepr (I := I) α X z)
  rw [hTeq]
  rw [fderiv_clm_apply hC hR]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [chartMovingTriv_basepoint (I := I) α (fderiv ℝ (chartRawRepr (I := I) α X) z₀ h)]

/-- **The flat summand of the inner CLM, read through the raw representation.**

The flat (non-Christoffel) summand of `chartLeviCivitaInnerCLM g α X α`, namely
`fderiv ℝ (chartE_section_repr α X ∘ φ.symm) (φ α) (trivToE α α w)`, equals the raw flat
derivative `fderiv ℝ (chartRawRepr α X) (φ α) (trivToE α α w)` **plus** the moving-
trivialization correction applied to `trivToE α α w`.

This is `chartTrivRepr_fderiv_eq` rewritten with the chart pullback
`chartE_section_repr α X ∘ φ.symm = chartTrivRepr α X` (a definitional `funext`), so the
identity reads off the inner CLM's flat term directly. -/
theorem chartLeviCivita_flat_summand_eq_rawRepr
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
        (extChartAt I α α) w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + (fderiv ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α) w)
            (chartRawRepr (I := I) α X (extChartAt I α α)) := by
  have hcomp : (chartE_section_repr (I := I) α X ∘ (extChartAt I α).symm)
      = chartTrivRepr (I := I) α X := rfl
  rw [hcomp]
  exact chartTrivRepr_fderiv_eq (I := I) α X w hR hC

end Bridge

end DifferentialGeometry.PDE.RicciFlow.ODE
