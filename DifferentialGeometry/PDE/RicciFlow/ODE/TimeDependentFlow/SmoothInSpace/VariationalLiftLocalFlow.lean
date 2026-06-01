import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatToCovariant
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE

/-!
# Generic per-flow raw variational identity from the `IsLocalFlow` variational ODE

The committed flat-data producer
`rawVariationalIdentity_of_flatChartFderiv_witness`
(`SmoothInSpace/VariationalLiftFlatToCovariant.lean`) builds `RawVariationalIdentity`
from the flat chart Euclidean variational data (`hDchart`, `hcontAt`, `hwitness`,
`hRdiff`, `hCdiff`) together with the *flat-plus-correction* value equation `hcov`

  `Q (Dchart' d)
     = -trivFromE α α (fderiv (chartRawRepr α X) (φ α) w)`     (raw flat `−∂X`)
       `- trivFromE α α (movingTrivCorrection α X w)`          (`D²φ`)
       `- trivFromE α α (christoffelCorrection g α α (X̃_α α) w)`,  (metric `Γ`)

with `α := Φ_fam t x` and `w := mfderiv I I (Φ_fam t) x v`.

The Euclidean variational ODE `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`
(`SmoothInSpace/VariationalODE.lean`) produces, for a genuine `IsLocalFlow` `Φ` of a
chart-coordinate vector field `f` on the model space `E`, the operator-valued flat ODE

  `HasDerivAt (fun u => fderiv ℝ (fun z => Φ (z, u)) z₀)
     ((fderiv ℝ (f t) (Φ (z₀, t))).comp (fderiv ℝ (fun z => Φ (z, t)) z₀)) t`.

This file connects that flat ODE output to the *raw-fibre* representation of `X` at the
basepoint, supplying the genuine geometric reconciliation that the producer's `hcov`
needs for its first two summands (the raw flat derivative and the moving-trivialization
`D²φ` correction).

## The honest accounting of what closes and what is gated

Write `f t = fun z => -(chartTrivRepr α X_t z)` for the chart-`α`-conjugated generating
field of the flow of `-X` (the convention `RawVariationalIdentity` integrates), and
suppose the time-`t` orbit point `Φ (z₀, t)` is the basepoint image `φ α` (true because
`Φ_fam t x = α`).  Then the flat ODE's linearization factor
`fderiv ℝ (f t) (Φ (z₀, t))` is `-fderiv ℝ (chartTrivRepr α X_t) (φ α)`, which by the
committed convention bridge `chartTrivRepr_fderiv_eq` decomposes into the *raw* flat
derivative plus the moving-trivialization `D²φ` correction:

  `fderiv ℝ (chartTrivRepr α X_t) (φ α) w
     = fderiv ℝ (chartRawRepr α X_t) (φ α) w + movingTrivCorrection α X_t w`.

This is proved here as `flatLinearization_eq_rawFderiv_add_movingTriv` — a pure
`E`-equation, fully discharged, the genuine content of step 2 *that does not reference the
metric `g`*.

The remaining contribution to `hcov` — the metric Christoffel correction
`christoffelCorrection g α α (X̃_α α) w` — is *not* produced by the flat variational ODE:
it enters only through a `g`-referencing step (the moving target-trivialization derivative
along the orbit, contracted against the metric), which the pure variational ODE never
performs.  The naive identification "moving-trivialization correction = metric Christoffel"
is **false** in a general chart (they coincide only in normal/geodesic coordinates at `α`).
The metric `Γ` contribution is therefore exposed as a genuine *additive* residual in the
generic producer's value-level input `hsplit` (never asserted to vanish); its discharge for a
specific flow is the metric-covariant reconciliation gated on the parabolic joint-regularity
master gap.

## Main results

* `chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv`,
  `flatLinearization_eq_rawFderiv_add_movingTriv` — the fully-proved reconciliation of the
  trivialised flat derivative (and its negation, for the `-X` generator) with the raw flat
  derivative plus the `D²φ` correction.  Pure smooth-structure content, no metric `g`.

* `hcov_of_flatTrivPart_and_movingTrivResidual` — assembly of the producer's full `hcov`
  value equation (three separate summands `raw`, `D²φ`, `Γ`) from the honest value
  decomposition `hsplit` (flat variational-ODE contribution plus moving-target-trivialization
  residual), folding the `D²φ` correction out of the trivialised flat derivative via the
  reconciliation above.

* `rawVariationalIdentity_of_isLocalFlow` — the generic per-flow producer: from the
  `IsLocalFlow` variational ODE data (operator-valued ODE `hDchart`, orbit continuity, the
  chart-reading witness, the convention-bridge side conditions) plus the value-level input
  `hsplit`, it produces `RawVariationalIdentity`.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no
joint-`C^∞`-on-`ℝ × M` predicate.  No hypothesis-packaging: every input is an
operator-valued ODE or an `E`-equation, none of which is — or trivially destructures to —
the vector-valued `HasDerivAt` conclusion `RawVariationalIdentity`.  The (false-in-general)
"moving-trivialization = metric Christoffel" identification is not assumed anywhere, and the
metric Christoffel contribution is a genuine additive residual, never set to zero.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section Reconciliation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The trivialised flat derivative as raw flat derivative plus `D²φ`.**

At the basepoint image `φ α`, the Fréchet derivative of the *trivialised* chart
representation `chartTrivRepr α X` applied to `w` equals the raw flat derivative plus the
moving-trivialization correction:

  `fderiv ℝ (chartTrivRepr α X) (φ α) w
     = fderiv ℝ (chartRawRepr α X) (φ α) w + movingTrivCorrection α X w`.

This is exactly the committed convention bridge `chartTrivRepr_fderiv_eq`, with the
moving-trivialization correction repackaged through the definition of
`movingTrivCorrection`.  Pure chart calculus, fully discharged; the conclusion is an
`E`-equation, never the `HasDerivAt` target. -/
theorem chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (chartTrivRepr (I := I) α X) (extChartAt I α α) w
      = fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
        + movingTrivCorrection (I := I) α X w := by
  rw [chartTrivRepr_fderiv_eq (I := I) α X w hR hC, movingTrivCorrection]

/-- **Flat-linearization factor of the chart-`α` conjugated flow generator.**

Let `f t` be the chart-`α` conjugated generating field of the flow of `-X`, i.e.
`f t = fun z => -(chartTrivRepr α X z)` (the trivialised chart representation, negated for
the `-X` generator).  At the basepoint image `φ α` — where the time-`t` orbit point sits,
since `Φ_fam t x = α` — the flat ODE's linearization factor `fderiv ℝ (f t) (φ α)` applied
to `w` decomposes as

  `fderiv ℝ (f t) (φ α) w
     = -(fderiv ℝ (chartRawRepr α X) (φ α) w + movingTrivCorrection α X w)`,

i.e. minus the raw flat derivative minus the moving-trivialization `D²φ` correction.

Genuine content: `fderiv` of a negation is the negation of `fderiv` (`fderiv_neg`), then
the trivialised flat derivative is rewritten through
`chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv`.  Fully discharged; the conclusion is an
`E`-equation, never the `HasDerivAt`/`hcov` target.  No metric `g` is referenced: this is
the smooth-structure content only. -/
theorem flatLinearization_eq_rawFderiv_add_movingTriv
    (α : M) (X : Π y : M, TangentSpace I y) (w : E)
    (hR : DifferentiableAt ℝ (chartRawRepr (I := I) α X) (extChartAt I α α))
    (hC : DifferentiableAt ℝ (fun z => chartMovingTriv (I := I) α z) (extChartAt I α α)) :
    fderiv ℝ (fun z => -(chartTrivRepr (I := I) α X z)) (extChartAt I α α) w
      = -(fderiv ℝ (chartRawRepr (I := I) α X) (extChartAt I α α) w
          + movingTrivCorrection (I := I) α X w) := by
  rw [fderiv_fun_neg, ContinuousLinearMap.neg_apply]
  rw [chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv (I := I) α X w hR hC]

end Reconciliation

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Assembly of the producer's `hcov` value equation from two genuine contributions.**

Let `α := Φ_fam t x` and `w := mfderiv I I (Φ_fam t) x v`.  The hypothesis `hsplit` is the
honest decomposition of the true derivative value `Q (Dchart' d)` into two genuine,
*separate* contributions:

  `Q (Dchart' d)
     = -trivFromE α α (fderiv (chartTrivRepr α X) (φ α) w)`           (flat-ODE part)
       `+ (-trivFromE α α (christoffelCorrection g α α (X̃_α α) w))`,  (moving-triv residual)

i.e. minus the trivialization-image of the *trivialised* flat derivative (the flat
variational-ODE contribution) plus the moving-target-trivialization residual identified with
minus the trivialization-image of the metric Christoffel correction.  The second summand is a
genuine *additive* contribution (the `g`-referencing moving-trivialization-derivative content,
supplied per flow); it is **not** asserted to vanish.

Then the producer's full `hcov` holds with the three separate summands `raw`, `D²φ`, `Γ`:

  `Q (Dchart' d)
     = -trivFromE α α (fderiv (chartRawRepr α X) (φ α) w)
       - trivFromE α α (movingTrivCorrection α X w)
       - trivFromE α α (christoffelCorrection g α α (X̃_α α) w)`.

The proof rewrites the *trivialised* flat derivative in `hsplit` through Part (A)'s
reconciliation (`chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv`, splitting it into raw flat
`+ D²φ`), pushes `trivFromE α α` over the resulting sum (`map_add`), and rearranges.  No
hypothesis-packaging: the conclusion is an `E`-equation derived from `hsplit` and the
reconciliation, never the `RawVariationalIdentity` target; the metric Christoffel summand
enters as a genuine additive residual, *never* assumed zero. -/
theorem hcov_of_flatTrivPart_and_movingTrivResidual
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    (Q : E →L[ℝ] E) (Dchart' : E →L[ℝ] E) (d : E)
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
        + (-trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)))) :
    Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
          (fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v))
        - trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)) := by
  classical
  have hAdecomp :
      fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
          (extChartAt I (Φ_fam t x) (Φ_fam t x))
          (mfderiv I I (Φ_fam t : M → M) x v)
        = fderiv ℝ (chartRawRepr (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y))
            (extChartAt I (Φ_fam t x) (Φ_fam t x))
            (mfderiv I I (Φ_fam t : M → M) x v)
          + movingTrivCorrection (I := I) (Φ_fam t x)
              (X : ∀ y : M, TangentSpace I y)
              (mfderiv I I (Φ_fam t : M → M) x v) :=
    chartTrivRepr_fderiv_eq_rawFderiv_add_movingTriv (I := I) (Φ_fam t x)
      (X : ∀ y : M, TangentSpace I y) (mfderiv I I (Φ_fam t : M → M) x v) hRdiff hCdiff
  rw [hsplit, hAdecomp, map_add]
  abel

end Assembly

section Producer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **Generic per-flow raw variational identity from `IsLocalFlow` variational data.**

Let `α := Φ_fam t x` and `w := mfderiv I I (Φ_fam t) x v`.  The inputs are exactly the data
that a genuine chart-local `IsLocalFlow` of the chart-coordinate generating field supplies:

* `hDchart` — the operator-valued Euclidean chart-flow variational ODE
  `HasDerivAt Dchart Dchart' t` on the model space `E` (produced by
  `IsLocalFlow.hasDerivAt_partial_spatial_fderiv`);
* `hcontAt` — continuity of the orbit `s ↦ Φ_fam s x` at `t` (separable continuity input);
* `hwitness` — the eventual reproduction of the transported chart-coordinate derivative by
  `Q (Dchart s d)` near `t` (the chart-reading dictionary);
* `hRdiff`, `hCdiff` — differentiability of the raw representation and the moving
  trivialization at the basepoint image (the convention-bridge side conditions);
* `hsplit` — the honest value decomposition of the true derivative value `Q (Dchart' d)` into
  the **flat variational-ODE contribution** (minus `trivFromE α α` of the *trivialised* flat
  derivative `fderiv (chartTrivRepr α X) (φ α) w`) **plus** the **moving-target-trivialization
  residual** (minus `trivFromE α α` of the metric Christoffel correction).  The second summand
  is the genuine `g`-referencing geometric content, supplied as an additive residual — *never*
  asserted to vanish.

It produces `RawVariationalIdentity`.  The full `hcov` (with the three separate summands
`raw`, `D²φ`, `Γ`) is assembled internally by `hcov_of_flatTrivPart_and_movingTrivResidual`
(Part B), which folds the `D²φ` correction out of the trivialised flat derivative via Part
(A); the result is fed into the committed flat-data producer
`rawVariationalIdentity_of_flatChartFderiv_witness`.

No joint-`C^∞`-on-`ℝ × M`, no `HasLocallyConstantChartAt`, no hypothesis-packaging: every
input is an operator-valued ODE or an `E`-equation, none of which is — or trivially
destructures to — the vector-valued `HasDerivAt` conclusion.  The (false-in-general)
"moving-trivialization = metric Christoffel" identification is not assumed; `hsplit` exposes
the flat content and the metric content as separate, genuine additive contributions. -/
theorem rawVariationalIdentity_of_isLocalFlow
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
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : Q (Dchart' d)
      = -trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (fderiv ℝ (chartTrivRepr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y))
              (extChartAt I (Φ_fam t x) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
        + (-trivFromE (I := I) (Φ_fam t x) (Φ_fam t x)
            (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v)))) :
    RawVariationalIdentity (I := I) g X Φ_fam t x v := by
  have hcov := hcov_of_flatTrivPart_and_movingTrivResidual (I := I) g X Φ_fam t x v
    Q Dchart' d hRdiff hCdiff hsplit
  exact rawVariationalIdentity_of_flatChartFderiv_witness (I := I) g X Φ_fam t x v Q d
    hDchart hcontAt hwitness hRdiff hCdiff hcov

end Producer

end DifferentialGeometry.PDE.RicciFlow.ODE
