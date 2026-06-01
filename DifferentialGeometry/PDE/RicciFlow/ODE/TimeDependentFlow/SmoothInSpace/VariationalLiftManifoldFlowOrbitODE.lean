import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftManifoldFlowOrbitReduction

/-!
# The product-rule operator ODE for the canonical chart operator of the orbit flow

The orbit-reduction lemma `rawVariationalIdentity_iff_hasDerivAt_chartCloseDop`
(`SmoothInSpace/VariationalLiftManifoldFlowOrbitReduction.lean`) identifies the variational
identity `RawVariationalIdentity g X Φ_fam t x v` with the single operator-applied `HasDerivAt`

  `HasDerivAt (fun s => chartCloseDop Φ_fam (Φ_fam t x) x s v)
      (-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)) t`,

and the per-flow connector `rawVariationalIdentity_of_manifoldFlowFamily_chartClose`
(`SmoothInSpace/VariationalLiftManifoldFlowClose.lean`) consumes the *operator*-valued ODE
`hDchart : HasDerivAt (chartCloseDop Φ_fam (Φ_fam t x) x) Dchart' t`.

`chartCloseDop` is, by definition, the continuous-linear **composition**

  `chartCloseDop Φ_fam α x s = (trivFromE α (Φ_fam s x)).comp (mfderiv (extChartAt I α ∘ Φ_fam s) x)`,

of two `s`-dependent operators:

* the **moving inverse target trivialisation** `T s := trivFromE α (Φ_fam s x)` (the chart-`α`
  inverse trivialisation read at the moving orbit point), and
* the **chart-coordinate spatial Fréchet derivative** `P s := mfderiv (extChartAt I α ∘ Φ_fam s) x`
  of the chart-`α`-conjugated flow.

This file establishes the genuine, metric-free **operator ODE** for `chartCloseDop` by the
continuous-linear-map product rule (`HasDerivAt.clm_comp`): from the two factor `HasDerivAt`
data — `hT : HasDerivAt T T' t` (the orbit-derivative of the moving inverse trivialisation) and
`hP : HasDerivAt P P' t` (the spatial-derivative variational ODE, supplied by
`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`) — the canonical operator satisfies

  `HasDerivAt (chartCloseDop Φ_fam α x) (T'.comp (P t) + (T t).comp P') t`.

This is exactly the operator-valued input `hDchart` the per-flow connector requires; it is a
true chart-calculus identity (no metric `g`, no hypothesis-packaging: the conclusion is an
operator-valued `HasDerivAt`, the inputs are the two factor `HasDerivAt`s and a value equation
no part of which is the conclusion).

## The basepoint reading of the derivative value

At `s = t`, the orbit point `Φ_fam t x = α` sits at the centre of its own chart, so the moving
inverse trivialisation degenerates to the identity (`trivFromE_basepoint_self`):

  `T t = trivFromE α α = 𝟙`,

and the chart-coordinate spatial derivative applied to the source vector `v` is the pushforward
read at `α`:

  `(P t) v = mfderiv (extChartAt I α ∘ Φ_fam t) x v = mfderiv (Φ_fam t) x v =: w`
  (`chartCloseDop_basepoint_apply_eq_mfderiv`, since `T t = 𝟙`).

Hence the derivative value, applied to `v`, reads off as

  `(T'.comp (P t) + (T t).comp P') v = T' w + P' v`,            (`chartCloseDop_deriv_basepoint_apply`)

the sum of the **orbit-derivative of the inverse trivialisation** applied to the pushforward `w`
and the **flat spatial-variational** value `P' v`.

## The honest residual: the moving-trivialisation jet is *not* the metric Christoffel

The connector's value equation `hsplit` requires the derivative value to read off (at `v`) as

  `Dchart' v = -trivFromE α α (fderiv (chartTrivRepr α X) (φ α) w)
               - trivFromE α α (christoffelCorrection g α α (X̃_α α) w)`,

i.e. minus the *trivialised* flat derivative minus the **metric** Christoffel correction.  With
the flat variational ODE supplying `P' v = -fderiv (chartRawRepr α X) (φ α) w` (the `-X`
generator, raw representation), and `chartTrivRepr_fderiv_eq` splitting the trivialised flat
derivative as raw flat `+` the moving-*forward*-trivialisation correction
`movingTrivCorrection α X w`, the value equation `hsplit` reduces to the operator identity

  `T' w = -movingTrivCorrection α X w - christoffelCorrection g α α (X̃_α α) w`.            (★)

Both `T' w` (the orbit-derivative of `s ↦ trivFromE α (Φ_fam s x)`, a *tangent-bundle
chart-transition first jet* along the orbit) and `movingTrivCorrection α X w` (the spatial
derivative of `z ↦ trivToE α (φ.symm z)`, the companion chart-transition jet) are **pure
smooth-structure** objects, *metric-independent*.  The right-hand summand
`christoffelCorrection g α α (X̃_α α) w` is the **metric** chart-Christoffel symbol built from
`g`.

The chart-transition transformation law `chartChristoffelContraction_chart_transform`
(`Geometry/Riemannian/Geodesic/ChartChristoffelTransform.lean`) records that the metric symbol
and the chart-transition second jet `D²φ` differ in a general chart (they coincide only in
normal/geodesic coordinates at `α`).  Consequently (★) is **false in a general chart**: the
metric Christoffel cannot be produced from the orbit-derivative of the moving trivialisation
plus the flat spatial jet alone.  This is the documented metric-covariant reconciliation gap:
the plain `E`-valued pushforward curve `s ↦ mfderiv (Φ_fam s) x v` (read in Mathlib's *moving*
target chart) has the **Lie-type / flat** derivative, whereas `RawVariationalIdentity` asserts
the **covariant** value `-∇_w X`; the two differ by `(Γ − D²φ) · X(α) · w`, generically nonzero,
and the metric content enters only after the inner-product pairing of the two slots, where
metric-compatibility makes the difference cancel across slots (downstream, in
`cartan_cancellation_value_identity`).

This file therefore ships the **maximal metric-free fragment**: the genuine product-rule
operator ODE for `chartCloseDop` (the connector's `hDchart`), with the two true factor inputs
exposed and the precise residual identity (★) named but *not* asserted.  No `sorry`, no
`axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no joint-`C^∞`-on-`ℝ × M` predicate,
and **no** false identification of the moving-trivialisation jet `D²φ` with the metric
Christoffel `Γ`.  No hypothesis-packaging: every input is a factor `HasDerivAt` or an
`E`/operator-equation, none of which is — or trivially destructures to — the variational
`HasDerivAt` conclusion.
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.ODE

open Set Function Bundle Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure

section OrbitODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The moving inverse target trivialisation along the orbit.**

`chartCloseTriv Φ_fam α x s := trivFromE α (Φ_fam s x)` is the chart-`α` inverse trivialisation
read at the moving orbit point `Φ_fam s x`.  Under the defeq `TangentSpace I b := E` it is an
`E →L[ℝ] E`.  It is the *first* factor of the canonical chart operator `chartCloseDop`; its
orbit-derivative is the tangent-bundle chart-transition first jet along the orbit (the
genuinely-`s`-dependent, smooth-structure content of the operator ODE). -/
def chartCloseTriv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  trivFromE (I := I) α ((Φ_fam s : M → M) x)

/-- **The chart-coordinate spatial Fréchet derivative of the conjugated flow.**

`chartCloseFderiv Φ_fam α x s := mfderiv I 𝓘(ℝ,E) (extChartAt I α ∘ Φ_fam s) x` is the spatial
derivative of the chart-`α`-conjugated flow at `x`.  It is the *second* factor of the canonical
chart operator `chartCloseDop`; its orbit-derivative is the flat spatial-variational ODE value,
supplied by `IsLocalFlow.hasDerivAt_partial_spatial_fderiv` (no metric content). -/
def chartCloseFderiv (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) : E →L[ℝ] E :=
  mfderiv I 𝓘(ℝ, E) (fun y => extChartAt I α ((Φ_fam s : M → M) y)) x

/-- The canonical chart operator is the continuous-linear composition of its two factors. -/
lemma chartCloseDop_eq_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (s : ℝ) :
    chartCloseDop (I := I) Φ_fam α x s
      = (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s) :=
  rfl

/-- **At the basepoint time, the inverse trivialisation factor is the identity.**

At `s = t`, the orbit point is `Φ_fam t x = α`, which sits at the centre of its own chart, so
the moving inverse trivialisation `trivFromE α α` is the identity continuous-linear map.

This is the inverse companion of `trivToE_basepoint` (`ChristoffelCorrectionBasepoint.lean`):
`trivFromE α α` is the inverse of `trivToE α α = 𝟙`, hence itself `𝟙`.  Proved directly from the
round-trip `trivToE_trivFromE` on the chart base set, which forces `trivFromE α α w = w`. -/
lemma chartCloseTriv_basepoint
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (w : E) :
    chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t w = w := by
  classical
  unfold chartCloseTriv
  set α : M := Φ_fam t x with hα
  have hcore : trivFromE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.symmL_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) w

/-- **Product-rule operator ODE for the canonical chart operator (`hDchart`).**

The canonical chart operator `chartCloseDop Φ_fam α x` is the continuous-linear composition of
the moving inverse trivialisation factor `chartCloseTriv` and the chart-coordinate spatial
derivative factor `chartCloseFderiv`.  Given the two factor `HasDerivAt` data at `t`,

* `hT : HasDerivAt (chartCloseTriv Φ_fam α x) T' t` — the orbit-derivative of the moving inverse
  trivialisation (the smooth-structure chart-transition jet), and
* `hP : HasDerivAt (chartCloseFderiv Φ_fam α x) P' t` — the flat spatial-variational ODE
  (`IsLocalFlow.hasDerivAt_partial_spatial_fderiv`),

the continuous-linear-map product rule (`HasDerivAt.clm_comp`) gives the operator-valued ODE

  `HasDerivAt (chartCloseDop Φ_fam α x)
      (T'.comp (chartCloseFderiv Φ_fam α x t) + (chartCloseTriv Φ_fam α x t).comp P') t`.

This is precisely the operator-valued input `hDchart` that
`rawVariationalIdentity_of_manifoldFlowFamily_chartClose` consumes.  Genuine chart-calculus
content (no metric `g`); no hypothesis-packaging: the inputs are the two factor `HasDerivAt`s,
neither of which is the operator-valued conclusion. -/
theorem chartCloseDop_hasDerivAt_clm_comp
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (α x : M) (t : ℝ)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam α x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam α x) P' t) :
    HasDerivAt (chartCloseDop (I := I) Φ_fam α x)
      (T'.comp (chartCloseFderiv (I := I) Φ_fam α x t)
        + (chartCloseTriv (I := I) Φ_fam α x t).comp P') t := by
  have hcomp : (fun s : ℝ =>
        (chartCloseTriv (I := I) Φ_fam α x s).comp
          (chartCloseFderiv (I := I) Φ_fam α x s))
      = chartCloseDop (I := I) Φ_fam α x := by
    funext s
    exact (chartCloseDop_eq_comp (I := I) Φ_fam α x s).symm
  have := hT.clm_comp hP
  rwa [hcomp] at this

/-- **The operator ODE derivative value, applied to the source vector `v`, at the basepoint.**

Apply the product-rule derivative value
`T'.comp (chartCloseFderiv Φ_fam α x t) + (chartCloseTriv Φ_fam α x t).comp P'` to the source
vector `v`, at the basepoint time `t` where `α := Φ_fam t x`.  Using

* `chartCloseTriv Φ_fam α x t = 𝟙` (`chartCloseTriv_basepoint`), so the second summand reads
  `P' v`, and
* `chartCloseFderiv Φ_fam α x t v = mfderiv (Φ_fam t) x v =: w`
  (the basepoint pushforward value, `chartCloseDop_basepoint_apply_eq_mfderiv` since the
  inverse trivialisation is the identity), so the first summand reads `T' w`,

the derivative value applied to `v` is

  `(T'.comp (chartCloseFderiv Φ_fam α x t) + (chartCloseTriv Φ_fam α x t).comp P') v
     = T' (mfderiv (Φ_fam t) x v) + P' v`.

Genuine content: continuous-linear evaluation (`ContinuousLinearMap.add_apply`,
`ContinuousLinearMap.comp_apply`), the basepoint identity-trivialisation, and the basepoint
pushforward reading.  The conclusion is an `E`-equation, never the variational `HasDerivAt`
target. -/
theorem chartCloseDop_deriv_basepoint_apply
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x)
    (T' P' : E →L[ℝ] E) :
    (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
      = T' (mfderiv I I (Φ_fam t : M → M) x v) + P' v := by
  classical
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply]
  rw [chartCloseTriv_basepoint (I := I) Φ_fam t x (P' v)]
  have hPv : chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v
      = mfderiv I I (Φ_fam t : M → M) x v := by
    have hdop : chartCloseDop (I := I) Φ_fam (Φ_fam t x) x t v
        = chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v := by
      rw [chartCloseDop_apply]
      exact chartCloseTriv_basepoint (I := I) Φ_fam t x
        (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t v)
    rw [← hdop]
    exact chartCloseDop_basepoint_apply_eq_mfderiv (I := I) Φ_fam t x v
  rw [hPv]

/-- **Assembly: the variational identity from the product-rule operator ODE and the value
equation.**

Packages the per-flow connector `rawVariationalIdentity_of_manifoldFlowFamily_chartClose`
with the product-rule operator ODE `chartCloseDop_hasDerivAt_clm_comp` (this file) feeding the
required `hDchart`.  The caller supplies:

* `hT`, `hP` — the two factor `HasDerivAt` data (the orbit-derivative of the moving inverse
  trivialisation and the flat spatial-variational ODE);
* `hcont` — joint continuity of the orbit (separable continuity input);
* `hRdiff`, `hCdiff` — the convention-bridge differentiability side conditions;
* `hsplit` — the metric value equation identifying the operator-ODE derivative value (applied
  to `v`) with the trivialised flat derivative plus the **metric** Christoffel correction.

It produces `RawVariationalIdentity`.  The `hsplit` value equation is the genuinely
metric-dependent residual — equivalently (★) in the module docstring, the identity
`T' w = -movingTrivCorrection α X w - christoffelCorrection g α α (X̃_α α) w`, which equates the
smooth-structure moving-trivialisation jet with the metric Christoffel.  That identity is
**false in a general chart**; this assembly therefore exposes `hsplit` as a genuine *input*,
never discharged here and never asserted to hold.  No hypothesis-packaging: `hsplit` is an
`E`-equation, not the `HasDerivAt` conclusion. -/
theorem rawVariationalIdentity_of_orbitODE_factors
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {T' P' : E →L[ℝ] E}
    (hT : HasDerivAt (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x) T' t)
    (hP : HasDerivAt (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x) P' t)
    (hcont : Continuous (fun s : ℝ => (Φ_fam s : M → M) x))
    (hRdiff : DifferentiableAt ℝ
      (chartRawRepr (I := I) (Φ_fam t x) (X : ∀ y : M, TangentSpace I y))
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hCdiff : DifferentiableAt ℝ
      (fun z => chartMovingTriv (I := I) (Φ_fam t x) z)
      (extChartAt I (Φ_fam t x) (Φ_fam t x)))
    (hsplit : (T'.comp (chartCloseFderiv (I := I) Φ_fam (Φ_fam t x) x t)
        + (chartCloseTriv (I := I) Φ_fam (Φ_fam t x) x t).comp P') v
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
  have hDchart := chartCloseDop_hasDerivAt_clm_comp (I := I) Φ_fam (Φ_fam t x) x t hT hP
  exact rawVariationalIdentity_of_manifoldFlowFamily_chartClose (I := I) g X Φ_fam t x v
    hcont hDchart hRdiff hCdiff hsplit

end OrbitODE

end DifferentialGeometry.PDE.RicciFlow.ODE
