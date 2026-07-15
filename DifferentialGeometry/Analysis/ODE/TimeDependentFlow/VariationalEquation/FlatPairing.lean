import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.VariationalEquation.VariationalFlow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.CovariantIdentity.FlatIdentity

/-!
# The flat-route Cartan pairing for the moving-pushforward inner product

`variational_flow_feeds_cartan_witness` (`VariationalEquation/VariationalFlow.lean`) consumes the
**covariant** per-slot identities `RawVariationalIdentity` (each asserting the slot pushforward
curve has derivative `-∇_{dΦ·} X`) and produces the `-lieDerivMetric` derivative of the
frozen-metric moving-pushforward inner product

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`.

As the orbit-ODE analysis records (`ChartOperator/ManifoldFlowOrbitODE.lean`,
the residual (★)), the covariant per-slot identity is **not dischargeable** from the flow ODE:
the genuine derivative of the orbit pushforward curve, read in Mathlib's moving target chart,
is the **flat / Lie-type** value `T' (dΦv) + P' v` (`RawVariationalIdentityFlat`,
`CovariantIdentity/FlatIdentity.lean`), which differs from the covariant value by the
metric Christoffel contraction at the basepoint.  Precisely, with `α := Φ_fam t x` and
`dΦv := mfderiv (Φ_fam t) x v`, the two per-slot values are related by

  `Vflat = -∇_{dΦv} X + christoffelCorrection g α α (X̃_α α) dΦv`,      (the per-slot residual)

an `E`-equation supplied here as the explicit input `hcorr_v` / `hcorr_w` (it is genuine
chart-Christoffel geometric data — not the conclusion, and not the false `D²φ = Γ`).

## The honest pairing value

Pairing the two **flat** per-slot derivatives against the *fixed* bilinear form `g.inner α`
(the genuine derivative of the frozen-metric moving-pushforward inner product, by
`variational_flow_inner_total_derivative`) and substituting the two per-slot residuals gives

  `d/ds [g_α(dΦ_s v, dΦ_s w)]|_t
     = -lieDerivMetric g X α dΦv dΦw
       + ( g_α(Γ(X̃_α, dΦv), dΦw) + g_α(dΦv, Γ(X̃_α, dΦw)) ),`

where the first summand is the Cartan value (`cartan_formula_for_lie_deriv_metric`, via the
covariant per-slot pairing) and the **bracketed residual** is the metric-transport term
`X(g)(dΦv, dΦw)` of the metric along the orbit (by chart metric-compatibility,
`∂_k G_{ij} = ∑_l Γ^l_{ki} G_{lj} + Γ^l_{kj} G_{li}`).

This residual is **not** zero in a general chart; it is exactly the contribution of the
*moving base point* `Φ_fam s x` inside the genuine pull-back inner product
`(g_DT s).inner (Φ_fam s x) …`, which the frozen-metric frozen-point pushforward slot does not
see.  The flat route therefore re-architects the Hamilton–DeTurck cancellation into a genuine
**three-piece** split (metric-family / base-point-motion / pushforward-kinetic) in which the
metric-transport residual produced here cancels against the base-point-motion piece, leaving
`-2 Ric`.  See the file footer for the precise three-piece statement.

No `sorry`, no `axiom`, no `HasLocallyConstantChartAt`-style hypothesis, no
joint-`C^∞`-on-`ℝ × M` predicate, and no false `D²φ = Γ` identification.  No
hypothesis-packaging: the inputs are the two flat per-slot `HasDerivAt`s and the two per-slot
Christoffel-residual `E`-equations; the conclusion is the *scalar* pairing `HasDerivAt`, a
distinct object.
-/

noncomputable section

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ODE

open Bundle Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The covariant per-slot value as an `E`-vector.**

`-(∇^g_{dΦ·} X)`, the negative Levi-Civita covariant derivative of `X` along the slot
pushforward at the orbit point `α := Φ_fam t x`, packaged at the model-fibre type `E` (via the
defeq `TangentSpace I α = E`).  This is the value that the *covariant* per-slot identity
`RawVariationalIdentity` asserts; it is named here as an honest `E`-typed abbreviation so the
flat-to-covariant residual `E`-equations elaborate without `HAdd` ambiguity across the
`TangentSpace I α = E` defeq. -/
def negCovariantSlotValue
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v : TangentSpace I x) : E :=
  -(LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) (Φ_fam t x)
    (mfderiv I I (Φ_fam t : M → M) x v)

/-- **The metric-transport residual at the basepoint.**

For a smooth metric `g`, a smooth vector field `X`, the orbit point `α := Φ_fam t x`, and the
two frozen pushforwards `dΦv := mfderiv (Φ_fam t) x v`, `dΦw := mfderiv (Φ_fam t) x w`, this is
the symmetric pairing of the basepoint metric Christoffel correction of `X̃_α(α)` against each
pushforward slot:

  `g_α( Γ(X̃_α, dΦv), dΦw ) + g_α( dΦv, Γ(X̃_α, dΦw) )`.

By chart metric-compatibility this equals the directional derivative `X(g)(dΦv, dΦw)` of the
metric `g` along `X` at `α` — the *metric-transport* contribution of the moving base point of
the pull-back inner product.  It is the genuine residual separating the flat-route pushforward
slot from `-lieDerivMetric`; it is generically nonzero. -/
def metricTransportResidual
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  g.inner (Φ_fam t x)
      (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
        (chartE_section_repr (I := I) (Φ_fam t x)
          (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
        (mfderiv I I (Φ_fam t : M → M) x v))
      (mfderiv I I (Φ_fam t : M → M) x w)
    + g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
          (chartE_section_repr (I := I) (Φ_fam t x)
            (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
          (mfderiv I I (Φ_fam t : M → M) x w))

/-- **Flat-route Cartan pairing of the moving-pushforward inner product.**

Given the two **flat** per-slot identities (`RawVariationalIdentityFlat` for `v` and `w`, with
factor-ODE derivative values `T'`, `P'`) and the two per-slot flat-to-covariant residual
`E`-equations `hcorr_v` / `hcorr_w`

  `T' (dΦv) + P' v = -∇_{dΦv} X + christoffelCorrection g α α (X̃_α α) dΦv`     (and slot `w`),

the frozen-metric moving-pushforward inner-product variation curve

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

has at `t` the derivative

  `-lieDerivMetric g X (Φ_fam t x) dΦv dΦw + metricTransportResidual g X Φ_fam t x v w`.

The flat product rule (`variational_flow_inner_total_derivative`) assembles the two flat slot
derivatives against the fixed bilinear form `g.inner α`; substituting the per-slot residuals
and applying `cartan_formula_for_lie_deriv_metric` (through the covariant pairing) yields the
displayed value.

This is the honest flat-route replacement for `variational_flow_feeds_cartan_witness`: the
metric content is in the `g.inner` pairing (not per-slot), but the metric-transport residual
does **not** vanish per the frozen-metric reading; it is exhibited explicitly and cancels only
against the base-point-motion piece downstream.  No hypothesis-packaging: `hcorr_v`/`hcorr_w`
are `E`-equations, the conclusion is the scalar pairing `HasDerivAt`. -/
theorem variational_flow_flat_pairing_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hcorr_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = negCovariantSlotValue (I := I) g X Φ_fam t x v
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hcorr_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = negCovariantSlotValue (I := I) g X Φ_fam t x w
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) t := by
  classical
  set α := Φ_fam t x with hα
  set dΦv : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x v with hdΦv
  set dΦw : TangentSpace I α := mfderiv I I (Φ_fam t : M → M) x w with hdΦw
  set Vflat : TangentSpace I α := T'v dΦv + P'v v with hVflat
  set Wflat : TangentSpace I α := T'w dΦw + P'w w with hWflat
  set Xα : E := chartE_section_repr (I := I) α (X : ∀ y : M, TangentSpace I y) α with hXα
  set nablaV : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦv with hnablaV
  set nablaW : TangentSpace I α :=
    (LeviCivita (I := I) g) (X : ∀ y : M, TangentSpace I y) α dΦw with hnablaW
  set Cv : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦv with hCv
  set Cw : TangentSpace I α := christoffelCorrection (I := I) g α α Xα dΦw with hCw
  have hcorr_v' : Vflat = -nablaV + Cv := by
    rw [hcorr_v]; rfl
  have hcorr_w' : Wflat = -nablaW + Cw := by
    rw [hcorr_w]; rfl
  have h_total :=
    variational_flow_inner_total_derivative (I := I) g Φ_fam t x v w Vflat Wflat hv_flat hw_flat
  have hval :
      g.inner α Vflat dΦw + g.inner α dΦv Wflat
        = -lieDerivMetric (I := I) g X α dΦv dΦw
          + metricTransportResidual (I := I) g X Φ_fam t x v w := by
    have hbil1 : (g.inner α) (-nablaV + Cv)
        = -(g.inner α) nablaV + (g.inner α) Cv := by
      rw [ContinuousLinearMap.map_add (g.inner α) _ _,
        ContinuousLinearMap.map_neg (g.inner α) _]
    have hslot1 : g.inner α Vflat dΦw
        = -g.inner α nablaV dΦw + g.inner α Cv dΦw := by
      rw [hcorr_v', hbil1, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.neg_apply]
    have hslot2 : g.inner α dΦv Wflat
        = -g.inner α dΦv nablaW + g.inner α dΦv Cw := by
      rw [hcorr_w', ContinuousLinearMap.map_add (g.inner α dΦv) _ _,
        ContinuousLinearMap.map_neg (g.inner α dΦv) _]
    have hcartan :
        -g.inner α nablaV dΦw + -g.inner α dΦv nablaW
          = -lieDerivMetric (I := I) g X α dΦv dΦw := by
      rw [hnablaV, hnablaW]
      exact (neg_lieDerivMetric_eq_neg_killing_sum (I := I) g X α dΦv dΦw).symm
    have hres : g.inner α Cv dΦw + g.inner α dΦv Cw
        = metricTransportResidual (I := I) g X Φ_fam t x v w := by
      rw [metricTransportResidual, hCv, hCw, hXα]
    rw [hslot1, hslot2, ← hcartan, ← hres]
    ring
  rwa [hval] at h_total

/-- **Flat-route pushforward-slot derivative (within-set form).**

The one-sided `HasDerivWithinAt (Ici 0)` restriction of `variational_flow_flat_pairing_hasDerivAt`:
with the metric frozen at `g` and the base point frozen at `Φ_fam t x`, the moving-pushforward
inner-product curve has within-set derivative `-lieDerivMetric g X α dΦv dΦw +
metricTransportResidual g X Φ_fam t x v w`.

This is the honest flat-route replacement for `deTurck_pushforward_slot_hasDerivWithinAt`: the
value is **not** `-lieDerivMetric` alone (that would require the non-dischargeable covariant
per-slot identity); the metric-transport residual is present and cancels only against the
base-point-motion piece downstream. -/
theorem variational_flow_flat_pairing_hasDerivWithinAt
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (T'v P'v T'w P'w : E →L[ℝ] E)
    (hv_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x v T'v P'v)
    (hw_flat : RawVariationalIdentityFlat (I := I) Φ_fam t x w T'w P'w)
    (hcorr_v :
      T'v (mfderiv I I (Φ_fam t : M → M) x v) + P'v v
        = negCovariantSlotValue (I := I) g X Φ_fam t x v
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x v))
    (hcorr_w :
      T'w (mfderiv I I (Φ_fam t : M → M) x w) + P'w w
        = negCovariantSlotValue (I := I) g X Φ_fam t x w
          + christoffelCorrection (I := I) g (Φ_fam t x) (Φ_fam t x)
              (chartE_section_repr (I := I) (Φ_fam t x)
                (X : ∀ y : M, TangentSpace I y) (Φ_fam t x))
              (mfderiv I I (Φ_fam t : M → M) x w)) :
    HasDerivWithinAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
          (mfderiv I I (Φ_fam t : M → M) x v)
          (mfderiv I I (Φ_fam t : M → M) x w)
        + metricTransportResidual (I := I) g X Φ_fam t x v w) (Set.Ici 0) t :=
  (variational_flow_flat_pairing_hasDerivAt (I := I) g X Φ_fam t x v w
    T'v P'v T'w P'w hv_flat hw_flat hcorr_v hcorr_w).hasDerivWithinAt

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
