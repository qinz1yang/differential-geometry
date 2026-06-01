import DifferentialGeometry.PDE.RicciFlow.Pullback.CartanCancellation
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ManifoldIntegralFlow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Variational slot-derivative reduction for the moving-pushforward inner product

For a smooth Riemannian metric `g` on a smooth manifold `M`, a smooth tangent
vector field `X`, a time-indexed diffeomorphism family `Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)`
(the genuine integral flow of `X`), a fixed time `t`, base point `x` and tangent
pair `(v, w)`, the Hamilton–DeTurck pull-back identity needs the time derivative of
the **moving-pushforward inner product**

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`.

The derivative-level Cartan-cancellation primitive
`cartan_cancellation_derivative_witness` (in `Pullback/CartanCancellation.lean`)
*takes* the per-slot `HasDerivAt` witnesses (`h_A`, `h_B`), the per-slot value
identifications (`h_A_value`, `h_B_value`), the assembled total `HasDerivAt`
(`h_total`) and the additive identity (`h_sum`) as hypotheses, and packages the
Cartan-Lie algebra on top.

This file **produces** those per-slot hypotheses from a single, strictly weaker /
different input: the *raw vector-valued* variational derivative of the
pushforward path

  `s ↦ (mfderiv (Φ_fam s) x v : E)`,

at the level of the model fibre `E` (recall `TangentSpace I b = E` definitionally
for every base point `b`, so the slot-pushforward path is genuinely `E`-valued and
its derivative is an element of `E`). Given that vector derivative, the scalar
per-slot derivatives, the bilinear total derivative, and the value identities all
follow by elementary calculus on the *fixed* continuous (bi)linear form
`g.inner (Φ_fam t x)`:

* a fixed continuous-linear functional composed with a `HasDerivAt` path
  (`HasFDerivAt.comp_hasDerivAt`) gives each single-slot scalar derivative;
* the continuous-bilinear product rule
  (`ContinuousLinearMap.hasDerivWithinAt_of_bilinear`) gives the two-slot total;
* `map_neg` / `ContinuousLinearMap.neg_apply` convert the raw value
  `V' = -∇^g_{dΦv} X` into the negated-Killing-piece value identity.

## The single remaining gap

The only input not proved here is the **raw linearized-flow identity**

  `HasDerivAt (fun s => (mfderiv (Φ_fam s) x v : E))
      (-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)) t`,

packaged as the predicate `RawVariationalIdentity`. This is the genuine
variational ODE for the manifold flow: it states that the time derivative of the
pushforward of a fixed tangent vector along the flow equals the (negative)
covariant derivative of the generating field `X` along that pushforward. It
requires *smooth dependence of the manifold integral flow on its initial
condition* — data that Mathlib's integral-curve API does not currently provide
(it supplies only Lipschitz dependence on the initial condition). It is therefore
exposed here as a separable hypothesis, **not** proved in this file. No
`sorry`/`axiom` is used: the gap is a hypothesis on the inputs, and everything
downstream of it is genuine calculus.

No `HasLocallyConstantChartAt`-style hypothesis appears anywhere in this file.
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Slot-1 scalar derivative from the raw vector derivative.**

Given the raw vector-valued derivative `hu` of the slot-1 pushforward path
`s ↦ (mfderiv (Φ_fam s) x v : E)` at `t`, the slot-1 inner-product variation
curve (slot-2 frozen at `t`) has scalar derivative
`g.inner (Φ_fam t x) V' (mfderiv (Φ_fam t) x w)`.

The proof composes the fixed continuous-linear functional
`(g.inner (Φ_fam t x)).flip (mfderiv (Φ_fam t) x w)` with `hu`. -/
theorem variational_flow_inner_slot1_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (V' : E)
    (hu : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) V' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w))
      (g.inner (Φ_fam t x) V' (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  set y := Φ_fam t x
  set c : E := mfderiv I I (Φ_fam t : M → M) x w with hc
  set L : E →L[ℝ] ℝ := (g.inner y).flip c with hL
  have hcomp : HasDerivAt (fun s => L (mfderiv I I (Φ_fam s : M → M) x v : E)) (L V') t :=
    L.hasFDerivAt.comp_hasDerivAt t hu
  have hfun : (fun s => L (mfderiv I I (Φ_fam s : M → M) x v : E))
      = (fun s => g.inner y (mfderiv I I (Φ_fam s : M → M) x v) c) := by
    funext s; rw [hL]; rfl
  rw [hfun] at hcomp
  have hval : L V' = g.inner y V' c := by rw [hL]; rfl
  rw [hval] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Slot-2 scalar derivative from the raw vector derivative.**

Given the raw vector-valued derivative `hw` of the slot-2 pushforward path
`s ↦ (mfderiv (Φ_fam s) x w : E)` at `t`, the slot-2 inner-product variation
curve (slot-1 frozen at `t`) has scalar derivative
`g.inner (Φ_fam t x) (mfderiv (Φ_fam t) x v) W'`.

The proof composes the fixed continuous-linear functional
`g.inner (Φ_fam t x) (mfderiv (Φ_fam t) x v)` with `hw`. -/
theorem variational_flow_inner_slot2_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (W' : E)
    (hw : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x w : E)) W' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (g.inner (Φ_fam t x) (mfderiv I I (Φ_fam t : M → M) x v) W') t := by
  set y := Φ_fam t x
  set c : E := mfderiv I I (Φ_fam t : M → M) x v with hc
  set L : E →L[ℝ] ℝ := g.inner y c with hL
  have hcomp : HasDerivAt (fun s => L (mfderiv I I (Φ_fam s : M → M) x w : E)) (L W') t :=
    L.hasFDerivAt.comp_hasDerivAt t hw
  have hfun : (fun s => L (mfderiv I I (Φ_fam s : M → M) x w : E))
      = (fun s => g.inner y c (mfderiv I I (Φ_fam s : M → M) x w)) := rfl
  rw [hfun] at hcomp
  exact hcomp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
/-- **Total two-slot derivative from the raw vector derivatives.**

Given both raw vector-valued derivatives `hu` (slot-`v`) and `hw` (slot-`w`),
the combined two-slot inner-product variation curve has scalar derivative

  `g.inner (Φ_fam t x) V' (mfderiv (Φ_fam t) x w)
    + g.inner (Φ_fam t x) (mfderiv (Φ_fam t) x v) W'`,

the bilinear product rule on `g.inner (Φ_fam t x)`. -/
theorem variational_flow_inner_total_derivative
    (g : SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x) (V' W' : E)
    (hu : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) V' t)
    (hw : HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x w : E)) W' t) :
    HasDerivAt
      (fun s => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (g.inner (Φ_fam t x) V' (mfderiv I I (Φ_fam t : M → M) x w)
        + g.inner (Φ_fam t x) (mfderiv I I (Φ_fam t : M → M) x v) W') t := by
  set y := Φ_fam t x
  set B : E →L[ℝ] E →L[ℝ] ℝ := g.inner y with hB
  set u : ℝ → E := fun s => (mfderiv I I (Φ_fam s : M → M) x v : E) with hudef
  set ww : ℝ → E := fun s => (mfderiv I I (Φ_fam s : M → M) x w : E) with hwdef
  have hprod := ContinuousLinearMap.hasDerivWithinAt_of_bilinear (B := B)
    (u := u) (v := ww) (s := Set.univ) (x := t)
    hu.hasDerivWithinAt hw.hasDerivWithinAt
  rw [hasDerivWithinAt_univ] at hprod
  rw [add_comm]
  exact hprod

/-- **Raw linearized-flow variational identity for one pushforward slot.**

For the genuine integral flow `Φ_fam` of `X`, the pushforward of a fixed tangent
vector `v` along the flow,

  `s ↦ (mfderiv (Φ_fam s) x v : E)`,

has at time `t` the *vector-valued* derivative

  `-(LeviCivita g) X (Φ_fam t x) (mfderiv (Φ_fam t) x v)`,

i.e. the negative covariant derivative of `X` along the slot pushforward (the
sign coming from the generator `-X`). This is the variational ODE for the
manifold flow; it is taken as an input (the documented gap). -/
def RawVariationalIdentity
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x) : Prop :=
  HasDerivAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
    (-(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) (Φ_fam t x)
      (mfderiv I I (Φ_fam t : M → M) x v)) t

/-- **Variational reduction feeding the Cartan-cancellation witness.**

Given the two raw linearized-flow variational identities `hv_raw` (slot-`v`) and
`hw_raw` (slot-`w`), the moving-pushforward inner-product variation curve

  `s ↦ g.inner (Φ_fam t x) (mfderiv (Φ_fam s) x v) (mfderiv (Φ_fam s) x w)`

has at `t` the derivative

  `-lieDerivMetric g X (Φ_fam t x) (mfderiv (Φ_fam t) x v) (mfderiv (Φ_fam t) x w)`.

This is the exact conclusion of `cartan_cancellation_derivative_witness`; the
present wrapper produces all six hypotheses that primitive takes (`h_A`, `h_B`,
`h_A_value`, `h_B_value`, `h_total`, `h_sum`) from the two raw identities, then
applies it. The only input not produced here is the raw variational ODE itself
(`RawVariationalIdentity`), the documented gap. -/
theorem variational_flow_feeds_cartan_witness
    (g : SmoothRiemannianMetric I M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (hv_raw : RawVariationalIdentity (I := I) g X Φ_fam t x v)
    (hw_raw : RawVariationalIdentity (I := I) g X Φ_fam t x w) :
    HasDerivAt
      (fun s : ℝ => g.inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (-lieDerivMetric (I := I) g X (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v)
        (mfderiv I I (Φ_fam t : M → M) x w)) t := by
  set y := Φ_fam t x with hy
  set dΦv : E := mfderiv I I (Φ_fam t : M → M) x v with hdΦv
  set dΦw : E := mfderiv I I (Φ_fam t : M → M) x w with hdΦw
  set Vraw : E := -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) y dΦv with hVraw
  set Wraw : E := -(LeviCivita (I := I) g) (X : ∀ x : M, TangentSpace I x) y dΦw with hWraw
  have h_A := variational_flow_inner_slot1_derivative (I := I) g Φ_fam t x v w Vraw hv_raw
  have h_B := variational_flow_inner_slot2_derivative (I := I) g Φ_fam t x v w Wraw hw_raw
  have h_total := variational_flow_inner_total_derivative (I := I) g Φ_fam t x v w
    Vraw Wraw hv_raw hw_raw
  have h_A_value : g.inner y Vraw dΦw
      = -g.inner y ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y dΦv) dΦw := by
    rw [hVraw, map_neg, ContinuousLinearMap.neg_apply]
  have h_B_value : g.inner y dΦv Wraw
      = -g.inner y dΦv ((LeviCivita (I := I) g)
          (X : ∀ x : M, TangentSpace I x) y dΦw) := by
    rw [hWraw, map_neg]
  exact cartan_cancellation_derivative_witness (I := I) g X Φ_fam t x v w
    (g.inner y Vraw dΦw + g.inner y dΦv Wraw)
    (g.inner y Vraw dΦw) (g.inner y dΦv Wraw)
    h_A h_B h_A_value h_B_value h_total rfl

end ODE
end RicciFlow
end PDE
end DifferentialGeometry
