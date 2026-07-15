# ApproximateIsometry.lean — ARCHIVED (never-green broken route, 2026-06-11)

This is the full original `ApproximateIsometry.lean` (5769 lines), preserved as a
**future reference only**.  The file was **never green** against this tree (~101+
errors): the never-ported `normRS` tensor family (`normRS`,
`normRS_eq_sqrt_normSqRS`, `sqrt_normRS_upper/lower_le_of_equiv`,
`normSqRS_le_of_metric_equiv`, `fieldNormRS`, `abs_quad02_le_norm`,
`connActConst`/`connActComp`), the `LeviCivita.leviCivitaConnectionOfMetric`
namespace (renamed to `Integral.Connection.leviCivitaConnectionOfMetric`), plus
`whnf` timeouts and cascades.

## What was salvaged (do NOT re-extract from here)

- **① book data structures + ② same-domain predicates + ③ bound-predicates &
  dimension constants** → `ApproxIsometryDefs.lean` (green; the `LeviCivita`
  rename and `fieldNormRS → √normSqRS` revivals applied there).
- **Keystone `exists_trivFrame_orthonormal_basis`** (smooth gRef-ON-at-a-point
  trivialization frame) → `RicBoundGoodFrame.lean` (green).
- The norm-comparison content (F1) and the `(0,s)` metric-equivalence factor are
  superseded by `Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv` (Comparison.lean)
  and `lemma45_cor_II_of_intrinsic` (Lemma45Covariant.lean).

## Still here (broken; revive only if a future need is concrete)

The F1 norm-comparison proofs (`normSqRS_compare_of_approxIsometry`,
`bookNormRS_compare`, `sqrt_normRS_upper`, …) and the entire F3 connection-
difference proof apparatus (`connDiff_*`, `lcDiff*`, `metricCov*`, `connDiffOne*`
/`connDiffTwo*`, `connDiffEpsBound_*`, `nablaRS_*`, `hcg_first_order_nabla_norm_estimate`).
Most are superseded by the green `Lemma45Engine` / `RicBoundClaims` machinery; the
unique surviving value was the interface (now in `ApproxIsometryDefs.lean`).

---

```lean
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Coordinates.ChristoffelTensor
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis
import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation
import Mathlib.LinearAlgebra.QuadraticForm.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Approximate Isometries On A Fixed Domain

This file records the supplied-metric version of the MSM135 approximate
isometry hypotheses used by the HCG compactness construction.  The construction
provides the pullback metric as data, so the predicate compares two metrics on
the same domain rather than constructing a pullback metric.

It also records a book-facing map-level interface for MSM135 Definition 4.1.
That interface is deliberately separate from the same-domain comparison
predicate below: for a general smooth map `Phi`, the pullback of a metric is a
smooth `(0,2)` tensor field, not a Riemannian metric a priori.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedDomain

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I âˆž M] [SigmaCompactSpace M]

section MapLevel

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I âˆž N] [SigmaCompactSpace N]
variable [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
variable [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) N]

/-- Concrete pullback metric tensor data for a smooth map.

For a general smooth map this is not packaged as a Riemannian metric: it is the
actual covariant `(0,2)` tensor whose value is
`h_{Phi x}(d Phi_x -, d Phi_x -)`.  The smooth tensor field is supplied as data,
and the formula field pins it to the map. -/
structure PullbackMetricTensorData
    (Phi : M -> N) (h : SmoothRiemannianMetric I N) where
  pullback :
    Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) 2
  pullback_apply :
    forall x : M, forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))

/-- The pointwise norm of the metric-error tensor `A - g`, measured by `g`. -/
noncomputable def metricTensorErrorNorm
    (A :
      Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) 2)
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) g x 2
      (A x - Tensor0SBundle.metricTensorField (I := I) g x))

/-- Generic iterated covariant derivatives of a smooth `(0,2)` tensor field,
using the Levi-Civita connection of the reference metric.  This is the
tensor-field version of `metricCovDeriv`; it is needed because `Phi^* h` is not
necessarily a Riemannian metric for a general smooth map. -/
noncomputable def tensor02CovDeriv
    (A :
      Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) (a + 2))
    A
    (fun a Aprev =>
      metricCovDerivStep (I := I) gRef a Aprev)

/-- Pointwise norm `|nabla_cov^a A|_norm` for a smooth `(0,2)` tensor field. -/
noncomputable def tensor02CovDerivNormWith
    (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (ð•œ := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (âˆž : WithTop â„•âˆž)) 2)
    (cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (tensor02CovDeriv (I := I) A cov a x))

/-- MSM135 Definition 4.1, localized to a set `K`: data for an `(eps,p)`
pre-approximate isometry is a smooth map whose actual pullback metric tensor is
`C^p`-close to the source metric. -/
structure PreApproxIsometryData
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smooth : ContMDiff I I (âˆž : WithTop â„•âˆž) Phi
  pullbackData : PullbackMetricTensorData (I := I) Phi h
  c0_small :
    forall x : M, x âˆˆ K ->
      metricTensorErrorNorm (I := I) pullbackData.pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x âˆˆ K ->
        tensor02CovDerivNormWith (I := I) a pullbackData.pullback g g x <= eps

/-- MSM135 Definition 4.1, localized two-sided data for diffeomorphisms.

The forward field is the pre-approximate isometry on the source set.  The
reverse field is the same condition for the inverse map on the target set. -/
structure BookApproxIsometryData
    (K : Set M) (L : Set N) (eps : Real) (p : Nat)
    (Phi : M â‰ƒâ‚˜âŸ®I, IâŸ¯ N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  forward : PreApproxIsometryData (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsometryData (I := I) L eps p (Phi.symm : N -> M) h g

/-- The metric tensor evaluates to the Riemannian quadratic form. -/
private theorem quad02_metricTensorField
    (g : SmoothRiemannianMetric I M) {x : M} (v : TangentSpace I x) :
    quad02 (I := I) (M := M)
      (Tensor0SBundle.metricTensorField (I := I) g x) v =
      g.inner x v v := by
  simp [quad02, Tensor0SBundle.metricTensorField_apply]

/-- A small `(0,2)` metric-error tensor gives a small quadratic error. -/
theorem preApprox_quad_error_abs_le
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : PreApproxIsometryData (I := I) K eps p Phi g h)
    {x : M} (hx : x âˆˆ K) (v : TangentSpace I x) :
    |quad02 (I := I) (M := M)
        (H.pullbackData.pullback x -
          Tensor0SBundle.metricTensorField (I := I) g x) v| <=
      eps * g.inner x v v := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := âˆž)
      (by simp)
  have hcs :=
    abs_quad02_le_norm (I := I) (M := M) g
      (H.pullbackData.pullback x -
        Tensor0SBundle.metricTensorField (I := I) g x) v
  have hsmall :
      metricTensorErrorNorm (I := I) H.pullbackData.pullback g x <= eps :=
    H.c0_small x hx
  have hquad_nonneg : 0 <= g.inner x v v := by
    by_cases hv : v = 0
    Â· subst v
      simp
    Â· exact le_of_lt (g.pos x v hv)
  calc
    |quad02 (I := I) (M := M)
        (H.pullbackData.pullback x -
          Tensor0SBundle.metricTensorField (I := I) g x) v|
        <= Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) g x 2
              (H.pullbackData.pullback x -
                Tensor0SBundle.metricTensorField (I := I) g x)) *
            g.inner x v v := hcs
    _ <= eps * g.inner x v v :=
        mul_le_mul_of_nonneg_right
          (by simpa [metricTensorErrorNorm] using hsmall) hquad_nonneg

/-- MSM135 Proposition 4.2, pre-approximate direction: the `C^0` tensor error
bound implies the upper quadratic-form bound for the actual pullback tensor. -/
theorem preApprox_quad_upper
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : PreApproxIsometryData (I := I) K eps p Phi g h)
    {x : M} (hx : x âˆˆ K) (v : TangentSpace I x) :
    quad02 (I := I) (M := M) (H.pullbackData.pullback x) v <=
      (1 + eps) * g.inner x v v := by
  let A := H.pullbackData.pullback x
  let G := Tensor0SBundle.metricTensorField (I := I) g x
  have herr :
      |quad02 (I := I) (M := M) (A - G) v| <=
        eps * g.inner x v v :=
    preApprox_quad_error_abs_le (I := I) H hx v
  have herr_upper :
      quad02 (I := I) (M := M) (A - G) v <=
        eps * g.inner x v v :=
    le_trans (le_abs_self _) herr
  have hmetric :
      quad02 (I := I) (M := M) G v = g.inner x v v :=
    quad02_metricTensorField (I := I) g v
  have hdiff :
      quad02 (I := I) (M := M) (A - G) v =
        quad02 (I := I) (M := M) A v - g.inner x v v := by
    simp [quad02, G, ContinuousMultilinearMap.sub_apply]
  have hsum :
      quad02 (I := I) (M := M) A v =
        quad02 (I := I) (M := M) (A - G) v + g.inner x v v := by
    linarith
  calc
    quad02 (I := I) (M := M) A v
        = quad02 (I := I) (M := M) (A - G) v + g.inner x v v := hsum
    _ <= eps * g.inner x v v + g.inner x v v :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right herr_upper (g.inner x v v)
    _ = (1 + eps) * g.inner x v v := by ring

private theorem mfderiv_symm_apply_mfderiv
    (Phi : M â‰ƒâ‚˜âŸ®I, IâŸ¯ N) (x : M) (v : TangentSpace I x) :
    mfderiv I I (Phi.symm : N -> M) (Phi x)
        (mfderiv I I (Phi : M -> N) x v) = v := by
  have hsymm_diff : MDifferentiableAt I I (Phi.symm : N -> M) (Phi x) :=
    Phi.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hPhi_diff : MDifferentiableAt I I (Phi : M -> N) x :=
    Phi.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (I := I) (I' := I) (I'' := I)
      (g := (Phi.symm : N -> M)) (f := (Phi : M -> N))
      (x := x) hsymm_diff hPhi_diff v
  have hid :
      (fun y : M => Phi.symm (Phi y)) = fun y : M => y := by
    funext y
    exact Diffeomorph.symm_apply_apply Phi y
  have hleft :
      mfderiv I I (fun y : M => Phi.symm (Phi y)) x v = v := by
    rw [hid]
    change (mfderiv I I (@id M) x) v = v
    rw [mfderiv_id]
    rfl
  have hcomp' :
      mfderiv I I (fun y : M => Phi.symm (Phi y)) x v =
        mfderiv I I (Phi.symm : N -> M) (Phi x)
          (mfderiv I I (Phi : M -> N) x v) := by
    simpa [Function.comp_def] using hcomp
  exact hcomp'.symm.trans hleft

/-- MSM135 Proposition 4.2, two-sided approximate-isometry form.  The first
inequality comes from the forward pre-approximate condition, and the second
from the inverse pre-approximate condition evaluated at `Phi x`. -/
theorem bookApprox_quad_twoSided
    {K : Set M} {L : Set N} {eps : Real} {p : Nat}
    {Phi : M â‰ƒâ‚˜âŸ®I, IâŸ¯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps p Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    {x : M} (hx : x âˆˆ K) (v : TangentSpace I x) :
    (1 + eps)â»Â¹ *
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v <=
      g.inner x v v âˆ§
    g.inner x v v <=
      (1 + eps) *
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
  have hCpos : 0 < 1 + eps := by linarith [H.forward.eps_pos]
  have hforward :=
    preApprox_quad_upper (I := I) H.forward hx v
  have hleft :
      (1 + eps)â»Â¹ *
          quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v <=
        g.inner x v v := by
    rwa [inv_mul_le_iffâ‚€ hCpos]
  let w : TangentSpace I (Phi x) :=
    mfderiv I I (Phi : M -> N) x v
  have hrev :=
    preApprox_quad_upper (I := I) H.reverse (hMapsTo hx) w
  have hrev_eval :
      quad02 (I := I) (M := N) (H.reverse.pullbackData.pullback (Phi x)) w =
        g.inner x v v := by
    have happly :=
      H.reverse.pullbackData.pullback_apply (Phi x)
        (fun _ : Fin 2 => w)
    have hmw :
        mfderiv I I (Phi.symm : N -> M) (Phi x) w = v := by
      simpa [w] using mfderiv_symm_apply_mfderiv (I := I) Phi x v
    have hpoint : Phi.symm (Phi x) = x :=
      Diffeomorph.symm_apply_apply Phi x
    rw [hpoint] at hmw happly
    rw [hmw] at happly
    simpa [quad02] using happly
  have hforward_eval :
      h.inner (Phi x) w w =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
    have happly :=
      H.forward.pullbackData.pullback_apply x (fun _ : Fin 2 => v)
    simpa [quad02, w] using happly.symm
  have hright :
      g.inner x v v <=
        (1 + eps) *
          quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v := by
    simpa [hrev_eval, hforward_eval] using hrev
  exact âŸ¨hleft, hrightâŸ©

/-- Same-domain packaging of MSM135 Proposition 4.2 when the pullback tensor is
already supplied as a Riemannian metric `gh` on the source.  This adapter does
not construct a pullback metric; it only transfers the checked quadratic-form
estimate to the existing `MetricUniformEquivalentOn` API. -/
theorem bookApprox_uniformEquiv_of_pullback
    {K : Set M} {L : Set N} {eps : Real} {p : Nat}
    {Phi : M â‰ƒâ‚˜âŸ®I, IâŸ¯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps p Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    (gh : SmoothRiemannianMetric I M)
    (hgh : forall x : M, x âˆˆ K -> forall v : TangentSpace I x,
      gh.inner x v v =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v) :
    MetricUniformEquivalentOn (I := I) K g gh (1 + eps) := by
  have hCpos : 0 < 1 + eps := by linarith [H.forward.eps_pos]
  refine âŸ¨?_, ?_âŸ©
  Â· linarith [H.forward.eps_pos]
  Â· intro x hx v
    have htwo :=
      bookApprox_quad_twoSided (I := I) H hMapsTo hx v
    have hupper_raw :=
      preApprox_quad_upper (I := I) H.forward hx v
    constructor
    Â· rw [inv_mul_le_iffâ‚€ hCpos]
      simpa [hgh x hx v] using htwo.2
    Â· simpa [hgh x hx v] using hupper_raw

end MapLevel

/-- Supplied-metric `(eps,p)` comparison data on a set `K`.

The `C^0` part is the uniform metric equivalence with constant `1 + eps`.
Higher-order smallness is stated using the fixed-background covariant derivative
norms from `AllTimesBounds`; order `0` is intentionally represented by the
metric-equivalence field.

This is a same-domain comparison predicate for a supplied pullback metric.  It
is not MSM135 Definition 4.1; it is the consumer-side form obtained after the
map-level pullback metric has already been constructed and its `C^0` tensor
error has been converted into vector metric equivalence.  Higher-order F3
estimates use `IsTwoSidedApproxIsometryOn`, which also records the inverse-side
derivative smallness. -/
structure IsApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  uniform_equiv : MetricUniformEquivalentOn (I := I) K g h (1 + eps)
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x âˆˆ K ->
        metricCovDerivNorm (I := I) a h g x <= eps

/-- Same-domain version of the two-sided approximate-isometry hypotheses in
MSM135 Chapter 4.

`IsApproxIsometryOn` is the forward, supplied-pullback side.  The extra field
records the inverse-side derivative smallness, equivalently the bounds on
`nabla_h^a g` needed in the higher connection-difference estimate. -/
structure IsTwoSidedApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  forward : IsApproxIsometryOn (I := I) K eps p g h
  reverse_cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x âˆˆ K ->
        metricCovDerivNorm (I := I) a g h x <= eps

theorem IsTwoSidedApproxIsometryOn.toApprox
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h) :
    IsApproxIsometryOn (I := I) K eps p g h :=
  Happrox.forward

/-- Pointwise norm `|nabla_cov^a h|_norm`, separating the connection metric
from the metric used to measure the resulting tensor. -/
noncomputable def metricCovDerivNormWith
    (a : Nat) (h cov norm : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSq0S (I := I) norm x (a + 2)
      (metricCovDeriv (I := I) h cov a x))

/-- In an orthonormal basis for the norm metric, a component of
`nabla_cov^a h` is bounded by `metricCovDerivNormWith`. -/
theorem metricCovComp_le
    (a : Nat) (h cov norm : SmoothRiemannianMetric I M) {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) norm x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (slots : Fin (a + 2) -> Idx) :
    |Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) h cov a x) slots| <=
      metricCovDerivNormWith (I := I) a h cov norm x := by
  simpa [metricCovDerivNormWith] using
    Tensor0SBundle.abs_component0S_le_sqrt_normSq0S
      (I := I) norm x (a + 2) basis hinv
      (metricCovDeriv (I := I) h cov a x) slots

/-- Compatibility with the older fixed-background notation:
`metricCovDerivNorm a h gRef = |nabla_gRef^a h|_gRef`. -/
theorem metricCovDerivNorm_eq_with
    (a : Nat) (h gRef : SmoothRiemannianMetric I M) (x : M) :
    metricCovDerivNorm (I := I) a h gRef x =
      metricCovDerivNormWith (I := I) a h gRef gRef x := rfl

/-- Under metric equivalence, the norm metric in `|nabla_cov^a h|` may be
changed at the expected tensor-norm cost. -/
theorem metricCovDerivNormWith_le_of_equiv
    {K : Set M} {C : Real}
    {h cov norm norm' : SmoothRiemannianMetric I M}
    (hEq : MetricUniformEquivalentOn (I := I) K norm norm' C)
    {x : M} (hx : x âˆˆ K) (a : Nat) :
    metricCovDerivNormWith (I := I) a h cov norm' x <=
      Real.sqrt (C ^ (a + 2)) *
        metricCovDerivNormWith (I := I) a h cov norm x := by
  let A := metricCovDeriv (I := I) h cov a x
  have hA_sq :
      Tensor0SBundle.normSq0S (I := I) norm' x (a + 2) A <=
        C ^ (a + 2) *
          Tensor0SBundle.normSq0S (I := I) norm x (a + 2) A :=
    Tensor0SBundle.normSq0S_upper_le_of_equiv
      (I := I) norm norm' x (a + 2) hEq.1 (hEq.2 x hx) A
  have hC_nonneg : 0 <= C := le_trans (by norm_num : (0 : Real) <= 1) hEq.1
  calc
    metricCovDerivNormWith (I := I) a h cov norm' x
        = Real.sqrt
            (Tensor0SBundle.normSq0S (I := I) norm' x (a + 2) A) := rfl
    _ <= Real.sqrt
          (C ^ (a + 2) *
            Tensor0SBundle.normSq0S (I := I) norm x (a + 2) A) :=
          Real.sqrt_le_sqrt hA_sq
    _ = Real.sqrt (C ^ (a + 2)) *
          metricCovDerivNormWith (I := I) a h cov norm x := by
          rw [Real.sqrt_mul (pow_nonneg hC_nonneg (a + 2))]
          rfl

/-- Book-facing norm conversion for the inverse-side metric derivatives:
`|nabla_h^a g|_g` is controlled by `|nabla_h^a g|_h` under the `C^0` part of a
two-sided approximate isometry. -/
theorem IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
    {K : Set M} {eps : Real} {p a : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) :
    metricCovDerivNormWith (I := I) a g h g x <=
      Real.sqrt ((1 + eps) ^ (a + 2)) *
        metricCovDerivNorm (I := I) a g h x := by
  simpa [metricCovDerivNorm_eq_with]
    using metricCovDerivNormWith_le_of_equiv
      (I := I) (hEq := metricUniformEquivalentOn_symm
        (I := I) Happrox.forward.uniform_equiv) hx a

/-- An approximate isometry compares all covariant tensor squared norms by the
expected powers of the `C^0` equivalence constant. -/
theorem IsApproxIsometryOn.normSq0S_compare
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (s : Nat)
    (T : Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    (1 + eps) ^ (-(s : Int)) *
        Tensor0SBundle.normSq0S (I := I) g x s T <=
      Tensor0SBundle.normSq0S (I := I) h x s T /\
    Tensor0SBundle.normSq0S (I := I) h x s T <=
      (1 + eps) ^ (s : Int) *
        Tensor0SBundle.normSq0S (I := I) g x s T := by
  exact Tensor0SBundle.normSq0S_le_of_metric_equiv
    (I := I) g h x s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- Non-method form of `IsApproxIsometryOn.normSq0S_compare`. -/
theorem normSq0S_compare_of_approxIsometry
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (s : Nat)
    (T : Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) s x) :
    (1 + eps) ^ (-(s : Int)) *
        Tensor0SBundle.normSq0S (I := I) g x s T <=
      Tensor0SBundle.normSq0S (I := I) h x s T /\
    Tensor0SBundle.normSq0S (I := I) h x s T <=
      (1 + eps) ^ (s : Int) *
        Tensor0SBundle.normSq0S (I := I) g x s T :=
  Happrox.normSq0S_compare (I := I) hx s T

/-- An approximate isometry compares all mixed-tensor squared norms by the
expected power of the `C^0` equivalence constant. -/
theorem IsApproxIsometryOn.normSqRS_compare
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    ((1 + eps) ^ (r + s))â»Â¹ *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T <=
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T /\
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T <=
      (1 + eps) ^ (r + s) *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T := by
  exact Tensor0SBundle.normSqRS_le_of_metric_equiv
    (I := I) g h x r s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- Non-method form of `IsApproxIsometryOn.normSqRS_compare`. -/
theorem normSqRS_compare_of_approxIsometry
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    ((1 + eps) ^ (r + s))â»Â¹ *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T <=
      Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T /\
    Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T <=
      (1 + eps) ^ (r + s) *
        Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T :=
  Happrox.normSqRS_compare (I := I) hx r s T

section BookTensorNorms

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I âˆž N] [SigmaCompactSpace N]
variable [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
variable [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) N]

/-- MSM135 Corollary "Norms of tensors", in the supplied-pullback-metric
form.  If a Riemannian metric `gh` on the source has the same quadratic form
as the pullback tensor `Phi^* h` on `K`, then an `(eps,0)` approximate isometry
compares mixed-tensor norms with the expected factor. -/
theorem bookNormRS_compare
    {K : Set M} {L : Set N} {eps : Real}
    {Phi : M â‰ƒâ‚˜âŸ®I, IâŸ¯ N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (H : BookApproxIsometryData (I := I) K L eps 0 Phi g h)
    (hMapsTo : Set.MapsTo (Phi : M -> N) K L)
    (gh : SmoothRiemannianMetric I M)
    (hgh : forall x : M, x âˆˆ K -> forall v : TangentSpace I x,
      gh.inner x v v =
        quad02 (I := I) (M := M) (H.forward.pullbackData.pullback x) v)
    {x : M} (hx : x âˆˆ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Tensor0SBundle.normRS (I := I) (g := gh) (x := x) r s T <=
        Real.sqrt ((1 + eps) ^ (r + s)) *
          Tensor0SBundle.normRS (I := I) (g := g) (x := x) r s T /\
      Tensor0SBundle.normRS (I := I) (g := g) (x := x) r s T <=
        Real.sqrt ((1 + eps) ^ (r + s)) *
          Tensor0SBundle.normRS (I := I) (g := gh) (x := x) r s T := by
  have hEq :
      MetricUniformEquivalentOn (I := I) K g gh (1 + eps) :=
    bookApprox_uniformEquiv_of_pullback (I := I) H hMapsTo gh hgh
  constructor
  Â· simpa [Tensor0SBundle.normRS_eq_sqrt_normSqRS]
      using Tensor0SBundle.sqrt_normRS_upper_le_of_equiv
        (I := I) g gh x r s hEq.1 (hEq.2 x hx) T
  Â· simpa [Tensor0SBundle.normRS_eq_sqrt_normSqRS]
      using Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
        (I := I) g gh x r s hEq.1 (hEq.2 x hx) T

end BookTensorNorms

/-- Square-root upper mixed-tensor norm comparison from the `C^0` part of an
approximate isometry. -/
theorem IsApproxIsometryOn.sqrt_normRS_upper
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Real.sqrt
        (Tensor0SBundle.normSqRS (I := I) (g := h) (x := x) r s T) <=
      Real.sqrt ((1 + eps) ^ (r + s)) *
        Real.sqrt
          (Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) r s T) := by
  exact Tensor0SBundle.sqrt_normRS_upper_le_of_equiv
    (I := I) g h x r s Happrox.uniform_equiv.1
    (Happrox.uniform_equiv.2 x hx) T

/-- F3 first producer, corresponding to the estimate preceding MSM135 Chapter 4
equation `lbl369`.

At a point with an `h`-orthonormal basis, an `(eps,p)` approximate isometry with
`1 <= p` bounds the norm of the Levi-Civita connection-difference tensor by the
first metric covariant-derivative smallness.  The book later combines this with
elementary numerical estimates when `eps < 1`; this theorem keeps the sharper
constant produced by the checked connection-difference API. -/
theorem connDiff_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
  have hdiff :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K) h g hx (1 + eps) Happrox.uniform_equiv basis hinv
  have hsmall :
      metricCovDerivNorm (I := I) 1 h g x <= eps :=
    Happrox.cov_deriv_small 1 le_rfl hp x hx
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x))
        <= (3 / 2 : Real) *
            (Real.sqrt ((1 + eps) ^ 3) *
              metricCovDerivNorm (I := I) 1 h g x) := hdiff
    _ = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) *
          metricCovDerivNorm (I := I) 1 h g x := by ring
    _ <= ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps :=
      mul_le_mul_of_nonneg_left hsmall hcoef_nonneg
    _ = (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by ring

/-- Book-orientation version of `connDiff_le_approx`.

This bounds `Gamma_g - Gamma_h` in the `g` norm using the inverse-side
derivative smallness `|nabla_h g|`. -/
theorem connDiff_book_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)) <=
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
  have hdiff :=
    diff_le_covOne_basis_ref_lc
      (I := I) (K := K) g h hx (1 + eps)
      (metricUniformEquivalentOn_symm (I := I) Happrox.forward.uniform_equiv)
      basis hinv
  have hsmall :
      metricCovDerivNorm (I := I) 1 g h x <= eps :=
    Happrox.reverse_cov_deriv_small 1 le_rfl hp x hx
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x))
        <= (3 / 2 : Real) *
            (Real.sqrt ((1 + eps) ^ 3) *
              metricCovDerivNorm (I := I) 1 g h x) := hdiff
    _ = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) *
          metricCovDerivNorm (I := I) 1 g h x := by ring
    _ <= ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps :=
      mul_le_mul_of_nonneg_left hsmall hcoef_nonneg
    _ = (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by ring

/-- Legacy-orientation base case for the connection-difference estimate in the
`g` norm.

This keeps the same `Gamma_h - Gamma_g` orientation as `connDiff_le_approx`.
The book-orientation version is `connDiff_book_le_eps_g`. -/
theorem connDiff_le_eps_g
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
      12 * eps := by
  let A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hC_nonneg : 0 <= (1 + eps) := by linarith
  have hpow_nonneg : 0 <= (1 + eps) ^ 3 := pow_nonneg hC_nonneg 3
  have hpow_le : (1 + eps) ^ 3 <= (8 : Real) := by
    have hbase_le : 1 + eps <= (2 : Real) := by linarith
    have hpow : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
      pow_le_pow_leftâ‚€ hC_nonneg hbase_le 3
    norm_num at hpow
    exact hpow
  have hcompare :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) 1 2 A) <=
        Real.sqrt ((1 + eps) ^ (1 + 2)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) 1 2 A) :=
    Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
      (I := I) g h x 1 2 Happrox.uniform_equiv.1
      (Happrox.uniform_equiv.2 x hx) A
  have hconn :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) 1 2 A) <=
        (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
    simpa [A] using
      connDiff_le_approx
        (I := I) Happrox hx hp basis hinv
  have hfirst :
      Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) 1 2 A) <=
        Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)) := by
    simpa using
      le_trans hcompare
        (mul_le_mul_of_nonneg_left hconn (Real.sqrt_nonneg _))
  have hsqrt_sq :
      Real.sqrt ((1 + eps) ^ 3) * Real.sqrt ((1 + eps) ^ 3) =
        (1 + eps) ^ 3 := by
    rw [â† pow_two, Real.sq_sqrt hpow_nonneg]
  have hcoef :
      Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)) =
        (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) := by
    calc
      Real.sqrt ((1 + eps) ^ 3) *
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
          =
        (3 / 2 : Real) *
          ((Real.sqrt ((1 + eps) ^ 3) *
            Real.sqrt ((1 + eps) ^ 3)) * eps) := by ring
      _ = (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) := by
            rw [hsqrt_sq]
  have hbound :
      (3 / 2 : Real) * ((1 + eps) ^ 3 * eps) <= 12 * eps := by
    have hmul :
        (1 + eps) ^ 3 * eps <= 8 * eps :=
      mul_le_mul_of_nonneg_right hpow_le heps_nonneg
    calc
      (3 / 2 : Real) * ((1 + eps) ^ 3 * eps)
          <= (3 / 2 : Real) * (8 * eps) := by
            exact mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 12 * eps := by ring
  exact hfirst.trans ((le_of_eq hcoef).trans hbound)

/-- Book-orientation `k = 0` connection-difference estimate in the `g` norm. -/
theorem connDiff_book_le_eps_g
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basis (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x)) <=
      12 * eps := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  have hC_nonneg : 0 <= (1 + eps) := by linarith
  have hpow_le : (1 + eps) ^ 3 <= (8 : Real) := by
    have hbase_le : 1 + eps <= (2 : Real) := by linarith
    have hpow : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
      pow_le_pow_leftâ‚€ hC_nonneg hbase_le 3
    norm_num at hpow
    exact hpow
  have hsqrt_le : Real.sqrt ((1 + eps) ^ 3) <= (8 : Real) := by
    have hsqrt : Real.sqrt ((1 + eps) ^ 3) <= Real.sqrt (8 : Real) :=
      Real.sqrt_le_sqrt hpow_le
    have hsqrt8 : Real.sqrt (8 : Real) <= (8 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt8
  have hbase :=
    connDiff_book_le_approx
      (I := I) Happrox hx hp basis hinv
  have hcoef :
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) <=
        12 * eps := by
    have hs :
        (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3) <= 12 := by
      calc
        (3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)
            <= (3 / 2 : Real) * 8 := by
              exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
        _ <= 12 := by norm_num
    calc
      (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)
          = ((3 / 2 : Real) * Real.sqrt ((1 + eps) ^ 3)) * eps := by ring
      _ <= 12 * eps := mul_le_mul_of_nonneg_right hs heps_nonneg
  exact hbase.trans hcoef

/-- A supplied smooth mixed `(1,2)` tensor field realizes the concrete
Levi-Civita connection-difference tensor.  This is the field-level bridge
needed before taking higher covariant derivatives; it is not an existence
assertion. -/
def ConnDiffFieldRealizes
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (g h : SmoothRiemannianMetric I M)
    (D : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 2) : Prop :=
  forall x : M,
    D x =
      Tensor0SBundle.connectionDifferenceTensorAt
        (I := I)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) x

/-- Pointwise `g`-norm of a supplied `k`-th `h`-covariant derivative of the
connection-difference tensor. -/
noncomputable def connDiffDerivNorm
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 (k + 2))
    (x : M) : Real :=
  Tensor0SBundle.fieldNormRS (I := I) g 1 (k + 2) Dk x

/-- A supplied mixed tensor field realizes the `k`-th `h`-covariant derivative
of `Gamma_g - Gamma_h`, the orientation used in MSM135 Chapter 4. -/
def ConnDiffDerivRealizes
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 (k + 2)) : Prop :=
  exists D : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 2,
    ConnDiffFieldRealizes (I := I) g h D âˆ§
      Tensor0SBundle.HigherCovDerivRSRealizes
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D k Dk

/-- The first positive-order connection-difference realization is an actual
total `h`-covariant derivative of the connection-difference field. -/
theorem ConnDiffDerivRealizes.one
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1) :
    exists D : Tensor0SBundle.TensorRSField
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (âˆž : WithTop â„•âˆž)) 1 2,
      ConnDiffFieldRealizes (I := I) g h D âˆ§
        Tensor0SBundle.TotalNablaRSRealizes
          (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) 1 2
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1 := by
  rcases hD1 with âŸ¨D, hD, hderivâŸ©
  exact âŸ¨D, hD, Tensor0SBundle.HigherCovDerivRSRealizes.one_12 hderivâŸ©

/-- The second positive-order connection-difference realization unpacks into
two successive total `h`-covariant derivatives. -/
theorem ConnDiffDerivRealizes.two
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D2 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 4}
    (hD2 : ConnDiffDerivRealizes (I := I) g h 2 D2) :
    exists D : Tensor0SBundle.TensorRSField
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (âˆž : WithTop â„•âˆž)) 1 2,
      ConnDiffFieldRealizes (I := I) g h D âˆ§
        exists D1 : Tensor0SBundle.TensorRSField
          (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (âˆž : WithTop â„•âˆž)) 1 3,
          Tensor0SBundle.TotalNablaRSRealizes
            (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) 1 2
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D D1 âˆ§
          Tensor0SBundle.TotalNablaRSRealizes
            (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) 1 3
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) D1 D2 := by
  rcases hD2 with âŸ¨D, hD, hderivâŸ©
  exact
    match hderiv with
    | Tensor0SBundle.HigherCovDerivRSRealizes.succ
        (Tensor0SBundle.HigherCovDerivRSRealizes.succ
          Tensor0SBundle.HigherCovDerivRSRealizes.zero hstep1) hstep2 =>
        by
          exact âŸ¨D, hD, _, by simpa using hstep1, by simpa using hstep2âŸ©

/-- Pointwise application form of the first realized connection-difference
derivative. -/
theorem ConnDiffDerivRealizes.one_apply
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž) (TangentSpace I : M -> Type _))
    (x : M) (Î² : Tensor0SBundle.Tensor0SSpace 1 I x)
    (slots : Fin 2 -> TangentSpace I x) :
    exists D : Tensor0SBundle.TensorRSField
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (âˆž : WithTop â„•âˆž)) 1 2,
      ConnDiffFieldRealizes (I := I) g h D âˆ§
        D1 x Î² (Fin.cons (X x) slots) =
          Tensor0SBundle.nablaRSFun
            (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
            1 2 (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            X D x Î² slots := by
  rcases hD1 with âŸ¨D, hD, hderivâŸ©
  exact âŸ¨D, hD,
    Tensor0SBundle.HigherCovDerivRSRealizes.one_apply_12
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      hderiv X x Î² slotsâŸ©

/-- Coordinate-frame component bridge for a realized first derivative of
`Gamma_g - Gamma_h`.

This is the HCG-facing wrapper around the coordinate theorem
`Coordinates.totalNabla_lcDiff_coordFrame`: a supplied `D1` realizing the first
`h`-covariant derivative has components equal to the differentiated
Christoffel-difference component formula. -/
theorem connDiffOne_coord
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (xâ‚€ : M) (d a b e : Coordinates.CoordinateIdx (ð•œ := Real) E)
    (hX : X xâ‚€ = Coordinates.coordinateFrameAt (I := I) xâ‚€ d xâ‚€) :
    Tensor0SBundle.componentRS (I := I)
        (Coordinates.coordinateFrameAt_toBasis (I := I) xâ‚€)
        (D1 xâ‚€) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h (Coordinates.coordinateFrameAt (I := I) xâ‚€)
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
        xâ‚€ d a b e := by
  rcases ConnDiffDerivRealizes.one (I := I) hD1 with âŸ¨D, hD, hstepâŸ©
  exact
    Coordinates.totalNabla_lcDiff_coordFrame
      (I := I) g h D D1 hD hstep X xâ‚€ d a b e hX

/-- Local-frame component bridge for a realized first derivative of
`Gamma_g - Gamma_h`.

This is the HCG-facing wrapper around
`Coordinates.totalNabla_lcDiff_localFrame`: it identifies any supplied
`ConnDiffDerivRealizes ... 1` field with the local-frame component formula for
`nabla_h (Gamma_g - Gamma_h)`. -/
theorem connDiffOne_localFrame
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ j : Idx,
      (fun y : M => Î± y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0) :
    Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h frame hframe x d a b e := by
  rcases ConnDiffDerivRealizes.one (I := I) hD1 with âŸ¨D, hD, hstepâŸ©
  exact
    Coordinates.totalNabla_lcDiff_localFrame
      (I := I) g h D D1 hD hstep X Z Î± frame hframe hu hx d a b e
      hX hZ hpair

/-- Trivialization-local-frame component bridge for a realized second derivative
of `Gamma_g - Gamma_h`.

This is the HCG wrapper around
`Coordinates.totalNabla_lcDiff2_trivFrame`: it unpacks
`ConnDiffDerivRealizes ... 2` into two total `h`-covariant derivatives and
identifies the resulting local-frame component with `lcDiff2Comp`. -/
theorem connDiffTwo_trivFrame
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D2 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 4}
    (hD2 : ConnDiffDerivRealizes (I := I) g h 2 D2)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (basisE : Module.Basis Idx Real E) {x : M}
    (m d a b e : Idx)
    (hX :
      X x =
        (trivializationAt E (TangentSpace I : M -> Type _) x).localFrame basisE m x) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    let hx : x âˆˆ u := mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
    Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx) (D2 x)
        (Coordinates.upperIdx1 e) (Coordinates.slots4 m d a b) =
      Coordinates.lcDiff2Comp (I := I) g h frame hframe x m d a b e := by
  rcases ConnDiffDerivRealizes.two (I := I) hD2 with
    âŸ¨D, hD, D1, hstep1, hstep2âŸ©
  exact
    Coordinates.totalNabla_lcDiff2_trivFrame
      (I := I) (M := M) (Idx := Idx)
      g h D D1 D2 hD hstep1 hstep2 X basisE m d a b e hX

/-- Local-frame component of a realized first derivative of
`Gamma_g - Gamma_h`, after substituting the differentiated Christoffel
formula.  This is the frame-flexible version of `connDiffOne_quad`: the right
hand side contains only the book's `nabla_h^2 g` and quadratic
`(nabla_h g) * (nabla_h g)` terms. -/
theorem connDiffOne_localFrame_quad
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ j : Idx,
      (fun y : M => Î± y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  have hlocal :=
    connDiffOne_localFrame
      (I := I) hD1 X Z Î± frame hframe hu hx d a b e hX hZ hpair
  have hquad :=
    Coordinates.lcDiffDeriv_eq_quad
      (I := I) g h gInv frame hframe hu hx hinv d a b e hD_mdiff
      hginv_mdiff hmetric_mdiff hA_mdiff
  calc
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b)
        =
      2 * Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h frame hframe x d a b e := by
          rw [hlocal]
    _ = Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := hquad

/-- Local-inverse version of `connDiffOne_localFrame_quad`.

This component bridge uses the coordinate-local differentiated Christoffel
formula, so it does not require a global inverse-metric component package for a
local frame. -/
theorem connDiffOne_localFrame_quad_local
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ j : Idx,
      (fun y : M => Î± y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => âˆ‘ k : Idx,
          gInv y i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =á¶ [nhds x]
        fun _ : M => if i = j then 1 else 0)
    (hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame hframe y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x) :
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := by
  have hlocal :=
    connDiffOne_localFrame
      (I := I) hD1 X Z Î± frame hframe hu hx d a b e hX hZ hpair
  have hquad :=
    Coordinates.lcDiffDeriv_eq_quad_local
      (I := I) g h gInv frame hframe hu hx hinvX hinvLeftN d a b e
      hD_mdiff hginv_mdiff hmetric_mdiff hA_mdiff
  calc
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b)
        =
      2 * Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h frame hframe x d a b e := by
          rw [hlocal]
    _ = Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x d a b e := hquad

/-- Infinite-smooth local-frame wrapper for `connDiffOne_localFrame_quad`.

The differentiated Christoffel formula only needs a `C^1` frame, but the
metric covariant-derivative component bridges in `AllTimesBounds` use an
infinite-smooth local frame.  This wrapper keeps the component basis from the
infinite frame while downgrading the regularity proof internally. -/
theorem connDiffOne_frameInf_quad
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ j : Idx,
      (fun y : M => Î± y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
          y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b e := by
  let hframe1 : IsLocalFrameOn I E (1 : WithTop â„•âˆž) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  have hmain :=
    connDiffOne_localFrame_quad
      (I := I) hD1 X Z Î± frame hframe1 hu hx gInv d a b e
      hX hZ hpair hinv hD_mdiff hginv_mdiff hmetric_mdiff hA_mdiff
  have hbasis : hframe1.toBasisAt hx = hframe.toBasisAt hx := by
    ext i
    simp [IsLocalFrameOn.toBasisAt_coe]
  simpa [hframe1, hbasis] using hmain

/-- Infinite-smooth local-frame wrapper for
`connDiffOne_localFrame_quad_local`. -/
theorem connDiffOne_frameInf_quad_local
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (d a b e : Idx)
    (hX : X x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ j : Idx,
      (fun y : M => Î± y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => âˆ‘ k : Idx,
          gInv y i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =á¶ [nhds x]
        fun _ : M => if i = j then 1 else 0)
    (hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
          y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
        (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b e := by
  let hframe1 : IsLocalFrameOn I E (1 : WithTop â„•âˆž) frame u :=
    localFrameOneOfInf (I := I) frame hframe
  have hmain :=
    connDiffOne_localFrame_quad_local
      (I := I) hD1 X Z Î± frame hframe1 hu hx gInv d a b e
      hX hZ hpair hinvX hinvLeftN hD_mdiff hginv_mdiff hmetric_mdiff hA_mdiff
  have hbasis : hframe1.toBasisAt hx = hframe.toBasisAt hx := by
    ext i
    simp [IsLocalFrameOn.toBasisAt_coe]
  simpa [hframe1, hbasis] using hmain

/-- In a fixed tangent trivialization frame, the scalar components of
`Gamma_g - Gamma_h` are differentiable.  Unlike `lcDiffComp_triv_mdiff`, this
keeps the trivialization fixed and varies the point inside its base set. -/
theorem lcDiffComp_e_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (eâ‚€ : Bundle.Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas eâ‚€]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (hx : x âˆˆ eâ‚€.baseSet)
    (a b eIdx : Idx) :
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M => Coordinates.lcDiffCompInFrame
        (I := I) g h frame hframe y a b eIdx) x := by
  classical
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframeInf : IsLocalFrameOn I E âˆž frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I âˆž basisE
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hg :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE g hx a b eIdx
  have hh :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE h hx a b eIdx
  have hdiff :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y)) -
            eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y))) x :=
    hg.sub hh
  have htarget :
      (fun y : M => Coordinates.lcDiffCompInFrame
        (I := I) g h frame hframe1 y a b eIdx) =á¶ [nhds x]
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y)) -
            eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y))) := by
    filter_upwards [eâ‚€.open_baseSet.mem_nhds hx] with y hy
    have hyu : y âˆˆ u := by
      simpa [u] using hy
    have hmdiff : MDiffAt (T% (frame b)) y :=
      (hframeInf.contMDiffAt eâ‚€.open_baseSet hyu b).mdifferentiableAt
        (by simp : (âˆž : WithTop â„•âˆž) â‰  0)
    change Coordinates.christoffelSymbolDifferenceInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe1 y a b eIdx =
      eâ‚€.localFrame_coeff I basisE eIdx y
          ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
              (eâ‚€.localFrame basisE b) y)
            (eâ‚€.localFrame basisE a y)) -
        eâ‚€.localFrame_coeff I basisE eIdx y
          ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
              (eâ‚€.localFrame basisE b) y)
            (eâ‚€.localFrame basisE a y))
    rw [Coordinates.christoffelSymbolDifferenceInFrame_eq_sub
      (I := I)
      (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (cov' := LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (frame := frame) (hframe := hframe1)
      (x := y) (i := a) (j := b) (k := eIdx) hmdiff]
    have hbasis : hframe1.toBasisAt hyu = eâ‚€.basisAt basisE hy := by
      ext j
      simp [frame, IsLocalFrameOn.toBasisAt,
        Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy]
    simp [Coordinates.christoffelSymbolInFrame, frame,
      IsLocalFrameOn.coeff, hyu, hy, Bundle.Trivialization.localFrame_coeff,
      hbasis]
  exact (hdiff.congr_of_eventuallyEq htarget).mdifferentiableAt (by simp)

/-- Levi-Civita Christoffel coefficients in a fixed tangent trivialization
frame are smooth when written through `christoffelSymbolInFrame`. -/
theorem lcChrist_e_contMDiffAt
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (eâ‚€ : Bundle.Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas eâ‚€]
    (g : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (hx : x âˆˆ eâ‚€.baseSet)
    (i j k : Idx) :
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun a y => eâ‚€.localFrame basisE a y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    ContMDiffAt I ð“˜(Real, Real) âˆž
      (fun y : M => Coordinates.christoffelSymbolInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe y i j k) x := by
  classical
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun a y => eâ‚€.localFrame basisE a y
  let u : Set M := eâ‚€.baseSet
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hraw :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE g hx i j k
  have heq :
      (fun y : M => Coordinates.christoffelSymbolInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe1 y i j k) =á¶ [nhds x]
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE k y
            ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                (eâ‚€.localFrame basisE j) y)
              (eâ‚€.localFrame basisE i y))) := by
    filter_upwards [eâ‚€.open_baseSet.mem_nhds hx] with y hy
    have hyu : y âˆˆ u := by
      simpa [u] using hy
    have hbasis : hframe1.toBasisAt hyu = eâ‚€.basisAt basisE hy := by
      ext q
      simp [frame, IsLocalFrameOn.toBasisAt,
        Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy]
    simp [Coordinates.christoffelSymbolInFrame, frame,
      IsLocalFrameOn.coeff, hyu, hy, Bundle.Trivialization.localFrame_coeff,
      hbasis]
  exact hraw.congr_of_eventuallyEq heq.symm

/-- First metric-covariant-derivative components in a fixed tangent
trivialization frame are smooth. -/
theorem metricCov_e_contMDiffAt
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (eâ‚€ : Bundle.Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas eâ‚€]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (hx : x âˆˆ eâ‚€.baseSet)
    (i j k : Idx) :
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun a y => eâ‚€.localFrame basisE a y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    ContMDiffAt I ð“˜(Real, Real) âˆž
      (fun y : M =>
        Coordinates.metricCovDerivForMetricCompInFrame
          (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe y i j k) x := by
  classical
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun a y => eâ‚€.localFrame basisE a y
  let u : Set M := eâ‚€.baseSet
  let hframeInf : IsLocalFrameOn I E âˆž frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I âˆž basisE
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hxi : ContMDiffAt I (I.prod ð“˜(Real, E)) âˆž (T% (frame i)) x :=
    hframeInf.contMDiffAt eâ‚€.open_baseSet (by simpa [u] using hx) i
  have hmetric (a b : Idx) :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame (I := I) g frame y a b) x := by
    simpa [frame] using
      LeviCivita.localFrame_metricComp_contMDiffAt
        (I := I) eâ‚€ basisE g hx a b
  have hderiv :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          extDerivFun (I := I)
            (fun q : M =>
              Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
            y (frame i y)) x :=
    extDerivFun_apply_contMDiffAt_of_section
      (I := I)
      (f := fun q : M =>
        Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
      (X := frame i) (hmetric j k) hxi
  have hsum1 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i j p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y p k) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx i j p).mul (hmetric p k)
  have hsum2 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i k p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y j p) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx i k p).mul (hmetric j p)
  exact (hderiv.sub hsum1).sub hsum2

/-- First metric-covariant-derivative components in a fixed tangent
trivialization frame are differentiable. -/
theorem metricCov_e_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (eâ‚€ : Bundle.Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas eâ‚€]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (hx : x âˆˆ eâ‚€.baseSet)
    (i j k : Idx) :
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun a y => eâ‚€.localFrame basisE a y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M =>
        Coordinates.metricCovDerivForMetricCompInFrame
          (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe y i j k) x := by
  classical
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun a y => eâ‚€.localFrame basisE a y
  let u : Set M := eâ‚€.baseSet
  let hframeInf : IsLocalFrameOn I E âˆž frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I âˆž basisE
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hxi : ContMDiffAt I (I.prod ð“˜(Real, E)) âˆž (T% (frame i)) x :=
    hframeInf.contMDiffAt eâ‚€.open_baseSet (by simpa [u] using hx) i
  have hmetric (a b : Idx) :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame (I := I) g frame y a b) x := by
    simpa [frame] using
      LeviCivita.localFrame_metricComp_contMDiffAt
        (I := I) eâ‚€ basisE g hx a b
  have hderiv :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          extDerivFun (I := I)
            (fun q : M =>
              Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
            y (frame i y)) x :=
    extDerivFun_apply_contMDiffAt_of_section
      (I := I)
      (f := fun q : M =>
        Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
      (X := frame i) (hmetric j k) hxi
  have hsum1 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i j p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y p k) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx i j p).mul (hmetric p k)
  have hsum2 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i k p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y j p) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx i k p).mul (hmetric j p)
  have htotal := (hderiv.sub hsum1).sub hsum2
  exact (by
    simpa [Coordinates.metricCovDerivForMetricCompInFrame, hframe1] using
      htotal.mdifferentiableAt (by simp))

/-- Second metric-covariant-derivative components in a fixed tangent
trivialization frame are differentiable. -/
theorem metricCov2_e_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (eâ‚€ : Bundle.Trivialization E
      (TotalSpace.proj : TotalSpace E (TangentSpace I : M -> Type _) -> M))
    [MemTrivializationAtlas eâ‚€]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (hx : x âˆˆ eâ‚€.baseSet)
    (d a b c : Idx) :
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M =>
        Coordinates.metricCovDeriv2ForMetricCompInFrame
          (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe y d a b c) x := by
  classical
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframeInf : IsLocalFrameOn I E âˆž frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I âˆž basisE
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hxd : ContMDiffAt I (I.prod ð“˜(Real, E)) âˆž (T% (frame d)) x :=
    hframeInf.contMDiffAt eâ‚€.open_baseSet (by simpa [u] using hx) d
  have hA (i j k : Idx) :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y i j k) x := by
    simpa [frame, u, hframe1] using
      metricCov_e_contMDiffAt
        (I := I) eâ‚€ g h basisE (x := x) hx i j k
  have hderiv :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          extDerivFun (I := I)
            (fun q : M =>
              Coordinates.metricCovDerivForMetricCompInFrame
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 q a b c)
            y (frame d y)) x :=
    extDerivFun_apply_contMDiffAt_of_section
      (I := I)
      (f := fun q : M =>
        Coordinates.metricCovDerivForMetricCompInFrame
          (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe1 q a b c)
      (X := frame d) (hA a b c) hxd
  have hsum1 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d a p *
              Coordinates.metricCovDerivForMetricCompInFrame
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y p b c) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx d a p).mul (hA p b c)
  have hsum2 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d b p *
              Coordinates.metricCovDerivForMetricCompInFrame
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y a p c) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx d b p).mul (hA a p c)
  have hsum3 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d c p *
              Coordinates.metricCovDerivForMetricCompInFrame
                (I := I) g
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y a b p) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_e_contMDiffAt
        (I := I) eâ‚€ h basisE (x := x) hx d c p).mul (hA a b p)
  have htotal := ((hderiv.sub hsum1).sub hsum2).sub hsum3
  exact (by
    simpa [Coordinates.metricCovDeriv2ForMetricCompInFrame, hframe1] using
      htotal.mdifferentiableAt (by simp))

/-- The substituted first-derivative Christoffel RHS is differentiable in a
fixed tangent trivialization frame. -/
theorem lcDiffQuadRHS_e_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M}
    (d a b eIdx : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe1 : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    let gInv : M -> Idx -> Idx -> Real :=
      fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M =>
        Coordinates.lcDiffQuadRHS
          (I := I) g gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe1 y d a b eIdx) x := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  have hU (i j : Idx) :
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x :=
    (LeviCivita.localInvMetricCoeff_contMDiffAt
      (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j).mdifferentiableAt
        (by simp)
  have hA1 (i j k : Idx) :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y i j k) x := by
    simpa [frame, u, hframe1] using
      metricCov_e_mdiff
        (I := I) eâ‚€ g h basisE (by simpa [u] using hx) i j k
  have hA2 (i j k l : Idx) :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDeriv2ForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y i j k l) x := by
    simpa [frame, u, hframe1] using
      metricCov2_e_mdiff
        (I := I) eâ‚€ g h basisE (by simpa [u] using hx) i j k l
  have hS (i j k : Idx) :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.lcDiffSymMetricCovComp
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y i j k) x := by
    simpa [Coordinates.lcDiffSymMetricCovComp] using
      ((hA1 i j k).add (hA1 j i k)).sub (hA1 k i j)
  have hinner (c : Idx) :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => âˆ‘ r : Idx, âˆ‘ q : Idx,
          gInv y eIdx r * gInv y c q *
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 y d r q) x := by
    refine Coordinates.mdiffAt_finset_sum_pointwise_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun r y => âˆ‘ q : Idx,
        gInv y eIdx r * gInv y c q *
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y d r q) ?_
    intro r _hr
    refine Coordinates.mdiffAt_finset_sum_pointwise_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun q y =>
        gInv y eIdx r * gInv y c q *
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y d r q) ?_
    intro q _hq
    exact ((hU eIdx r).mul (hU c q)).mul (hA1 d r q)
  have hfirst :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => âˆ‘ c : Idx,
          (-(âˆ‘ r : Idx, âˆ‘ q : Idx,
            gInv y eIdx r * gInv y c q *
              Coordinates.metricCovDerivForMetricCompInFrame
                (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d r q)) *
              Coordinates.lcDiffSymMetricCovComp
                (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y a b c) x := by
    refine Coordinates.mdiffAt_finset_sum_pointwise_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun c y =>
        (-(âˆ‘ r : Idx, âˆ‘ q : Idx,
          gInv y eIdx r * gInv y c q *
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 y d r q)) *
          Coordinates.lcDiffSymMetricCovComp
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 y a b c) ?_
    intro c _hc
    exact (hinner c).neg.mul (hS a b c)
  have hsecond :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => âˆ‘ c : Idx,
          gInv y eIdx c *
            (Coordinates.metricCovDeriv2ForMetricCompInFrame
                (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d a b c +
              Coordinates.metricCovDeriv2ForMetricCompInFrame
                (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d b a c -
              Coordinates.metricCovDeriv2ForMetricCompInFrame
                (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y d c a b)) x := by
    refine Coordinates.mdiffAt_finset_sum_pointwise_real
      (I := I) (t := (Finset.univ : Finset Idx))
      (f := fun c y =>
        gInv y eIdx c *
          (Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 y d a b c +
            Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 y d b a c -
            Coordinates.metricCovDeriv2ForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe1 y d c a b)) ?_
    intro c _hc
    exact (hU eIdx c).mul (((hA2 d a b c).add (hA2 d b a c)).sub (hA2 d c a b))
  simpa [Coordinates.lcDiffQuadRHS, gInv, frame, hframe1] using hfirst.add hsecond

/-- In a fixed tangent-trivialization frame, the first-derivative
Christoffel-difference formula holds eventually near the base point.  This is
the honest producer for the `hquad_ev` input of `lcDiff2_eq_cubic`. -/
theorem lcDiffQuad_ev_triv
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M}
    (d a b eIdx : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe1 : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    let gInv : M -> Idx -> Idx -> Real :=
      fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
    (fun y : M =>
      2 * Coordinates.lcDiffCovDerivCompInFrame (I := I) g h frame hframe1
        y d a b eIdx) =á¶ [nhds x]
      fun y : M =>
        Coordinates.lcDiffQuadRHS
          (I := I) g gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe1 y d a b eIdx := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  filter_upwards [eâ‚€.open_baseSet.mem_nhds (by simpa [u] using hx)] with y hy
  have hyu : y âˆˆ u := by simpa [u] using hy
  have hinvY : forall i j : Idx,
      (âˆ‘ k : Idx, gInv y i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame y i k *
            gInv y k j) =
          (if i = j then 1 else 0) := by
    intro i j
    constructor
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_left_inv
          (I := I) eâ‚€ basisE g hy i j
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_right_inv
          (I := I) eâ‚€ basisE g hy i j
  have hinvLeftN : forall i j : Idx,
      (fun z : M => âˆ‘ k : Idx,
          gInv z i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame z k j) =á¶ [nhds y]
        fun _ : M => if i = j then 1 else 0 := by
    intro i j
    simpa [gInv, frame, u] using
      LeviCivita.localInvMetricCoeff_metricComp_left_inv_eventually
        (I := I) eâ‚€ basisE g hy i j
  have hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun z : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame hframe1 z a b eIdx) y := by
    simpa [frame, u, hframe1] using
      lcDiffComp_e_mdiff
        (I := I) eâ‚€ g h basisE hy a b eIdx
  have hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun z : M => gInv z i j) y := by
    intro i j
    exact
      (LeviCivita.localInvMetricCoeff_contMDiffAt
        (I := I) eâ‚€ basisE g hy i j).mdifferentiableAt (by simp)
  have hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun z : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame z i j) y := by
    intro i j
    simpa [frame] using
      LeviCivita.localFrame_metricComp_mdiff
        (I := I) eâ‚€ basisE g hy i j
  have hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun z : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 z i j k) y := by
    intro i j k
    simpa [frame, u, hframe1] using
      metricCov_e_mdiff
        (I := I) eâ‚€ g h basisE hy i j k
  exact
    Coordinates.lcDiffDeriv_eq_quad_local
      (I := I) g h gInv frame hframe1 eâ‚€.open_baseSet hy hinvY
      hinvLeftN d a b eIdx hD_mdiff hginv_mdiff hmetric_mdiff hA_mdiff

/-- In a fixed tangent trivialization frame, the first covariant derivative
component of `Gamma_g - Gamma_h` is differentiable. -/
theorem lcDiffCovDeriv_e_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M}
    (d a b eIdx : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe1 : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M =>
        Coordinates.lcDiffCovDerivCompInFrame
          (I := I) g h frame hframe1 y d a b eIdx) x := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  have hRhs :=
    lcDiffQuadRHS_e_mdiff
      (I := I) g h basisE (x := x) d a b eIdx
  have hEq :=
    lcDiffQuad_ev_triv
      (I := I) g h basisE (x := x) d a b eIdx
  have hTwo :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          2 * Coordinates.lcDiffCovDerivCompInFrame
            (I := I) g h frame hframe1 y d a b eIdx) x := by
    simpa [gInv, frame, hframe1] using hRhs.congr_of_eventuallyEq hEq
  have hScaled := hTwo.const_smul ((1 / 2 : Real))
  have hEqFun :
      (fun y : M =>
        Coordinates.lcDiffCovDerivCompInFrame
          (I := I) g h frame hframe1 y d a b eIdx) =
        ((1 / 2 : Real) â€¢ fun y : M =>
          2 * Coordinates.lcDiffCovDerivCompInFrame
            (I := I) g h frame hframe1 y d a b eIdx) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  change MDifferentiableAt I ð“˜(Real, Real)
    (fun y : M =>
      Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h frame hframe1 y d a b eIdx) x
  rw [hEqFun]
  exact hScaled

/-- Trivialization-frame component of a realized second derivative of
`Gamma_g - Gamma_h`, after the coordinate-layer cubic reassembly. -/
theorem connDiffTwo_trivFrame_cubic
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D2 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 4}
    (hD2 : ConnDiffDerivRealizes (I := I) g h 2 D2)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (basisE : Module.Basis Idx Real E) {x : M}
    (m d a b eIdx : Idx)
    (hX :
      X x =
        (trivializationAt E (TangentSpace I : M -> Type _) x).localFrame basisE m x) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E 1 frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
    let hx : x âˆˆ u := mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
    let gInv : M -> Idx -> Idx -> Real :=
      fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx) (D2 x)
        (Coordinates.upperIdx1 eIdx) (Coordinates.slots4 m d a b) =
      Coordinates.lcDiffQuadCubicRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x m d a b eIdx := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  have hcomp :=
    connDiffTwo_trivFrame
      (I := I) hD2 X basisE (x := x) m d a b eIdx hX
  have hquad_ev :
      (fun y : M =>
        2 * Coordinates.lcDiffCovDerivCompInFrame
          (I := I) g h frame hframe y d a b eIdx) =á¶ [nhds x]
      fun y : M =>
        Coordinates.lcDiffQuadRHS
          (I := I) g gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe y d a b eIdx := by
    simpa [frame, u, hframe, gInv] using
      lcDiffQuad_ev_triv (I := I) g h basisE (x := x) d a b eIdx
  have hquad_at : âˆ€ i j k l : Idx,
      2 * Coordinates.lcDiffCovDerivCompInFrame (I := I) g h frame hframe x i j k l =
        Coordinates.lcDiffQuadRHS
          (I := I) g gInv
          (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x i j k l := by
    intro i j k l
    have hev :=
      lcDiffQuad_ev_triv (I := I) g h basisE (x := x) i j k l
    simpa [frame, u, hframe, gInv] using hev.self_of_nhds
  have hD1_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.lcDiffCovDerivCompInFrame
            (I := I) g h frame hframe y d a b eIdx) x := by
    simpa [frame, u, hframe] using
      lcDiffCovDeriv_e_mdiff
        (I := I) g h basisE (x := x) d a b eIdx
  have hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x := by
    intro i j
    exact
      (LeviCivita.localInvMetricCoeff_contMDiffAt
        (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j).mdifferentiableAt
        (by simp)
  have hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x := by
    intro i j
    simpa [frame] using
      LeviCivita.localFrame_metricComp_mdiff
        (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
  have hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k) x := by
    intro i j k
    simpa [frame, u, hframe] using
      metricCov_e_mdiff
        (I := I) eâ‚€ g h basisE (by simpa [u] using hx) i j k
  have hA2_mdiff : âˆ€ i j k l : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDeriv2ForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe y i j k l) x := by
    intro i j k l
    simpa [frame, u, hframe] using
      metricCov2_e_mdiff
        (I := I) eâ‚€ g h basisE (by simpa [u] using hx) i j k l
  have hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0) := by
    intro i j
    constructor
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_left_inv
          (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_right_inv
          (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
  have hinvLeftN : forall i j : Idx,
      (fun y : M => âˆ‘ k : Idx,
          gInv y i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =á¶ [nhds x]
        fun _ : M => if i = j then 1 else 0 := by
    intro i j
    simpa [gInv, frame, u] using
      LeviCivita.localInvMetricCoeff_metricComp_left_inv_eventually
        (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
  have hExtInv : âˆ€ i j : Idx,
      extDerivFun (I := I) (fun y : M => gInv y i j) x (frame m x) =
        Coordinates.lcDiffInvQuad
          (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame hframe x m i j -
          (âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x m p i * gInv x p j) -
          (âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame hframe x m p j * gInv x i p) := by
    intro i j
    exact
      Coordinates.gInv_extDeriv_eq_lcDiffInvQuad_sub_local
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe hinvX hinvLeftN hginv_mdiff hmetric_mdiff m i j
  have hcubic :=
    Coordinates.lcDiff2_eq_cubic
      (I := I) g h gInv frame hframe m d a b eIdx
      hquad_ev hquad_at hD1_mdiff hginv_mdiff hA_mdiff hA2_mdiff hExtInv
  calc
    2 * Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx) (D2 x)
        (Coordinates.upperIdx1 eIdx) (Coordinates.slots4 m d a b)
        =
      2 * Coordinates.lcDiff2Comp (I := I) g h frame hframe x m d a b eIdx := by
        rw [hcomp]
    _ =
      Coordinates.lcDiffQuadCubicRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe x m d a b eIdx := hcubic

/-- A local inverse-metric component function agrees with the identity matrix
at a point where the local frame is `g`-orthonormal. -/
theorem gInv_eq_identity_at
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g : SmoothRiemannianMetric I M}
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    {x : M} (hx : x âˆˆ u)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (i j : Idx) :
    gInv x i j = Tensor0SBundle.identityInvMetric (Idx := Idx) i j := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx) (fun i j : Idx => gInv x i j) := by
    intro i j
    constructor
    Â· simpa [Coordinates.metricCompForMetricInFrame,
        IsLocalFrameOn.toBasisAt_coe] using (hinv x i j).1
    Â· simpa [Coordinates.metricCompForMetricInFrame,
        IsLocalFrameOn.toBasisAt_coe] using (hinv x i j).2
  have hEq :=
    Tensor0SBundle.MetricInverseInBasis.eq_of
      (I := I) g x (hframe.toBasisAt hx) hinvAt hinvBasis
  exact congrFun (congrFun hEq i) j

/-- Pointwise version of `gInv_eq_identity_at`. -/
theorem gInv_eq_identity_at_local
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g : SmoothRiemannianMetric I M}
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    {x : M} (hx : x âˆˆ u)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (i j : Idx) :
    gInv x i j = Tensor0SBundle.identityInvMetric (Idx := Idx) i j := by
  have hinvAt :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx) (fun i j : Idx => gInv x i j) := by
    intro i j
    constructor
    Â· simpa [Coordinates.metricCompForMetricInFrame,
        IsLocalFrameOn.toBasisAt_coe] using (hinvX i j).1
    Â· simpa [Coordinates.metricCompForMetricInFrame,
        IsLocalFrameOn.toBasisAt_coe] using (hinvX i j).2
  have hEq :=
    Tensor0SBundle.MetricInverseInBasis.eq_of
      (I := I) g x (hframe.toBasisAt hx) hinvAt hinvBasis
  exact congrFun (congrFun hEq i) j

/-- Coarse finite-sum bound for the substituted differentiated
Christoffel-difference RHS.

This is purely algebraic: if the inverse-metric components are bounded by `1`,
the first metric-derivative components are bounded by `N1`, and the second
metric-derivative components are bounded by `N2`, then the local-frame RHS is
bounded by a dimension-dependent expression. -/
theorem lcDiffQuad_abs_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (d a b e : Idx) {N1 N2 : Real}
    (hN1 : 0 <= N1) (hN2 : 0 <= N2)
    (hU : forall i j : Idx, |gInv x i j| <= 1)
    (hA1 : forall i j k : Idx,
      |Coordinates.metricCovDerivForMetricCompInFrame
        (I := I) g cov frame hframe x i j k| <= N1)
    (hA2 : forall i j k l : Idx,
      |Coordinates.metricCovDeriv2ForMetricCompInFrame
        (I := I) g cov frame hframe x i j k l| <= N2) :
    |Coordinates.lcDiffQuadRHS
        (I := I) g gInv cov frame hframe x d a b e| <=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) * N1)) * (3 * N1)) +
        (Fintype.card Idx : Real) * (3 * N2) := by
  classical
  let U : Idx -> Idx -> Real := fun i j => gInv x i j
  let A1 : Idx -> Idx -> Idx -> Real := fun i j k =>
    Coordinates.metricCovDerivForMetricCompInFrame
      (I := I) g cov frame hframe x i j k
  let A2 : Idx -> Idx -> Idx -> Idx -> Real := fun i j k l =>
    Coordinates.metricCovDeriv2ForMetricCompInFrame
      (I := I) g cov frame hframe x i j k l
  let S : Idx -> Idx -> Idx -> Real := fun i j k =>
    Coordinates.lcDiffSymMetricCovComp (I := I) g cov frame hframe x i j k
  have hcard_nonneg : 0 <= (Fintype.card Idx : Real) := by positivity
  have hinner_nonneg :
      0 <= (Fintype.card Idx : Real) *
        ((Fintype.card Idx : Real) * N1) := by positivity
  have hS_bound (i j k : Idx) :
      |S i j k| <= 3 * N1 := by
    have htri :
        |A1 i j k + A1 j i k - A1 k i j| <=
          |A1 i j k| + |A1 j i k| + |A1 k i j| := by
      calc
        |A1 i j k + A1 j i k - A1 k i j|
            = |(A1 i j k + A1 j i k) + (-(A1 k i j))| := by ring_nf
        _ <= |A1 i j k + A1 j i k| + |-(A1 k i j)| := abs_add_le _ _
        _ <= (|A1 i j k| + |A1 j i k|) + |A1 k i j| := by
              simpa [abs_neg] using
                add_le_add_right (abs_add_le (A1 i j k) (A1 j i k)) |-(A1 k i j)|
        _ = |A1 i j k| + |A1 j i k| + |A1 k i j| := by ring
    have hS_eq :
        S i j k = A1 i j k + A1 j i k - A1 k i j := by
      simp [S, A1, Coordinates.lcDiffSymMetricCovComp]
    rw [hS_eq]
    have hi := hA1 i j k
    have hj := hA1 j i k
    have hk := hA1 k i j
    linarith [htri, hi, hj, hk]
  have hprod_bound (c r q : Idx) :
      |U e r * U c q * A1 d r q| <= N1 := by
    have h1_nonneg : 0 <= |U e r| := abs_nonneg _
    have h2_nonneg : 0 <= |U c q| := abs_nonneg _
    have hA_nonneg : 0 <= |A1 d r q| := abs_nonneg _
    have h12 :
        |U e r| * |U c q| <= 1 := by
      nlinarith [hU e r, hU c q, h1_nonneg, h2_nonneg]
    have h123 :
        |U e r| * |U c q| * |A1 d r q| <= N1 := by
      nlinarith [h12, hA1 d r q, hN1, hA_nonneg]
    calc
      |U e r * U c q * A1 d r q|
          = |U e r| * |U c q| * |A1 d r q| := by rw [abs_mul, abs_mul]
      _ <= N1 := h123
  have hinner (c : Idx) :
      |âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q| <=
        (Fintype.card Idx : Real) * ((Fintype.card Idx : Real) * N1) := by
    calc
      |âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q|
          <= âˆ‘ r : Idx, |âˆ‘ q : Idx, U e r * U c q * A1 d r q| :=
            Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ r : Idx, âˆ‘ q : Idx, |U e r * U c q * A1 d r q| := by
            exact Finset.sum_le_sum fun r _ =>
              Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ _r : Idx, âˆ‘ _q : Idx, N1 := by
            refine Finset.sum_le_sum ?_
            intro r _
            refine Finset.sum_le_sum ?_
            intro q _
            exact hprod_bound c r q
      _ = (Fintype.card Idx : Real) * ((Fintype.card Idx : Real) * N1) := by
            simp
  have hfirst_term (c : Idx) :
      |(-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c| <=
        ((Fintype.card Idx : Real) *
            ((Fintype.card Idx : Real) * N1)) * (3 * N1) := by
    calc
      |(-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c|
          =
        |âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q| * |S a b c| := by
          rw [abs_mul, abs_neg]
      _ <=
        ((Fintype.card Idx : Real) *
            ((Fintype.card Idx : Real) * N1)) * (3 * N1) := by
          exact mul_le_mul (hinner c) (hS_bound a b c)
            (abs_nonneg _) hinner_nonneg
  have hfirst :
      |âˆ‘ c : Idx,
          (-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c| <=
        (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) * N1)) * (3 * N1)) := by
    calc
      |âˆ‘ c : Idx,
          (-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c|
          <=
        âˆ‘ c : Idx,
          |(-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c| :=
            Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ _c : Idx,
        ((Fintype.card Idx : Real) *
            ((Fintype.card Idx : Real) * N1)) * (3 * N1) := by
            exact Finset.sum_le_sum fun c _ => hfirst_term c
      _ =
        (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) * N1)) * (3 * N1)) := by
            simp
  have hA2_combo (c : Idx) :
      |A2 d a b c + A2 d b a c - A2 d c a b| <= 3 * N2 := by
    have htri :
        |A2 d a b c + A2 d b a c - A2 d c a b| <=
          |A2 d a b c| + |A2 d b a c| + |A2 d c a b| := by
      calc
        |A2 d a b c + A2 d b a c - A2 d c a b|
            = |(A2 d a b c + A2 d b a c) + (-(A2 d c a b))| := by ring_nf
        _ <= |A2 d a b c + A2 d b a c| + |-(A2 d c a b)| := abs_add_le _ _
        _ <= (|A2 d a b c| + |A2 d b a c|) + |A2 d c a b| := by
              simpa [abs_neg] using
                add_le_add_right
                  (abs_add_le (A2 d a b c) (A2 d b a c)) |-(A2 d c a b)|
        _ = |A2 d a b c| + |A2 d b a c| + |A2 d c a b| := by ring
    have hi := hA2 d a b c
    have hj := hA2 d b a c
    have hk := hA2 d c a b
    linarith [htri, hi, hj, hk]
  have hsecond_term (c : Idx) :
      |U e c * (A2 d a b c + A2 d b a c - A2 d c a b)| <= 3 * N2 := by
    have hU_nonneg : 0 <= |U e c| := abs_nonneg _
    have hcombo_abs_nonneg :
        0 <= |A2 d a b c + A2 d b a c - A2 d c a b| := abs_nonneg _
    calc
      |U e c * (A2 d a b c + A2 d b a c - A2 d c a b)|
          = |U e c| * |A2 d a b c + A2 d b a c - A2 d c a b| := by
            rw [abs_mul]
      _ <= 1 * (3 * N2) := by
            nlinarith [hU e c, hA2_combo c, hU_nonneg, hcombo_abs_nonneg]
      _ = 3 * N2 := by ring
  have hsecond :
      |âˆ‘ c : Idx,
          U e c * (A2 d a b c + A2 d b a c - A2 d c a b)| <=
        (Fintype.card Idx : Real) * (3 * N2) := by
    calc
      |âˆ‘ c : Idx,
          U e c * (A2 d a b c + A2 d b a c - A2 d c a b)|
          <=
        âˆ‘ c : Idx,
          |U e c * (A2 d a b c + A2 d b a c - A2 d c a b)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ _c : Idx, 3 * N2 := by
            exact Finset.sum_le_sum fun c _ => hsecond_term c
      _ = (Fintype.card Idx : Real) * (3 * N2) := by simp
  have hquad :
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv cov frame hframe x d a b e =
        (âˆ‘ c : Idx,
          (-(âˆ‘ r : Idx, âˆ‘ q : Idx, U e r * U c q * A1 d r q)) * S a b c) +
        (âˆ‘ c : Idx,
          U e c * (A2 d a b c + A2 d b a c - A2 d c a b)) := by
    simp [Coordinates.lcDiffQuadRHS, U, A1, A2, S]
  rw [hquad]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Coarse finite-sum bound for the cubic RHS of the second covariant
Christoffel-difference formula.

The bound is intentionally non-sharp.  Its role is only to show that the cubic
coordinate expression is controlled by the schematic quantities
`|nabla_h g|`, `|nabla_h^2 g|`, and `|nabla_h^3 g|`, with constants depending on
the finite frame index set. -/
theorem lcDiffCubic_abs_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E 1 frame u)
    (x : M) (m d a b e : Idx) {N1 N2 N3 : Real}
    (hN1 : 0 <= N1) (hN2 : 0 <= N2) (hN3 : 0 <= N3)
    (hU : forall i j : Idx, |gInv x i j| <= 1)
    (hA1 : forall i j k : Idx,
      |Coordinates.metricCovDerivForMetricCompInFrame
        (I := I) g cov frame hframe x i j k| <= N1)
    (hA2 : forall i j k l : Idx,
      |Coordinates.metricCovDeriv2ForMetricCompInFrame
        (I := I) g cov frame hframe x i j k l| <= N2)
    (hA3 : forall i j k l r : Idx,
      |Coordinates.metricCovDeriv3ForMetricCompInFrame
        (I := I) g cov frame hframe x i j k l r| <= N3) :
    let n : Real := Fintype.card Idx
    let Q : Real := n * (n * N1)
    let R : Real := n * (n * (N2 + Q * N1 + Q * N1))
    |Coordinates.lcDiffQuadCubicRHS
        (I := I) g gInv cov frame hframe x m d a b e| <=
      n * (Q * (3 * N2) + R * (3 * N1)) +
        n * (3 * N3 + Q * (3 * N2)) := by
  classical
  let n : Real := Fintype.card Idx
  let Q : Real := n * (n * N1)
  let R : Real := n * (n * (N2 + Q * N1 + Q * N1))
  let U : Idx -> Idx -> Real := fun i j => gInv x i j
  let A1 : Idx -> Idx -> Idx -> Real := fun i j k =>
    Coordinates.metricCovDerivForMetricCompInFrame
      (I := I) g cov frame hframe x i j k
  let A2 : Idx -> Idx -> Idx -> Idx -> Real := fun i j k l =>
    Coordinates.metricCovDeriv2ForMetricCompInFrame
      (I := I) g cov frame hframe x i j k l
  let A3 : Idx -> Idx -> Idx -> Idx -> Idx -> Real := fun i j k l r =>
    Coordinates.metricCovDeriv3ForMetricCompInFrame
      (I := I) g cov frame hframe x i j k l r
  let S1 : Idx -> Idx -> Idx -> Real := fun i j k =>
    Coordinates.lcDiffSymMetricCovComp (I := I) g cov frame hframe x i j k
  let S2 : Idx -> Idx -> Idx -> Idx -> Real := fun i j k l =>
    Coordinates.lcDiffSymMetricCov2Comp (I := I) g cov frame hframe x i j k l
  let S3 : Idx -> Idx -> Idx -> Idx -> Idx -> Real := fun i j k l r =>
    Coordinates.lcDiffSymMetricCov3Comp (I := I) g cov frame hframe x i j k l r
  let IQ : Idx -> Idx -> Idx -> Real := fun i j k =>
    Coordinates.lcDiffInvQuad (I := I) g gInv cov frame hframe x i j k
  let IQC : Idx -> Idx -> Idx -> Idx -> Real := fun i j k l =>
    Coordinates.lcDiffInvQuadCovRHS (I := I) g gInv cov frame hframe x i j k l
  have hn_nonneg : 0 <= n := by
    dsimp [n]
    positivity
  have hQ_nonneg : 0 <= Q := by
    dsimp [Q]
    positivity
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    positivity
  have hS1 (i j k : Idx) : |S1 i j k| <= 3 * N1 := by
    have htri :
        |A1 i j k + A1 j i k - A1 k i j| <=
          |A1 i j k| + |A1 j i k| + |A1 k i j| := by
      calc
        |A1 i j k + A1 j i k - A1 k i j|
            = |(A1 i j k + A1 j i k) + (-(A1 k i j))| := by ring_nf
        _ <= |A1 i j k + A1 j i k| + |-(A1 k i j)| := abs_add_le _ _
        _ <= (|A1 i j k| + |A1 j i k|) + |A1 k i j| := by
              simpa [abs_neg] using
                add_le_add_right (abs_add_le (A1 i j k) (A1 j i k)) |-(A1 k i j)|
        _ = |A1 i j k| + |A1 j i k| + |A1 k i j| := by ring
    have hS_eq : S1 i j k = A1 i j k + A1 j i k - A1 k i j := by
      simp [S1, A1, Coordinates.lcDiffSymMetricCovComp]
    rw [hS_eq]
    linarith [htri, hA1 i j k, hA1 j i k, hA1 k i j]
  have hS2 (i j k l : Idx) : |S2 i j k l| <= 3 * N2 := by
    have htri :
        |A2 i j k l + A2 i k j l - A2 i l j k| <=
          |A2 i j k l| + |A2 i k j l| + |A2 i l j k| := by
      calc
        |A2 i j k l + A2 i k j l - A2 i l j k|
            = |(A2 i j k l + A2 i k j l) + (-(A2 i l j k))| := by ring_nf
        _ <= |A2 i j k l + A2 i k j l| + |-(A2 i l j k)| := abs_add_le _ _
        _ <= (|A2 i j k l| + |A2 i k j l|) + |A2 i l j k| := by
              simpa [abs_neg] using
                add_le_add_right (abs_add_le (A2 i j k l) (A2 i k j l)) |-(A2 i l j k)|
        _ = |A2 i j k l| + |A2 i k j l| + |A2 i l j k| := by ring
    have hS_eq : S2 i j k l = A2 i j k l + A2 i k j l - A2 i l j k := by
      simp [S2, A2, Coordinates.lcDiffSymMetricCov2Comp]
    rw [hS_eq]
    linarith [htri, hA2 i j k l, hA2 i k j l, hA2 i l j k]
  have hS3 (i j k l r : Idx) : |S3 i j k l r| <= 3 * N3 := by
    have htri :
        |A3 i j k l r + A3 i j l k r - A3 i j r k l| <=
          |A3 i j k l r| + |A3 i j l k r| + |A3 i j r k l| := by
      calc
        |A3 i j k l r + A3 i j l k r - A3 i j r k l|
            = |(A3 i j k l r + A3 i j l k r) + (-(A3 i j r k l))| := by ring_nf
        _ <= |A3 i j k l r + A3 i j l k r| + |-(A3 i j r k l)| := abs_add_le _ _
        _ <= (|A3 i j k l r| + |A3 i j l k r|) + |A3 i j r k l| := by
              simpa [abs_neg] using
                add_le_add_right (abs_add_le (A3 i j k l r) (A3 i j l k r))
                  |-(A3 i j r k l)|
        _ = |A3 i j k l r| + |A3 i j l k r| + |A3 i j r k l| := by ring
    have hS_eq : S3 i j k l r = A3 i j k l r + A3 i j l k r - A3 i j r k l := by
      simp [S3, A3, Coordinates.lcDiffSymMetricCov3Comp]
    rw [hS_eq]
    linarith [htri, hA3 i j k l r, hA3 i j l k r, hA3 i j r k l]
  have hprodA1 (dd ee cc rr qq : Idx) :
      |U ee rr * U cc qq * A1 dd rr qq| <= N1 := by
    have h1_nonneg : 0 <= |U ee rr| := abs_nonneg _
    have h2_nonneg : 0 <= |U cc qq| := abs_nonneg _
    have hA_nonneg : 0 <= |A1 dd rr qq| := abs_nonneg _
    have h12 : |U ee rr| * |U cc qq| <= 1 := by
      nlinarith [hU ee rr, hU cc qq, h1_nonneg, h2_nonneg]
    calc
      |U ee rr * U cc qq * A1 dd rr qq|
          = |U ee rr| * |U cc qq| * |A1 dd rr qq| := by rw [abs_mul, abs_mul]
      _ <= N1 := by nlinarith [h12, hA1 dd rr qq, hN1, hA_nonneg]
  have hIQ (dd ee cc : Idx) : |IQ dd ee cc| <= Q := by
    have hsum :
        |âˆ‘ r : Idx, âˆ‘ q : Idx, U ee r * U cc q * A1 dd r q| <= Q := by
      calc
        |âˆ‘ r : Idx, âˆ‘ q : Idx, U ee r * U cc q * A1 dd r q|
            <= âˆ‘ r : Idx, |âˆ‘ q : Idx, U ee r * U cc q * A1 dd r q| :=
              Finset.abs_sum_le_sum_abs _ _
        _ <= âˆ‘ r : Idx, âˆ‘ q : Idx, |U ee r * U cc q * A1 dd r q| := by
              exact Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _
        _ <= âˆ‘ _r : Idx, âˆ‘ _q : Idx, N1 := by
              refine Finset.sum_le_sum ?_
              intro r _
              refine Finset.sum_le_sum ?_
              intro q _
              exact hprodA1 dd ee cc r q
        _ = Q := by simp [Q, n]
    have hIQ_eq : IQ dd ee cc = -(âˆ‘ r : Idx, âˆ‘ q : Idx, U ee r * U cc q * A1 dd r q) := by
      simp [IQ, U, A1, Coordinates.lcDiffInvQuad]
    rw [hIQ_eq, abs_neg]
    exact hsum
  have hprodA2 (ee cc rr qq : Idx) :
      |U ee rr * U cc qq * A2 m d rr qq| <= N2 := by
    have h1_nonneg : 0 <= |U ee rr| := abs_nonneg _
    have h2_nonneg : 0 <= |U cc qq| := abs_nonneg _
    have hA_nonneg : 0 <= |A2 m d rr qq| := abs_nonneg _
    have h12 : |U ee rr| * |U cc qq| <= 1 := by
      nlinarith [hU ee rr, hU cc qq, h1_nonneg, h2_nonneg]
    calc
      |U ee rr * U cc qq * A2 m d rr qq|
          = |U ee rr| * |U cc qq| * |A2 m d rr qq| := by rw [abs_mul, abs_mul]
      _ <= N2 := by nlinarith [h12, hA2 m d rr qq, hN2, hA_nonneg]
  have hprodIQ (ee cc rr qq : Idx) :
      |U ee rr * IQ m cc qq * A1 d rr qq| <= Q * N1 := by
    have hU_nonneg : 0 <= |U ee rr| := abs_nonneg _
    have hIQ_nonneg : 0 <= |IQ m cc qq| := abs_nonneg _
    have hA_nonneg : 0 <= |A1 d rr qq| := abs_nonneg _
    have hU_IQ : |U ee rr| * |IQ m cc qq| <= Q := by
      calc
        |U ee rr| * |IQ m cc qq| <= 1 * Q :=
          mul_le_mul (hU ee rr) (hIQ m cc qq) hIQ_nonneg (by norm_num)
        _ = Q := by ring
    calc
      |U ee rr * IQ m cc qq * A1 d rr qq|
          = |U ee rr| * |IQ m cc qq| * |A1 d rr qq| := by rw [abs_mul, abs_mul]
      _ <= Q * N1 :=
          mul_le_mul hU_IQ (hA1 d rr qq) hA_nonneg hQ_nonneg
  have hprodIQ' (ee cc rr qq : Idx) :
      |IQ m ee rr * U cc qq * A1 d rr qq| <= Q * N1 := by
    have hIQ_nonneg : 0 <= |IQ m ee rr| := abs_nonneg _
    have hU_nonneg : 0 <= |U cc qq| := abs_nonneg _
    have hA_nonneg : 0 <= |A1 d rr qq| := abs_nonneg _
    have hIQ_U : |IQ m ee rr| * |U cc qq| <= Q := by
      calc
        |IQ m ee rr| * |U cc qq| <= Q * 1 :=
          mul_le_mul (hIQ m ee rr) (hU cc qq) hU_nonneg hQ_nonneg
        _ = Q := by ring
    calc
      |IQ m ee rr * U cc qq * A1 d rr qq|
          = |IQ m ee rr| * |U cc qq| * |A1 d rr qq| := by rw [abs_mul, abs_mul]
      _ <= Q * N1 :=
          mul_le_mul hIQ_U (hA1 d rr qq) hA_nonneg hQ_nonneg
  have hIQC (ee cc : Idx) : |IQC m d ee cc| <= R := by
    have hterm (r q : Idx) :
        |U ee r * U cc q * A2 m d r q +
          U ee r * IQ m cc q * A1 d r q +
          IQ m ee r * U cc q * A1 d r q| <=
          N2 + Q * N1 + Q * N1 := by
      have htri := abs_add_le
        (U ee r * U cc q * A2 m d r q + U ee r * IQ m cc q * A1 d r q)
        (IQ m ee r * U cc q * A1 d r q)
      have htri2 := abs_add_le
        (U ee r * U cc q * A2 m d r q)
        (U ee r * IQ m cc q * A1 d r q)
      linarith [htri, htri2, hprodA2 ee cc r q, hprodIQ ee cc r q,
        hprodIQ' ee cc r q]
    have hsum :
        |âˆ‘ r : Idx, âˆ‘ q : Idx,
          (U ee r * U cc q * A2 m d r q +
            U ee r * IQ m cc q * A1 d r q +
            IQ m ee r * U cc q * A1 d r q)| <= R := by
      calc
        |âˆ‘ r : Idx, âˆ‘ q : Idx,
          (U ee r * U cc q * A2 m d r q +
            U ee r * IQ m cc q * A1 d r q +
            IQ m ee r * U cc q * A1 d r q)|
            <= âˆ‘ r : Idx, |âˆ‘ q : Idx,
              (U ee r * U cc q * A2 m d r q +
                U ee r * IQ m cc q * A1 d r q +
                IQ m ee r * U cc q * A1 d r q)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ <= âˆ‘ r : Idx, âˆ‘ q : Idx,
              |U ee r * U cc q * A2 m d r q +
                U ee r * IQ m cc q * A1 d r q +
                IQ m ee r * U cc q * A1 d r q| := by
              exact Finset.sum_le_sum fun r _ => Finset.abs_sum_le_sum_abs _ _
        _ <= âˆ‘ _r : Idx, âˆ‘ _q : Idx, (N2 + Q * N1 + Q * N1) := by
              refine Finset.sum_le_sum ?_
              intro r _
              refine Finset.sum_le_sum ?_
              intro q _
              exact hterm r q
        _ = R := by
              simp [R, n]
              ring_nf
    have hIQC_eq :
        IQC m d ee cc =
          -(âˆ‘ r : Idx, âˆ‘ q : Idx,
            (U ee r * U cc q * A2 m d r q +
              U ee r * IQ m cc q * A1 d r q +
              IQ m ee r * U cc q * A1 d r q)) := by
      simp [IQC, IQ, U, A1, A2, Coordinates.lcDiffInvQuadCovRHS]
    rw [hIQC_eq, abs_neg]
    exact hsum
  have hfirst_term (c : Idx) :
      |IQ d e c * S2 m a b c + IQC m d e c * S1 a b c| <=
        Q * (3 * N2) + R * (3 * N1) := by
    have hA : |IQ d e c * S2 m a b c| <= Q * (3 * N2) := by
      calc
        |IQ d e c * S2 m a b c| = |IQ d e c| * |S2 m a b c| := by rw [abs_mul]
        _ <= Q * (3 * N2) :=
          mul_le_mul (hIQ d e c) (hS2 m a b c) (abs_nonneg _) hQ_nonneg
    have hB : |IQC m d e c * S1 a b c| <= R * (3 * N1) := by
      calc
        |IQC m d e c * S1 a b c| = |IQC m d e c| * |S1 a b c| := by rw [abs_mul]
        _ <= R * (3 * N1) :=
          mul_le_mul (hIQC e c) (hS1 a b c) (abs_nonneg _) hR_nonneg
    exact (abs_add_le _ _).trans (add_le_add hA hB)
  have hfirst :
      |âˆ‘ c : Idx, (IQ d e c * S2 m a b c + IQC m d e c * S1 a b c)| <=
        n * (Q * (3 * N2) + R * (3 * N1)) := by
    calc
      |âˆ‘ c : Idx, (IQ d e c * S2 m a b c + IQC m d e c * S1 a b c)|
          <= âˆ‘ c : Idx, |IQ d e c * S2 m a b c + IQC m d e c * S1 a b c| :=
            Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ _c : Idx, (Q * (3 * N2) + R * (3 * N1)) := by
            exact Finset.sum_le_sum fun c _ => hfirst_term c
      _ = n * (Q * (3 * N2) + R * (3 * N1)) := by
            simp [n]
            ring_nf
  have hlinear_term (c : Idx) :
      |U e c * S3 m d a b c + IQ m e c * S2 d a b c| <=
        3 * N3 + Q * (3 * N2) := by
    have hA : |U e c * S3 m d a b c| <= 3 * N3 := by
      calc
        |U e c * S3 m d a b c| = |U e c| * |S3 m d a b c| := by rw [abs_mul]
        _ <= 1 * (3 * N3) := by
              have hU_nonneg : 0 <= |U e c| := abs_nonneg _
              have hS_nonneg : 0 <= |S3 m d a b c| := abs_nonneg _
              nlinarith [hU e c, hS3 m d a b c, hU_nonneg, hS_nonneg]
        _ = 3 * N3 := by ring
    have hB : |IQ m e c * S2 d a b c| <= Q * (3 * N2) := by
      calc
        |IQ m e c * S2 d a b c| = |IQ m e c| * |S2 d a b c| := by rw [abs_mul]
        _ <= Q * (3 * N2) :=
          mul_le_mul (hIQ m e c) (hS2 d a b c) (abs_nonneg _) hQ_nonneg
    exact (abs_add_le _ _).trans (add_le_add hA hB)
  have hlinear :
      |âˆ‘ c : Idx, (U e c * S3 m d a b c + IQ m e c * S2 d a b c)| <=
        n * (3 * N3 + Q * (3 * N2)) := by
    calc
      |âˆ‘ c : Idx, (U e c * S3 m d a b c + IQ m e c * S2 d a b c)|
          <= âˆ‘ c : Idx, |U e c * S3 m d a b c + IQ m e c * S2 d a b c| :=
            Finset.abs_sum_le_sum_abs _ _
      _ <= âˆ‘ _c : Idx, (3 * N3 + Q * (3 * N2)) := by
            exact Finset.sum_le_sum fun c _ => hlinear_term c
      _ = n * (3 * N3 + Q * (3 * N2)) := by
            simp [n]
            ring_nf
  have hcubic :
      Coordinates.lcDiffQuadCubicRHS
        (I := I) g gInv cov frame hframe x m d a b e =
        (âˆ‘ c : Idx, (IQ d e c * S2 m a b c + IQC m d e c * S1 a b c)) +
        (âˆ‘ c : Idx, (U e c * S3 m d a b c + IQ m e c * S2 d a b c)) := by
    simp [Coordinates.lcDiffQuadCubicRHS, Coordinates.lcDiffLinear2CubicRHS,
      IQ, IQC, U, S1, S2, S3]
  rw [hcubic]
  exact (abs_add_le _ _).trans (add_le_add hfirst hlinear)

/-- First metric-derivative local-frame components are bounded by the
invariant `|nabla_h g|_g` norm. -/
theorem metricCov1_comp_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (d a b : Idx) :
    |Coordinates.metricCovDerivForMetricCompInFrame
        (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b| <=
      metricCovDerivNormWith (I := I) 1 g h g x := by
  have hcomp :=
    metricCovComp_le
      (I := I) 1 g h g (hframe.toBasisAt hx) hinvBasis
      (Fin.cons d (fun q : Fin 2 => if q = 0 then a else b) :
        Fin 3 -> Idx)
  have hcoord :=
    metricCov1_coord (I := I) g h frame hframe hu hx d a b
  rw [<- hcoord]
  exact hcomp

/-- Second metric-derivative local-frame components are bounded by the
invariant `|nabla_h^2 g|_g` norm. -/
theorem metricCov2_comp_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (d a b c : Idx) :
    |Coordinates.metricCovDeriv2ForMetricCompInFrame
        (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b c| <=
      metricCovDerivNormWith (I := I) 2 g h g x := by
  have hcomp :=
    metricCovComp_le
      (I := I) 2 g h g (hframe.toBasisAt hx) hinvBasis
      (Fin.cons d (Coordinates.slots3 a b c) : Fin 4 -> Idx)
  have hcoord :=
    metricCov2_coord (I := I) g h frame hframe hu hx d a b c
  rw [<- hcoord]
  exact hcomp

/-- Third metric-derivative local-frame components are bounded by the
invariant `|nabla_h^3 g|_g` norm. -/
theorem metricCov3_comp_le
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (m d a b c : Idx) :
    |Coordinates.metricCovDeriv3ForMetricCompInFrame
        (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x m d a b c| <=
      metricCovDerivNormWith (I := I) 3 g h g x := by
  have hcomp :=
    metricCovComp_le
      (I := I) 3 g h g (hframe.toBasisAt hx) hinvBasis
      (Fin.cons m (Coordinates.slots4 d a b c) : Fin 5 -> Idx)
  have hcoord :=
    metricCov3_coord (I := I) g h frame hframe hu hx m d a b c
  rw [<- hcoord]
  exact hcomp

/-- Norm form of `lcDiffCubic_abs_le`: in a `g`-orthonormal local frame, the
second covariant derivative cubic RHS is controlled by the invariant norms of
`nabla_h g`, `nabla_h^2 g`, and `nabla_h^3 g`. -/
theorem lcDiffCubic_abs_le_norms_local
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (m d a b e : Idx) :
    let n : Real := Fintype.card Idx
    let N1 : Real := metricCovDerivNormWith (I := I) 1 g h g x
    let N2 : Real := metricCovDerivNormWith (I := I) 2 g h g x
    let N3 : Real := metricCovDerivNormWith (I := I) 3 g h g x
    let Q : Real := n * (n * N1)
    let R : Real := n * (n * (N2 + Q * N1 + Q * N1))
    |Coordinates.lcDiffQuadCubicRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x m d a b e| <=
      n * (Q * (3 * N2) + R * (3 * N1)) +
        n * (3 * N3 + Q * (3 * N2)) := by
  have hU : forall i j : Idx, |gInv x i j| <= 1 := by
    intro i j
    rw [gInv_eq_identity_at_local (I := I) gInv frame hframe hx hinvX hinvBasis i j]
    by_cases hij : i = j
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
  exact
    lcDiffCubic_abs_le
      (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      frame (localFrameOneOfInf (I := I) frame hframe) x m d a b e
      (by
        dsimp [metricCovDerivNormWith]
        exact Real.sqrt_nonneg _)
      (by
        dsimp [metricCovDerivNormWith]
        exact Real.sqrt_nonneg _)
      (by
        dsimp [metricCovDerivNormWith]
        exact Real.sqrt_nonneg _)
      hU
      (fun i j k =>
        metricCov1_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k)
      (fun i j k l =>
        metricCov2_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k l)
      (fun i j k l r =>
        metricCov3_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k l r)

/-- Norm form of `lcDiffQuad_abs_le`: in a `g`-orthonormal local frame, the
substituted differentiated Christoffel RHS is controlled by
`|nabla_h g|_g` and `|nabla_h^2 g|_g`. -/
theorem lcDiffQuad_abs_le_norms
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (d a b e : Idx) :
    |Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b e| <=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x) := by
  have hU : forall i j : Idx, |gInv x i j| <= 1 := by
    intro i j
    rw [gInv_eq_identity_at (I := I) gInv frame hframe hx hinv hinvBasis i j]
    by_cases hij : i = j
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
  exact
    lcDiffQuad_abs_le
      (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      frame (localFrameOneOfInf (I := I) frame hframe) x d a b e
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hU
      (fun i j k =>
        metricCov1_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k)
      (fun i j k l =>
        metricCov2_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k l)

/-- Local-inverse version of `lcDiffQuad_abs_le_norms`. -/
theorem lcDiffQuad_abs_le_norms_local
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    (g h : SmoothRiemannianMetric I M)
    (gInv : M -> Idx -> Idx -> Real)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (d a b e : Idx) :
    |Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame (localFrameOneOfInf (I := I) frame hframe) x d a b e| <=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x) := by
  have hU : forall i j : Idx, |gInv x i j| <= 1 := by
    intro i j
    rw [gInv_eq_identity_at_local (I := I) gInv frame hframe hx hinvX hinvBasis i j]
    by_cases hij : i = j
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
    Â· simp [Tensor0SBundle.identityInvMetric, Tensor0SBundle.diagonalInvMetric, hij]
  exact
    lcDiffQuad_abs_le
      (I := I) g gInv (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      frame (localFrameOneOfInf (I := I) frame hframe) x d a b e
      (by
        dsimp [metricCovDerivNormWith]
        exact Real.sqrt_nonneg _)
      (by
        dsimp [metricCovDerivNormWith]
        exact Real.sqrt_nonneg _)
      hU
      (fun i j k =>
        metricCov1_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k)
      (fun i j k l =>
        metricCov2_comp_le (I := I) g h frame hframe hu hx hinvBasis i j k l)

/-- Local-frame norm estimate for the first `h`-covariant derivative of
`Gamma_g - Gamma_h`.

This is the pointwise norm packaging of the differentiated Christoffel formula:
with a `g`-orthonormal local frame and the local differentiability data needed
by `lcDiffDeriv_eq_quad`, the realized tensor `D1` is controlled by
`|nabla_h g|_g` and `|nabla_h^2 g|_g`. -/
theorem connDiffOne_local_norm
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Idx -> Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (hX : âˆ€ d : Idx, X d x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ e j : Idx,
      (fun y : M => Î± e y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv frame)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hD_mdiff : âˆ€ a b e : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
          y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let B : Real :=
    (Fintype.card Idx : Real) *
        (((Fintype.card Idx : Real) *
            ((Fintype.card Idx : Real) *
              metricCovDerivNormWith (I := I) 1 g h g x)) *
          (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
      (Fintype.card Idx : Real) *
        (3 * metricCovDerivNormWith (I := I) 2 g h g x)
  have hB_nonneg : 0 <= B := by
    have hcard : 0 <= (Fintype.card Idx : Real) := by
      exact_mod_cast Nat.zero_le (Fintype.card Idx)
    have hN1 : 0 <= metricCovDerivNormWith (I := I) 1 g h g x := by
      dsimp [metricCovDerivNormWith]
      exact Real.sqrt_nonneg _
    have hN2 : 0 <= metricCovDerivNormWith (I := I) 2 g h g x := by
      dsimp [metricCovDerivNormWith]
      exact Real.sqrt_nonneg _
    dsimp [B]
    exact add_nonneg
      (mul_nonneg hcard
        (mul_nonneg
          (mul_nonneg hcard (mul_nonneg hcard hN1))
          (mul_nonneg (by norm_num : (0 : Real) <= 3) hN1)))
      (mul_nonneg hcard
        (mul_nonneg (by norm_num : (0 : Real) <= 3) hN2))
  have hnorm :=
    Tensor0SBundle.sqrt_normRS_le_comps
      (I := I) g x 1 3 (hframe.toBasisAt hx) hinvBasis (D1 x)
      hB_nonneg
      (fun upper lower => ?_)
  Â· simpa [connDiffDerivNorm, B] using hnorm
  let e : Idx := upper 0
  let d : Idx := lower 0
  let a : Idx := lower 1
  let b : Idx := lower 2
  have hupper : upper = Coordinates.upperIdx1 e := by
    funext q
    fin_cases q
    simp [e, Coordinates.upperIdx1]
  have hlower : lower = Coordinates.slots3 d a b := by
    funext q
    fin_cases q <;> simp [d, a, b, Coordinates.slots3]
  let comp : Real :=
    Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
      (D1 x) upper lower
  have hcomp_le_two : |comp| <= |(2 : Real) * comp| := by
    calc
      |comp| = (1 : Real) * |comp| := by ring
      _ <= |(2 : Real)| * |comp| :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : Real) <= |(2 : Real)|)
          (abs_nonneg comp)
      _ = |(2 : Real) * comp| := by
        rw [abs_mul]
  have hquad :
      |(2 : Real) * comp| <= B := by
    have hquad_eq :=
      connDiffOne_frameInf_quad
        (I := I) hD1 (X d) Z (Î± e) frame hframe hu hx gInv d a b e
        (hX d) hZ (hpair e) hinv (hD_mdiff a b e)
        hginv_mdiff hmetric_mdiff hA_mdiff
    have hRHS :=
      lcDiffQuad_abs_le_norms
        (I := I) g h gInv frame hframe hu hx hinv hinvBasis d a b e
    have hcomp_eq :
        comp =
          Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
            (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) := by
      dsimp [comp]
      rw [hupper, hlower]
    rw [hcomp_eq]
    rw [hquad_eq]
    simpa [B] using hRHS
  simpa [comp] using le_trans hcomp_le_two hquad

/-- Local-inverse version of `connDiffOne_local_norm`. -/
theorem connDiffOne_local_norm_local
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx] {u : Set M}
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Z : Idx -> ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (Î± : Idx -> Tensor0SBundle.Tensor0SField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u)
    (hu : IsOpen u) {x : M} (hx : x âˆˆ u)
    (gInv : M -> Idx -> Idx -> Real)
    (hX : âˆ€ d : Idx, X d x = frame d x)
    (hZ : âˆ€ j : Idx,
      (fun y : M => Z j y) =á¶ [nhds x] fun y : M => frame j y)
    (hpair : âˆ€ e j : Idx,
      (fun y : M => Î± e y (fun _ : Fin 1 => Z j y)) =á¶ [nhds x]
        fun _ : M => if j = e then (1 : Real) else 0)
    (hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0))
    (hinvLeftN : forall i j : Idx,
      (fun y : M => âˆ‘ k : Idx,
          gInv y i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =á¶ [nhds x]
        fun _ : M => if i = j then 1 else 0)
    (hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hD_mdiff : âˆ€ a b e : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Coordinates.lcDiffCompInFrame
          (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
          y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g frame y i j) x)
    (hA_mdiff : âˆ€ i j k : Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let B : Real :=
    (Fintype.card Idx : Real) *
        (((Fintype.card Idx : Real) *
            ((Fintype.card Idx : Real) *
              metricCovDerivNormWith (I := I) 1 g h g x)) *
          (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
      (Fintype.card Idx : Real) *
        (3 * metricCovDerivNormWith (I := I) 2 g h g x)
  have hB_nonneg : 0 <= B := by
    have hcard : 0 <= (Fintype.card Idx : Real) := by
      exact_mod_cast Nat.zero_le (Fintype.card Idx)
    have hN1 : 0 <= metricCovDerivNormWith (I := I) 1 g h g x := by
      dsimp [metricCovDerivNormWith]
      exact Real.sqrt_nonneg _
    have hN2 : 0 <= metricCovDerivNormWith (I := I) 2 g h g x := by
      dsimp [metricCovDerivNormWith]
      exact Real.sqrt_nonneg _
    dsimp [B]
    exact add_nonneg
      (mul_nonneg hcard
        (mul_nonneg
          (mul_nonneg hcard (mul_nonneg hcard hN1))
          (mul_nonneg (by norm_num : (0 : Real) <= 3) hN1)))
      (mul_nonneg hcard
        (mul_nonneg (by norm_num : (0 : Real) <= 3) hN2))
  have hnorm :=
    Tensor0SBundle.sqrt_normRS_le_comps
      (I := I) g x 1 3 (hframe.toBasisAt hx) hinvBasis (D1 x)
      hB_nonneg
      (fun upper lower => ?_)
  Â· simpa [connDiffDerivNorm, B] using hnorm
  let e : Idx := upper 0
  let d : Idx := lower 0
  let a : Idx := lower 1
  let b : Idx := lower 2
  have hupper : upper = Coordinates.upperIdx1 e := by
    funext q
    fin_cases q
    simp [e, Coordinates.upperIdx1]
  have hlower : lower = Coordinates.slots3 d a b := by
    funext q
    fin_cases q <;> simp [d, a, b, Coordinates.slots3]
  let comp : Real :=
    Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
      (D1 x) upper lower
  have hcomp_le_two : |comp| <= |(2 : Real) * comp| := by
    calc
      |comp| = (1 : Real) * |comp| := by ring
      _ <= |(2 : Real)| * |comp| :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : Real) <= |(2 : Real)|)
          (abs_nonneg comp)
      _ = |(2 : Real) * comp| := by
        rw [abs_mul]
  have hquad :
      |(2 : Real) * comp| <= B := by
    have hquad_eq :=
      connDiffOne_frameInf_quad_local
        (I := I) hD1 (X d) Z (Î± e) frame hframe hu hx gInv d a b e
        (hX d) hZ (hpair e) hinvX hinvLeftN (hD_mdiff a b e)
        hginv_mdiff hmetric_mdiff hA_mdiff
    have hRHS :=
      lcDiffQuad_abs_le_norms_local
        (I := I) g h gInv frame hframe hu hx hinvX hinvBasis d a b e
    have hcomp_eq :
        comp =
          Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
            (D1 x) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) := by
      dsimp [comp]
      rw [hupper, hlower]
    rw [hcomp_eq]
    rw [hquad_eq]
    simpa [B] using hRHS
  simpa [comp] using le_trans hcomp_le_two hquad

set_option backward.isDefEq.respectTransparency false in
/-- Trivialization-frame version of `connDiffOne_local_norm`.

This removes the arbitrary vector-section and coframe-extension hypotheses from
the local norm estimate by choosing the smooth extensions supplied by
`Coordinates.existsTrivFrameCoframePair`.  The remaining assumptions are the
actual local metric inputs: inverse components, center orthonormality, and the
scalar differentiability witnesses needed to differentiate the Christoffel
formula. -/
theorem connDiffOne_trivNorm
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (basisE : Module.Basis Idx Real E) {x : M}
    (gInv : M -> Idx -> Idx -> Real)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv
        (fun i y =>
          (trivializationAt E (TangentSpace I : M -> Type _) x).localFrame
            basisE i y))
    (hinvBasis :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hx : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hD_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      âˆ€ a b e : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M => Coordinates.lcDiffCompInFrame
            (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
            y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      âˆ€ i j : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M =>
            Coordinates.metricCompForMetricInFrame
              (I := I) g frame y i j) x)
    (hA_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      âˆ€ i j k : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M =>
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  have hu : IsOpen u := eâ‚€.open_baseSet
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  obtain âŸ¨Z, Î¸, hZ, _hÎ¸, hpairâŸ© :=
    Coordinates.existsTrivFrameCoframePair (J := I) (N := M) x basisE
  have hX : âˆ€ d : Idx, Z d x = frame d x := by
    intro d
    exact (hZ d).self_of_nhds
  exact
    connDiffOne_local_norm
      (I := I) hD1 Z Z Î¸ frame hframe hu hx gInv hX hZ hpair
      (by
        simpa [frame, eâ‚€] using hinv)
      (by
        simpa [frame, u, hframe, hx, eâ‚€] using hinvBasis)
      (by
        simpa [frame, u, hframe, eâ‚€] using hD_mdiff)
      hginv_mdiff
      (by
        simpa [frame, eâ‚€] using hmetric_mdiff)
      (by
        simpa [frame, u, hframe, eâ‚€] using hA_mdiff)

/-- Local-inverse trivialization-frame version of `connDiffOne_local_norm`. -/
theorem connDiffOne_trivNorm_local
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (basisE : Module.Basis Idx Real E) {x : M}
    (gInv : M -> Idx -> Idx -> Real)
    (hinvX :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      forall i j : Idx,
        (âˆ‘ k : Idx, gInv x i k *
            Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
            (if i = j then 1 else 0) âˆ§
          (âˆ‘ k : Idx,
            Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
              gInv x k j) =
            (if i = j then 1 else 0))
    (hinvLeftN :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      forall i j : Idx,
        (fun y : M => âˆ‘ k : Idx,
            gInv y i k *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y k j) =á¶ [nhds x]
          fun _ : M => if i = j then 1 else 0)
    (hinvBasis :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hx : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hD_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      âˆ€ a b e : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M => Coordinates.lcDiffCompInFrame
            (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
            y a b e) x)
    (hginv_mdiff : âˆ€ i j : Idx,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) x)
    (hmetric_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      âˆ€ i j : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M =>
            Coordinates.metricCompForMetricInFrame
              (I := I) g frame y i j) x)
    (hA_mdiff :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      âˆ€ i j k : Idx,
        MDifferentiableAt I ð“˜(Real, Real)
          (fun y : M =>
            Coordinates.metricCovDerivForMetricCompInFrame
              (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  have hu : IsOpen u := eâ‚€.open_baseSet
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  obtain âŸ¨Z, Î¸, hZ, _hÎ¸, hpairâŸ© :=
    Coordinates.existsTrivFrameCoframePair (J := I) (N := M) x basisE
  have hX : âˆ€ d : Idx, Z d x = frame d x := by
    intro d
    exact (hZ d).self_of_nhds
  exact
    connDiffOne_local_norm_local
      (I := I) hD1 Z Z Î¸ frame hframe hu hx gInv hX hZ hpair
      (by
        simpa [frame, eâ‚€] using hinvX)
      (by
        simpa [frame, eâ‚€] using hinvLeftN)
      (by
        simpa [frame, u, hframe, hx, eâ‚€] using hinvBasis)
      (by
        simpa [frame, u, hframe, eâ‚€] using hD_mdiff)
      hginv_mdiff
      (by
        simpa [frame, eâ‚€] using hmetric_mdiff)
      (by
        simpa [frame, u, hframe, eâ‚€] using hA_mdiff)

/-- In a fixed tangent trivialization frame, the scalar components of
`Gamma_g - Gamma_h` are differentiable.  This is just the difference of the
two checked Levi-Civita Christoffel coefficient smoothness theorems. -/
theorem lcDiffComp_triv_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (a b eIdx : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun i y => eâ‚€.localFrame basisE i y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M => Coordinates.lcDiffCompInFrame
        (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
        y a b eIdx) x := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  have hx : x âˆˆ eâ‚€.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  have hg :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE g hx a b eIdx
  have hh :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE h hx a b eIdx
  have hdiff :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y)) -
            eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y))) x :=
    hg.sub hh
  have htarget :
      (fun y : M => Coordinates.lcDiffCompInFrame
        (I := I) g h frame (localFrameOneOfInf (I := I) frame hframe)
        y a b eIdx) =á¶ [nhds x]
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y)) -
            eâ‚€.localFrame_coeff I basisE eIdx y
              ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
                  (eâ‚€.localFrame basisE b) y)
                (eâ‚€.localFrame basisE a y))) := by
    filter_upwards [eâ‚€.open_baseSet.mem_nhds hx] with y hy
    let hframe1 := localFrameOneOfInf (I := I) frame hframe
    have hyu : y âˆˆ u := by
      simpa [u] using hy
    have hmdiff : MDiffAt (T% (frame b)) y := by
      exact (hframe.contMDiffAt eâ‚€.open_baseSet hyu b).mdifferentiableAt
        (by simp : (âˆž : WithTop â„•âˆž) â‰  0)
    change Coordinates.christoffelSymbolDifferenceInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        frame hframe1 y a b eIdx =
      eâ‚€.localFrame_coeff I basisE eIdx y
          ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
              (eâ‚€.localFrame basisE b) y)
            (eâ‚€.localFrame basisE a y)) -
        eâ‚€.localFrame_coeff I basisE eIdx y
          ((LeviCivita.leviCivitaConnectionOfMetric (I := I) h
              (eâ‚€.localFrame basisE b) y)
            (eâ‚€.localFrame basisE a y))
    rw [Coordinates.christoffelSymbolDifferenceInFrame_eq_sub
      (I := I)
      (cov := LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
      (cov' := LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (frame := frame) (hframe := hframe1)
      (x := y) (i := a) (j := b) (k := eIdx) hmdiff]
    have hbasis : hframe1.toBasisAt hyu = eâ‚€.basisAt basisE hy := by
      ext j
      simp [frame, IsLocalFrameOn.toBasisAt,
        Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy]
    simp [Coordinates.christoffelSymbolInFrame, frame,
      IsLocalFrameOn.coeff, hyu, hy, Bundle.Trivialization.localFrame_coeff,
      hbasis]
  exact (hdiff.congr_of_eventuallyEq htarget).mdifferentiableAt (by simp)

/-- Levi-Civita Christoffel coefficients in a fixed tangent trivialization frame
are smooth when written through `christoffelSymbolInFrame`. -/
theorem lcChrist_triv_contMDiffAt
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (i j k : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun a y => eâ‚€.localFrame basisE a y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
    ContMDiffAt I ð“˜(Real, Real) âˆž
      (fun y : M => Coordinates.christoffelSymbolInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun a y => eâ‚€.localFrame basisE a y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  let hframe1 := localFrameOneOfInf (I := I) frame hframe
  have hx : x âˆˆ eâ‚€.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  have hraw :=
    LeviCivita.lc_christoffel_contMDiffAt
      (I := I) eâ‚€ basisE g hx i j k
  have heq :
      (fun y : M => Coordinates.christoffelSymbolInFrame
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
        frame hframe1 y i j k) =á¶ [nhds x]
        (fun y : M =>
          eâ‚€.localFrame_coeff I basisE k y
            ((LeviCivita.leviCivitaConnectionOfMetric (I := I) g
                (eâ‚€.localFrame basisE j) y)
              (eâ‚€.localFrame basisE i y))) := by
    filter_upwards [eâ‚€.open_baseSet.mem_nhds hx] with y hy
    have hyu : y âˆˆ u := by
      simpa [u] using hy
    have hbasis : hframe1.toBasisAt hyu = eâ‚€.basisAt basisE hy := by
      ext q
      simp [frame, IsLocalFrameOn.toBasisAt,
        Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy]
    simp [Coordinates.christoffelSymbolInFrame, frame,
      IsLocalFrameOn.coeff, hyu, hy, Bundle.Trivialization.localFrame_coeff,
      hbasis]
  exact hraw.congr_of_eventuallyEq heq.symm

/-- First metric-covariant-derivative components in a fixed tangent
trivialization frame are differentiable. -/
theorem metricCov_triv_mdiff
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g h : SmoothRiemannianMetric I M)
    (basisE : Module.Basis Idx Real E) {x : M} (i j k : Idx) :
    let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
    let frame : Idx -> (y : M) -> TangentSpace I y :=
      fun a y => eâ‚€.localFrame basisE a y
    let u : Set M := eâ‚€.baseSet
    let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
      eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
    MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M =>
        Coordinates.metricCovDerivForMetricCompInFrame
          (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
          frame (localFrameOneOfInf (I := I) frame hframe) y i j k) x := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun a y => eâ‚€.localFrame basisE a y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  let hframe1 := localFrameOneOfInf (I := I) frame hframe
  have hx : x âˆˆ eâ‚€.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  have hxi : ContMDiffAt I (I.prod ð“˜(Real, E)) âˆž (T% (frame i)) x :=
    hframe.contMDiffAt eâ‚€.open_baseSet (by simpa [u] using hx) i
  have hmetric (a b : Idx) :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame (I := I) g frame y a b) x := by
    simpa [frame] using
      LeviCivita.localFrame_metricComp_contMDiffAt
        (I := I) eâ‚€ basisE g hx a b
  have hderiv :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          extDerivFun (I := I)
            (fun q : M =>
              Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
            y (frame i y)) x :=
    extDerivFun_apply_contMDiffAt_of_section
      (I := I)
      (f := fun q : M =>
        Coordinates.metricCompForMetricInFrame (I := I) g frame q j k)
      (X := frame i) (hmetric j k) hxi
  have hsum1 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i j p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y p k) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_triv_contMDiffAt
        (I := I) h basisE (x := x) i j p).mul (hmetric p k)
  have hsum2 :
      ContMDiffAt I ð“˜(Real, Real) âˆž
        (fun y : M =>
          âˆ‘ p : Idx,
            Coordinates.christoffelSymbolInFrame
                (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
                frame hframe1 y i k p *
              Coordinates.metricCompForMetricInFrame (I := I) g frame y j p) x := by
    refine ContMDiffAt.sum fun p _ => ?_
    exact
      (lcChrist_triv_contMDiffAt
        (I := I) h basisE (x := x) i k p).mul (hmetric j p)
  have htotal := (hderiv.sub hsum1).sub hsum2
  exact (by
    simpa [Coordinates.metricCovDerivForMetricCompInFrame, hframe1] using
      htotal.mdifferentiableAt (by simp))

/-- In an orthonormal basis for `g`, the identity matrix is the inverse metric
matrix.  This local helper avoids importing curvature trace infrastructure just
to build the inverse-metric hypothesis used by the F3 connection-difference
norm estimate. -/
theorem metricInverseInBasis_identity_of_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) {x : M}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hON : forall i j : Idx,
      g.inner x (basis i) (basis j) = if i = j then 1 else 0) :
    Tensor0SBundle.MetricInverseInBasis
      (I := I) g x basis
      (Tensor0SBundle.identityInvMetric (Idx := Idx)) := by
  classical
  intro i j
  constructor <;>
    simp [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric, hON]

/-- Trivialization-frame version of `connDiffOne_trivNorm_local` using the
canonical inverse coefficients of the fixed local-frame Gram matrix. -/
theorem connDiffOne_trivInv
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (basisE : Module.Basis Idx Real E) {x : M}
    (hinvBasis :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hx : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  refine
    connDiffOne_trivNorm_local
      (I := I) (x := x) (gInv := gInv) hD1 basisE ?_ ?_ ?_ ?_ ?_ ?_ ?_
  Â· dsimp
    intro a b
    constructor
    Â· simpa [gInv, frame, eâ‚€] using
        LeviCivita.localInvMetricCoeff_metricComp_left_inv
          (I := I) eâ‚€ basisE g hx a b
    Â· simpa [gInv, frame, eâ‚€] using
        LeviCivita.localInvMetricCoeff_metricComp_right_inv
          (I := I) eâ‚€ basisE g hx a b
  Â· dsimp
    intro a b
    simpa [gInv, frame, eâ‚€] using
      LeviCivita.localInvMetricCoeff_metricComp_left_inv_eventually
        (I := I) eâ‚€ basisE g hx a b
  Â· simpa [frame, u, hframe, hx, eâ‚€] using hinvBasis
  Â· dsimp
    intro i j k
    simpa [frame, u, hframe, eâ‚€] using
      lcDiffComp_triv_mdiff
        (I := I) (g := g) (h := h) (basisE := basisE) (x := x) i j k
  Â· intro a b
    exact
      (LeviCivita.localInvMetricCoeff_contMDiffAt
        (I := I) eâ‚€ basisE g hx a b).mdifferentiableAt (by simp)
  Â· dsimp
    intro a b
    simpa [frame, eâ‚€] using
      LeviCivita.localFrame_metricComp_mdiff (I := I) eâ‚€ basisE g hx a b
  Â· dsimp
    intro i j k
    simpa [frame, u, hframe, eâ‚€] using
      metricCov_triv_mdiff
        (I := I) (g := g) (h := h) (basisE := basisE) (x := x) i j k

/-- Trivialization-frame version of `connDiffOne_trivInv` using a pointwise
`g`-orthonormality hypothesis for the centered frame.  This removes the
inverse-metric matrix from the caller; constructing such a frame is the
separate local orthonormal-frame producer needed for the public
`ConnDiffEpsBoundOn ... 1` endpoint. -/
theorem connDiffOne_trivON
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (basisE : Module.Basis Idx Real E) {x : M}
    (hON :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hx : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      forall i j : Idx,
        g.inner x (hframe.toBasisAt hx i) (hframe.toBasisAt hx j) =
          if i = j then 1 else 0) :
    let B : Real :=
      (Fintype.card Idx : Real) *
          (((Fintype.card Idx : Real) *
              ((Fintype.card Idx : Real) *
                metricCovDerivNormWith (I := I) 1 g h g x)) *
            (3 * metricCovDerivNormWith (I := I) 1 g h g x)) +
        (Fintype.card Idx : Real) *
          (3 * metricCovDerivNormWith (I := I) 2 g h g x)
    connDiffDerivNorm (I := I) g 1 D1 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal
      (I := I) g (hframe.toBasisAt hx) (by
        simpa [eâ‚€, frame, u, hframe, hx] using hON)
  exact
    connDiffOne_trivInv
      (I := I) hD1 basisE (x := x) (by
        simpa [eâ‚€, frame, u, hframe, hx] using hinvBasis)

set_option backward.isDefEq.respectTransparency false in
/-- Trivialization-frame local norm estimate for the second `h`-covariant
derivative of `Gamma_g - Gamma_h`.

This is the `k = 2` analogue of `connDiffOne_trivON`, using the checked cubic
coordinate reassembly `connDiffTwo_trivFrame_cubic`. -/
theorem connDiffTwo_trivON
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {g h : SmoothRiemannianMetric I M}
    {D2 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 4}
    (hD2 : ConnDiffDerivRealizes (I := I) g h 2 D2)
    (basisE : Module.Basis Idx Real E) {x : M}
    (hON :
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hx : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      forall i j : Idx,
        g.inner x (hframe.toBasisAt hx i) (hframe.toBasisAt hx j) =
          if i = j then 1 else 0) :
    let n : Real := Fintype.card Idx
    let N1 : Real := metricCovDerivNormWith (I := I) 1 g h g x
    let N2 : Real := metricCovDerivNormWith (I := I) 2 g h g x
    let N3 : Real := metricCovDerivNormWith (I := I) 3 g h g x
    let Q : Real := n * (n * N1)
    let R : Real := n * (n * (N2 + Q * N1 + Q * N1))
    let B : Real := n * (Q * (3 * N2) + R * (3 * N1)) +
      n * (3 * N3 + Q * (3 * N2))
    connDiffDerivNorm (I := I) g 2 D2 x <=
      Real.sqrt
        ((Fintype.card (Fin 1 -> Idx) : Real) *
          ((Fintype.card (Fin 4 -> Idx) : Real) * B ^ 2)) := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  let frame : Idx -> (y : M) -> TangentSpace I y :=
    fun i y => eâ‚€.localFrame basisE i y
  let u : Set M := eâ‚€.baseSet
  let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
  let hframe1 : IsLocalFrameOn I E 1 frame u :=
    eâ‚€.isLocalFrameOn_localFrame_baseSet I 1 basisE
  have hu : IsOpen u := eâ‚€.open_baseSet
  have hx : x âˆˆ u :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  let gInv : M -> Idx -> Idx -> Real :=
    fun y i j => LeviCivita.localInvMetricCoeff (I := I) eâ‚€ basisE g i j y
  let n : Real := Fintype.card Idx
  let N1 : Real := metricCovDerivNormWith (I := I) 1 g h g x
  let N2 : Real := metricCovDerivNormWith (I := I) 2 g h g x
  let N3 : Real := metricCovDerivNormWith (I := I) 3 g h g x
  let Q : Real := n * (n * N1)
  let R : Real := n * (n * (N2 + Q * N1 + Q * N1))
  let B : Real := n * (Q * (3 * N2) + R * (3 * N1)) +
    n * (3 * N3 + Q * (3 * N2))
  have hinvBasis :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (hframe.toBasisAt hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx)) :=
    metricInverseInBasis_identity_of_orthonormal
      (I := I) g (hframe.toBasisAt hx) (by
        simpa [eâ‚€, frame, u, hframe, hx] using hON)
  have hinvX : forall i j : Idx,
      (âˆ‘ k : Idx, gInv x i k *
          Coordinates.metricCompForMetricInFrame (I := I) g frame x k j) =
          (if i = j then 1 else 0) âˆ§
        (âˆ‘ k : Idx,
          Coordinates.metricCompForMetricInFrame (I := I) g frame x i k *
            gInv x k j) =
          (if i = j then 1 else 0) := by
    intro i j
    constructor
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_left_inv
          (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
    Â· simpa [gInv, frame, u] using
        LeviCivita.localInvMetricCoeff_metricComp_right_inv
          (I := I) eâ‚€ basisE g (by simpa [u] using hx) i j
  have hB_nonneg : 0 <= B := by
    dsimp [B, R, Q, N1, N2, N3, n, metricCovDerivNormWith]
    positivity
  have hnorm :=
    Tensor0SBundle.sqrt_normRS_le_comps
      (I := I) g x 1 4 (hframe.toBasisAt hx) hinvBasis (D2 x)
      hB_nonneg
      (fun upper lower => ?_)
  Â· simpa [connDiffDerivNorm, B, R, Q, N1, N2, N3, n] using hnorm
  let e : Idx := upper 0
  let m : Idx := lower 0
  let d : Idx := lower 1
  let a : Idx := lower 2
  let b : Idx := lower 3
  have hupper : upper = Coordinates.upperIdx1 e := by
    funext q
    fin_cases q
    simp [e, Coordinates.upperIdx1]
  have hlower : lower = Coordinates.slots4 m d a b := by
    funext q
    fin_cases q <;> simp [m, d, a, b, Coordinates.slots4]
  let comp : Real :=
    Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
      (D2 x) upper lower
  have hcomp_le_two : |comp| <= |(2 : Real) * comp| := by
    calc
      |comp| = (1 : Real) * |comp| := by ring
      _ <= |(2 : Real)| * |comp| :=
        mul_le_mul_of_nonneg_right (by norm_num : (1 : Real) <= |(2 : Real)|)
          (abs_nonneg comp)
      _ = |(2 : Real) * comp| := by rw [abs_mul]
  obtain âŸ¨Z, _Î¸, hZ, _hÎ¸, _hpairâŸ© :=
    Coordinates.existsTrivFrameCoframePair (J := I) (N := M) x basisE
  have hquad :
      |(2 : Real) * comp| <= B := by
    have hquad_eq :=
      connDiffTwo_trivFrame_cubic
        (I := I) hD2 (Z m) basisE (x := x) m d a b e
        ((hZ m).self_of_nhds)
    have hRHS :=
      lcDiffCubic_abs_le_norms_local
        (I := I) g h gInv frame hframe hu hx hinvX hinvBasis m d a b e
    have hx0 : x âˆˆ eâ‚€.baseSet := by
      simp [eâ‚€, u] at hx âŠ¢
    have hbasis :
        hframe.toBasisAt hx = eâ‚€.basisAt basisE hx0 := by
      ext i
      simp [frame, IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, hx0]
    have hbasis1 :
        hframe1.toBasisAt hx = eâ‚€.basisAt basisE hx0 := by
      ext i
      simp [frame, IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
        Bundle.Trivialization.basisAt, hx0]
    have hquad_eq' :
        2 * Tensor0SBundle.componentRS (I := I) (eâ‚€.basisAt basisE hx0) (D2 x)
            (Coordinates.upperIdx1 e) (Coordinates.slots4 m d a b) =
          Coordinates.lcDiffQuadCubicRHS
            (I := I) g gInv
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            frame hframe1 x m d a b e := by
      simpa [gInv, frame, u, hframe1, hbasis1] using hquad_eq
    have hcomp_eq :
        comp =
          Tensor0SBundle.componentRS (I := I) (hframe.toBasisAt hx)
            (D2 x) (Coordinates.upperIdx1 e) (Coordinates.slots4 m d a b) := by
      dsimp [comp]
      rw [hupper, hlower]
    rw [hcomp_eq]
    rw [hbasis]
    rw [hquad_eq']
    simpa [B, R, Q, N1, N2, N3, n, gInv, frame, u, hframe, hframe1,
      localFrameOneOfInf] using hRHS
  simpa [comp] using le_trans hcomp_le_two hquad

/-- Coordinate-frame component of a realized first derivative of
`Gamma_g - Gamma_h`, after substituting the differentiated Christoffel
formula.  The right-hand side contains the book's `âˆ‡_hÂ² g` and
`(âˆ‡_h g) * (âˆ‡_h g)` terms. -/
theorem connDiffOne_quad
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {g h : SmoothRiemannianMetric I M}
    {D1 : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 3}
    (hD1 : ConnDiffDerivRealizes (I := I) g h 1 D1)
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž)
      (TangentSpace I : M -> Type _))
    (xâ‚€ : M) (gInv : M -> Coordinates.CoordinateIdx (ð•œ := Real) E ->
      Coordinates.CoordinateIdx (ð•œ := Real) E -> Real)
    (d a b e : Coordinates.CoordinateIdx (ð•œ := Real) E)
    (hX : X xâ‚€ = Coordinates.coordinateFrameAt (I := I) xâ‚€ d xâ‚€)
    (hinv :
      Coordinates.InverseMetricComponentsForMetricInFrameOn
        (I := I) g gInv (Coordinates.coordinateFrameAt (I := I) xâ‚€))
    (hD_mdiff :
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.lcDiffCompInFrame
            (I := I) g h (Coordinates.coordinateFrameAt (I := I) xâ‚€)
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
            y a b e) xâ‚€)
    (hginv_mdiff : âˆ€ i j : Coordinates.CoordinateIdx (ð•œ := Real) E,
      MDifferentiableAt I ð“˜(Real, Real) (fun y : M => gInv y i j) xâ‚€)
    (hmetric_mdiff : âˆ€ i j : Coordinates.CoordinateIdx (ð•œ := Real) E,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCompForMetricInFrame
            (I := I) g (Coordinates.coordinateFrameAt (I := I) xâ‚€) y i j) xâ‚€)
    (hA_mdiff : âˆ€ i j k : Coordinates.CoordinateIdx (ð•œ := Real) E,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          Coordinates.metricCovDerivForMetricCompInFrame
            (I := I) g (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (Coordinates.coordinateFrameAt (I := I) xâ‚€)
            (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
            y i j k) xâ‚€) :
    2 * Tensor0SBundle.componentRS (I := I)
        (Coordinates.coordinateFrameAt_toBasis (I := I) xâ‚€)
        (D1 xâ‚€) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b) =
      Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (Coordinates.coordinateFrameAt (I := I) xâ‚€)
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
        xâ‚€ d a b e := by
  have hcoord :=
    connDiffOne_coord
      (I := I) hD1 X xâ‚€ d a b e hX
  have hquad :=
    Coordinates.lcDiffDeriv_eq_quad
      (I := I) g h gInv (Coordinates.coordinateFrameAt (I := I) xâ‚€)
      (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
      (Coordinates.coordinateFrameSet_open (I := I) xâ‚€)
      (Coordinates.coordinateFrameAt_mem (I := I) xâ‚€)
      hinv d a b e hD_mdiff hginv_mdiff hmetric_mdiff hA_mdiff
  calc
    2 * Tensor0SBundle.componentRS (I := I)
        (Coordinates.coordinateFrameAt_toBasis (I := I) xâ‚€)
        (D1 xâ‚€) (Coordinates.upperIdx1 e) (Coordinates.slots3 d a b)
        =
      2 * Coordinates.lcDiffCovDerivCompInFrame
        (I := I) g h (Coordinates.coordinateFrameAt (I := I) xâ‚€)
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
        xâ‚€ d a b e := by
          rw [hcoord]
    _ = Coordinates.lcDiffQuadRHS
        (I := I) g gInv
        (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
        (Coordinates.coordinateFrameAt (I := I) xâ‚€)
        (Coordinates.coordinateFrameAt_isLocalFrame_one (I := I) xâ‚€)
        xâ‚€ d a b e := hquad

/-- Uniform bound predicate for realized higher connection-difference
derivatives on a set.  The realization field prevents this from becoming an
arbitrary placeholder predicate. -/
def ConnDiffDerivBoundOn
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x âˆˆ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C

/-- Book-facing F3-hi epsilon control for a realized `k`-th `h`-covariant
derivative of `Gamma_g - Gamma_h`.  The constant is independent of `eps`; this
is the shape consumed in MSM135 Chapter 4, Lemma "Norms of covariant derivatives
of tensors, I". -/
def ConnDiffEpsBoundOn
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x âˆˆ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C * eps

/-- Uniform book-facing F3-hi epsilon controls for all orders below `m`. -/
def ConnDiffEpsBoundsBelow
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffEpsBoundOn (I := I) K eps g h k (C k)

/-- The `k = 0` connection-difference derivative bound, packaged in the
higher-derivative realization vocabulary used by F3e. -/
theorem connDiffDerivBound_zero
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x âˆˆ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x âˆˆ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffDerivBoundOn (I := I) K g h 0 (12 * eps) := by
  intro D0 hD0 x hx
  rcases hD0 with âŸ¨D, hD, hderivâŸ©
  cases hderiv
  simpa [connDiffDerivNorm, ConnDiffFieldRealizes, hD x] using
    connDiff_book_le_eps_g
      (I := I) Happrox hx hp heps_lt (basis x hx) (hinv x hx)

/-- The checked `k = 0` instance of the book-facing F3-hi epsilon control. -/
theorem connDiffEpsBound_zero
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : forall x : M, x âˆˆ K ->
      Module.Basis Idx Real (TangentSpace I x))
    (hinv : forall x : M, forall hx : x âˆˆ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric (Idx := Idx))) :
    ConnDiffEpsBoundOn (I := I) K eps g h 0 12 := by
  intro D0 hD0 x hx
  simpa using
    connDiffDerivBound_zero
      (I := I) Happrox hp heps_lt basis hinv D0 hD0 x hx

/-- A coarse dimension constant for the first positive-order
connection-difference epsilon estimate in a finite index frame.  The constant is
not sharp; it only packages the finite component count in the proof. -/
def connDiffOneConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let q : Real := n * (((n * (n * 8)) * (3 * 8))) + n * (3 * 16)
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 3 -> Idx) : Real) * q ^ 2))

/-- A coarse dimension constant for the second positive-order
connection-difference epsilon estimate in a finite index frame. -/
def connDiffTwoConst (Idx : Type*) [Fintype Idx] : Real :=
  let n : Real := Fintype.card Idx
  let Q0 : Real := n * (n * 8)
  let R0 : Real := n * (n * (16 + Q0 * 8 + Q0 * 8))
  let q : Real :=
    n * (Q0 * (3 * 16) + R0 * (3 * 8)) +
      n * (3 * 32 + Q0 * (3 * 16))
  Real.sqrt
    ((Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 4 -> Idx) : Real) * q ^ 2))

/-- First positive-order connection-difference epsilon estimate, assuming the
centered tangent trivialization frame has been chosen `g`-orthonormally.

This closes the numerical approximate-isometry part of the `k = 1` estimate.
The remaining producer for the public theorem is the pointwise construction of
such a centered trivialization basis. -/
theorem connDiffEpsBound_one_of_trivON
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 2 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisE : forall x : M, x âˆˆ K -> Module.Basis Idx Real E)
    (hON : forall x : M, forall hx : x âˆˆ K,
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame (basisE x hx) i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) (basisE x hx)
      let hxu : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      forall i j : Idx,
        g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
          if i = j then 1 else 0) :
    ConnDiffEpsBoundOn (I := I) K eps g h 1 (connDiffOneConst Idx) := by
  classical
  intro D1 hD1 x hx
  let A1 : Real := metricCovDerivNormWith (I := I) 1 g h g x
  let A2 : Real := metricCovDerivNormWith (I := I) 2 g h g x
  let n : Real := Fintype.card Idx
  let B : Real :=
    n * (((n * (n * A1)) * (3 * A1))) + n * (3 * A2)
  let q : Real := n * (((n * (n * 8)) * (3 * 8))) + n * (3 * 16)
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  have heps_le_one : eps <= 1 := by linarith
  have hbase_nonneg : 0 <= 1 + eps := by linarith
  have hbase_le : 1 + eps <= (2 : Real) := by linarith
  have hsqrt3_le : Real.sqrt ((1 + eps) ^ 3) <= (8 : Real) := by
    have hpow : (1 + eps) ^ 3 <= (8 : Real) := by
      have hpow' : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
        pow_le_pow_leftâ‚€ hbase_nonneg hbase_le 3
      norm_num at hpow'
      exact hpow'
    have hsqrt : Real.sqrt ((1 + eps) ^ 3) <= Real.sqrt (8 : Real) :=
      Real.sqrt_le_sqrt hpow
    have hsqrt8 : Real.sqrt (8 : Real) <= (8 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt8
  have hsqrt4_le : Real.sqrt ((1 + eps) ^ 4) <= (16 : Real) := by
    have hpow : (1 + eps) ^ 4 <= (16 : Real) := by
      have hpow' : (1 + eps) ^ 4 <= (2 : Real) ^ 4 :=
        pow_le_pow_leftâ‚€ hbase_nonneg hbase_le 4
      norm_num at hpow'
      exact hpow'
    have hsqrt : Real.sqrt ((1 + eps) ^ 4) <= Real.sqrt (16 : Real) :=
      Real.sqrt_le_sqrt hpow
    have hsqrt16 : Real.sqrt (16 : Real) <= (16 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt16
  have hA1_nonneg : 0 <= A1 := by
    dsimp [A1, metricCovDerivNormWith]
    exact Real.sqrt_nonneg _
  have hA2_nonneg : 0 <= A2 := by
    dsimp [A2, metricCovDerivNormWith]
    exact Real.sqrt_nonneg _
  have hA1_raw : A1 <= Real.sqrt ((1 + eps) ^ 3) * eps := by
    have hconv :=
      IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
        (I := I) (a := 1) Happrox hx
    have hsmall :
        metricCovDerivNorm (I := I) 1 g h x <= eps :=
      Happrox.reverse_cov_deriv_small 1 le_rfl
        (le_trans (by norm_num : 1 <= 2) hp) x hx
    exact hconv.trans
      (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
  have hA2_raw : A2 <= Real.sqrt ((1 + eps) ^ 4) * eps := by
    have hconv :=
      IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
        (I := I) (a := 2) Happrox hx
    have hsmall :
        metricCovDerivNorm (I := I) 2 g h x <= eps :=
      Happrox.reverse_cov_deriv_small 2 (by norm_num) hp x hx
    simpa using hconv.trans
      (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
  have hA1_eps : A1 <= 8 * eps := by
    exact hA1_raw.trans
      (mul_le_mul_of_nonneg_right hsqrt3_le heps_nonneg)
  have hA1_const : A1 <= 8 := by
    calc
      A1 <= 8 * eps := hA1_eps
      _ <= 8 * 1 := mul_le_mul_of_nonneg_left heps_le_one (by norm_num)
      _ = 8 := by norm_num
  have hA2_eps : A2 <= 16 * eps := by
    exact hA2_raw.trans
      (mul_le_mul_of_nonneg_right hsqrt4_le heps_nonneg)
  have hn_nonneg : 0 <= n := by
    dsimp [n]
    positivity
  have hB_eq : B = 3 * n ^ 3 * A1 ^ 2 + 3 * n * A2 := by
    dsimp [B]
    ring
  have hq_eq : q = 192 * n ^ 3 + 48 * n := by
    dsimp [q]
    ring
  have hA1_sq : A1 ^ 2 <= 64 * eps := by
    calc
      A1 ^ 2 = A1 * A1 := by ring
      _ <= (8 * eps) * 8 :=
        mul_le_mul hA1_eps hA1_const hA1_nonneg
          (mul_nonneg (by norm_num) heps_nonneg)
      _ = 64 * eps := by ring
  have hB_nonneg : 0 <= B := by
    rw [hB_eq]
    positivity
  have hq_nonneg : 0 <= q := by
    rw [hq_eq]
    positivity
  have hB_le : B <= q * eps := by
    have hterm1 : 3 * n ^ 3 * A1 ^ 2 <= 3 * n ^ 3 * (64 * eps) := by
      exact mul_le_mul_of_nonneg_left hA1_sq (by positivity)
    have hterm2 : 3 * n * A2 <= 3 * n * (16 * eps) := by
      exact mul_le_mul_of_nonneg_left hA2_eps (by positivity)
    rw [hB_eq, hq_eq]
    nlinarith [hterm1, hterm2]
  have hraw :
      connDiffDerivNorm (I := I) g 1 D1 x <=
        Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) := by
    simpa [B, n, A1, A2] using
      connDiffOne_trivON
        (I := I) hD1 (basisE x hx) (x := x) (hON x hx)
  have hBsq_le : B ^ 2 <= (q * eps) ^ 2 :=
    (sq_le_sqâ‚€ hB_nonneg (mul_nonneg hq_nonneg heps_nonneg)).2 hB_le
  have hcardUpper_nonneg :
      0 <= (Fintype.card (Fin 1 -> Idx) : Real) := by positivity
  have hcardLower_nonneg :
      0 <= (Fintype.card (Fin 3 -> Idx) : Real) := by positivity
  let R : Real :=
    (Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 3 -> Idx) : Real) * q ^ 2)
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    positivity
  have hsqrt_le :
      Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 3 -> Idx) : Real) * B ^ 2)) <=
        Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 3 -> Idx) : Real) * (q * eps) ^ 2)) := by
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBsq_le hcardLower_nonneg)
        hcardUpper_nonneg)
  have hsqrt_eq :
      Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 3 -> Idx) : Real) * (q * eps) ^ 2)) =
        connDiffOneConst Idx * eps := by
    have hrewrite :
        (Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 3 -> Idx) : Real) * (q * eps) ^ 2) =
          eps ^ 2 * R := by
      dsimp [R]
      ring
    rw [hrewrite]
    rw [Real.sqrt_mul (sq_nonneg eps)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps_nonneg]
    dsimp [connDiffOneConst, q, n, R]
    ring
  exact hraw.trans (hsqrt_le.trans (le_of_eq hsqrt_eq))

/-- Second positive-order connection-difference epsilon estimate, assuming the
centered tangent trivialization frame has been chosen `g`-orthonormally.

This is the `k = 2` numerical endpoint after the cubic Christoffel reassembly:
the cubic terms are made linear in `eps` by using `eps < 1`. -/
theorem connDiffEpsBound_two_of_trivON
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 3 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisE : forall x : M, x âˆˆ K -> Module.Basis Idx Real E)
    (hON : forall x : M, forall hx : x âˆˆ K,
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Idx -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame (basisE x hx) i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) (basisE x hx)
      let hxu : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      forall i j : Idx,
        g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
          if i = j then 1 else 0) :
    ConnDiffEpsBoundOn (I := I) K eps g h 2 (connDiffTwoConst Idx) := by
  classical
  intro D2 hD2 x hx
  let A1 : Real := metricCovDerivNormWith (I := I) 1 g h g x
  let A2 : Real := metricCovDerivNormWith (I := I) 2 g h g x
  let A3 : Real := metricCovDerivNormWith (I := I) 3 g h g x
  let n : Real := Fintype.card Idx
  let Q : Real := n * (n * A1)
  let R : Real := n * (n * (A2 + Q * A1 + Q * A1))
  let B : Real :=
    n * (Q * (3 * A2) + R * (3 * A1)) +
      n * (3 * A3 + Q * (3 * A2))
  let Q0 : Real := n * (n * 8)
  let R0 : Real := n * (n * (16 + Q0 * 8 + Q0 * 8))
  let q : Real :=
    n * (Q0 * (3 * 16) + R0 * (3 * 8)) +
      n * (3 * 32 + Q0 * (3 * 16))
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.forward.uniform_equiv.1
    linarith
  have heps_le_one : eps <= 1 := by linarith
  have hbase_nonneg : 0 <= 1 + eps := by linarith
  have hbase_le : 1 + eps <= (2 : Real) := by linarith
  have hsqrt3_le : Real.sqrt ((1 + eps) ^ 3) <= (8 : Real) := by
    have hpow : (1 + eps) ^ 3 <= (8 : Real) := by
      have hpow' : (1 + eps) ^ 3 <= (2 : Real) ^ 3 :=
        pow_le_pow_leftâ‚€ hbase_nonneg hbase_le 3
      norm_num at hpow'
      exact hpow'
    have hsqrt : Real.sqrt ((1 + eps) ^ 3) <= Real.sqrt (8 : Real) :=
      Real.sqrt_le_sqrt hpow
    have hsqrt8 : Real.sqrt (8 : Real) <= (8 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt8
  have hsqrt4_le : Real.sqrt ((1 + eps) ^ 4) <= (16 : Real) := by
    have hpow : (1 + eps) ^ 4 <= (16 : Real) := by
      have hpow' : (1 + eps) ^ 4 <= (2 : Real) ^ 4 :=
        pow_le_pow_leftâ‚€ hbase_nonneg hbase_le 4
      norm_num at hpow'
      exact hpow'
    have hsqrt : Real.sqrt ((1 + eps) ^ 4) <= Real.sqrt (16 : Real) :=
      Real.sqrt_le_sqrt hpow
    have hsqrt16 : Real.sqrt (16 : Real) <= (16 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt16
  have hsqrt5_le : Real.sqrt ((1 + eps) ^ 5) <= (32 : Real) := by
    have hpow : (1 + eps) ^ 5 <= (32 : Real) := by
      have hpow' : (1 + eps) ^ 5 <= (2 : Real) ^ 5 :=
        pow_le_pow_leftâ‚€ hbase_nonneg hbase_le 5
      norm_num at hpow'
      exact hpow'
    have hsqrt : Real.sqrt ((1 + eps) ^ 5) <= Real.sqrt (32 : Real) :=
      Real.sqrt_le_sqrt hpow
    have hsqrt32 : Real.sqrt (32 : Real) <= (32 : Real) := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact hsqrt.trans hsqrt32
  have hA1_nonneg : 0 <= A1 := by
    dsimp [A1, metricCovDerivNormWith]
    exact Real.sqrt_nonneg _
  have hA2_nonneg : 0 <= A2 := by
    dsimp [A2, metricCovDerivNormWith]
    exact Real.sqrt_nonneg _
  have hA3_nonneg : 0 <= A3 := by
    dsimp [A3, metricCovDerivNormWith]
    exact Real.sqrt_nonneg _
  have hA1_raw : A1 <= Real.sqrt ((1 + eps) ^ 3) * eps := by
    have hconv :=
      IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
        (I := I) (a := 1) Happrox hx
    have hsmall :
        metricCovDerivNorm (I := I) 1 g h x <= eps :=
      Happrox.reverse_cov_deriv_small 1 le_rfl
        (le_trans (by norm_num : 1 <= 3) hp) x hx
    exact hconv.trans
      (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
  have hA2_raw : A2 <= Real.sqrt ((1 + eps) ^ 4) * eps := by
    have hconv :=
      IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
        (I := I) (a := 2) Happrox hx
    have hsmall :
        metricCovDerivNorm (I := I) 2 g h x <= eps :=
      Happrox.reverse_cov_deriv_small 2 (by norm_num)
        (le_trans (by norm_num : 2 <= 3) hp) x hx
    simpa using hconv.trans
      (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
  have hA3_raw : A3 <= Real.sqrt ((1 + eps) ^ 5) * eps := by
    have hconv :=
      IsTwoSidedApproxIsometryOn.metricCovDerivNormWith_book_le
        (I := I) (a := 3) Happrox hx
    have hsmall :
        metricCovDerivNorm (I := I) 3 g h x <= eps :=
      Happrox.reverse_cov_deriv_small 3 (by norm_num) hp x hx
    simpa using hconv.trans
      (mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _))
  have hA1_eps : A1 <= 8 * eps :=
    hA1_raw.trans (mul_le_mul_of_nonneg_right hsqrt3_le heps_nonneg)
  have hA2_eps : A2 <= 16 * eps :=
    hA2_raw.trans (mul_le_mul_of_nonneg_right hsqrt4_le heps_nonneg)
  have hA3_eps : A3 <= 32 * eps :=
    hA3_raw.trans (mul_le_mul_of_nonneg_right hsqrt5_le heps_nonneg)
  have hA1_const : A1 <= 8 := by
    calc
      A1 <= 8 * eps := hA1_eps
      _ <= 8 * 1 := mul_le_mul_of_nonneg_left heps_le_one (by norm_num)
      _ = 8 := by norm_num
  have hA2_const : A2 <= 16 := by
    calc
      A2 <= 16 * eps := hA2_eps
      _ <= 16 * 1 := mul_le_mul_of_nonneg_left heps_le_one (by norm_num)
      _ = 16 := by norm_num
  have hn_nonneg : 0 <= n := by
    dsimp [n]
    positivity
  have hQ_nonneg : 0 <= Q := by
    dsimp [Q]
    positivity
  have hR_nonneg' : 0 <= R := by
    dsimp [R, Q]
    positivity
  have hQ_const : Q <= Q0 := by
    dsimp [Q, Q0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hA1_const hn_nonneg) hn_nonneg
  have hQ0_nonneg : 0 <= Q0 := by
    dsimp [Q0]
    positivity
  have hR_const : R <= R0 := by
    have hQA_const : Q * A1 <= Q0 * 8 :=
      mul_le_mul hQ_const hA1_const hA1_nonneg hQ0_nonneg
    have hsum :
        A2 + Q * A1 + Q * A1 <= 16 + Q0 * 8 + Q0 * 8 := by
      nlinarith [hA2_const, hQA_const]
    dsimp [R, R0]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum hn_nonneg) hn_nonneg
  have hR0_nonneg : 0 <= R0 := by
    dsimp [R0, Q0]
    positivity
  have hB_nonneg : 0 <= B := by
    dsimp [B]
    positivity
  have hq_nonneg : 0 <= q := by
    dsimp [q, R0, Q0]
    positivity
  have hB_le : B <= q * eps := by
    have htermQA2 :
        Q * (3 * A2) <= Q0 * (3 * 16) * eps := by
      calc
        Q * (3 * A2) <= Q0 * (3 * (16 * eps)) :=
          mul_le_mul hQ_const
            (mul_le_mul_of_nonneg_left hA2_eps (by norm_num))
            (by positivity) hQ0_nonneg
        _ = Q0 * (3 * 16) * eps := by ring
    have htermRA1 :
        R * (3 * A1) <= R0 * (3 * 8) * eps := by
      calc
        R * (3 * A1) <= R0 * (3 * (8 * eps)) :=
          mul_le_mul hR_const
            (mul_le_mul_of_nonneg_left hA1_eps (by norm_num))
            (by positivity) hR0_nonneg
        _ = R0 * (3 * 8) * eps := by ring
    have htermA3 :
        3 * A3 <= 3 * 32 * eps := by
      calc
        3 * A3 <= 3 * (32 * eps) :=
          mul_le_mul_of_nonneg_left hA3_eps (by norm_num)
        _ = 3 * 32 * eps := by ring
    dsimp [B, q]
    nlinarith [htermQA2, htermRA1, htermA3]
  have hraw :
      connDiffDerivNorm (I := I) g 2 D2 x <=
        Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 4 -> Idx) : Real) * B ^ 2)) := by
    simpa [B, R, Q, n, A1, A2, A3] using
      connDiffTwo_trivON
        (I := I) hD2 (basisE x hx) (x := x) (hON x hx)
  have hBsq_le : B ^ 2 <= (q * eps) ^ 2 :=
    (sq_le_sqâ‚€ hB_nonneg (mul_nonneg hq_nonneg heps_nonneg)).2 hB_le
  have hcardUpper_nonneg :
      0 <= (Fintype.card (Fin 1 -> Idx) : Real) := by positivity
  have hcardLower_nonneg :
      0 <= (Fintype.card (Fin 4 -> Idx) : Real) := by positivity
  let S : Real :=
    (Fintype.card (Fin 1 -> Idx) : Real) *
      ((Fintype.card (Fin 4 -> Idx) : Real) * q ^ 2)
  have hsqrt_le :
      Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 4 -> Idx) : Real) * B ^ 2)) <=
        Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 4 -> Idx) : Real) * (q * eps) ^ 2)) := by
    exact Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBsq_le hcardLower_nonneg)
        hcardUpper_nonneg)
  have hsqrt_eq :
      Real.sqrt
          ((Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 4 -> Idx) : Real) * (q * eps) ^ 2)) =
        connDiffTwoConst Idx * eps := by
    have hrewrite :
        (Fintype.card (Fin 1 -> Idx) : Real) *
            ((Fintype.card (Fin 4 -> Idx) : Real) * (q * eps) ^ 2) =
          eps ^ 2 * S := by
      dsimp [S]
      ring
    rw [hrewrite]
    rw [Real.sqrt_mul (sq_nonneg eps)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg heps_nonneg]
    dsimp [connDiffTwoConst, q, n, Q0, R0, S]
    ring
  exact hraw.trans (hsqrt_le.trans (le_of_eq hsqrt_eq))

/-- A finite-dimensional real vector space carrying a symmetric positive-definite
bilinear form admits a basis orthonormal for that form.  This is elementary
linear algebra: take any `B`-orthogonal basis and rescale each vector by the
inverse square root of its self-pairing. -/
private theorem exists_orthonormalBasis_of_posDef
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (B : LinearMap.BilinForm Real V) (hsymm : LinearMap.IsSymm B)
    (hpos : forall v : V, v â‰  0 -> 0 < B v v) :
    exists b : Module.Basis (Fin (Module.finrank Real V)) Real V,
      forall i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  obtain âŸ¨v, hvâŸ© := LinearMap.BilinForm.exists_orthogonal_basis (B := B) hsymm
  have hdpos : forall i, 0 < B (v i) (v i) := fun i => hpos (v i) (v.ne_zero i)
  set w : Fin (Module.finrank Real V) -> Real :=
    fun i => (Real.sqrt (B (v i) (v i)))â»Â¹ with hw
  have hwunit : forall i, IsUnit (w i) := by
    intro i
    refine isUnit_iff_ne_zero.mpr ?_
    simp only [hw]
    exact inv_ne_zero (Real.sqrt_pos.mpr (hdpos i)).ne'
  refine âŸ¨v.isUnitSMul hwunit, ?_âŸ©
  intro i j
  have hreduce :
      B ((v.isUnitSMul hwunit) i) ((v.isUnitSMul hwunit) j) =
        (w i * w j) * B (v i) (v j) := by
    simp only [Module.Basis.isUnitSMul_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [hreduce]
  by_cases hij : i = j
  Â· subst hij
    rw [if_pos rfl]
    have hd : 0 < B (v i) (v i) := hdpos i
    have hroot :
        Real.sqrt (B (v i) (v i)) * Real.sqrt (B (v i) (v i)) = B (v i) (v i) :=
      Real.mul_self_sqrt hd.le
    simp only [hw]
    rw [â† mul_inv, hroot, inv_mul_cancelâ‚€ hd.ne']
  Â· rw [if_neg hij]
    have horth : B (v i) (v j) = 0 := (LinearMap.isOrthoáµ¢_def.mp hv) i j hij
    rw [horth, mul_zero]

/-- Pointwise orthonormal trivialization frame for a Riemannian metric.

At each point `x`, the canonical trivialization `trivializationAt` identifies the
tangent fiber with the model fiber `E`.  Pulling `g.inner x` back to `E` gives a
symmetric positive-definite bilinear form, so finite-dimensional linear algebra
provides a basis of `E` whose induced local frame is `g`-orthonormal at `x`.
This is the producer that removes the orthonormal-trivialization-frame
hypothesis from `connDiffEpsBound_one_of_trivON`. -/
theorem exists_trivFrame_orthonormal_basis
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothRiemannianMetric I M) (x : M) :
    exists basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Fin (Module.finrank Real E) -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame basisE i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
      let hxu : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      forall i j : Fin (Module.finrank Real E),
        g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
          if i = j then 1 else 0 := by
  classical
  let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
  have hxu0 : x âˆˆ eâ‚€.baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
  -- Pull `g.inner x` back to the model fiber `E` through the trivialization.
  let Q : LinearMap.BilinForm Real E :=
    LinearMap.mkâ‚‚ Real
      (fun v w => g.inner x (eâ‚€.symmL Real x v) (eâ‚€.symmL Real x w))
      (fun _ _ _ => by simp [map_add, ContinuousLinearMap.add_apply])
      (fun _ _ _ => by simp [map_smul, ContinuousLinearMap.smul_apply])
      (fun _ _ _ => by simp [map_add])
      (fun _ _ _ => by simp [map_smul])
  have hsymm : LinearMap.IsSymm Q :=
    âŸ¨fun v w => by
      simp only [Q, LinearMap.mkâ‚‚_apply, RingHom.id_apply]
      exact g.symm x (eâ‚€.symmL Real x v) (eâ‚€.symmL Real x w)âŸ©
  have hpos : forall v : E, v â‰  0 -> 0 < Q v v := by
    intro v hv
    have hSv : eâ‚€.symmL Real x v â‰  0 := by
      intro h0
      apply hv
      have hself := eâ‚€.continuousLinearMapAt_symmL (R := Real) hxu0 v
      rw [h0, map_zero] at hself
      exact hself.symm
    simp only [Q, LinearMap.mkâ‚‚_apply]
    exact g.pos x (eâ‚€.symmL Real x v) hSv
  obtain âŸ¨b, hbâŸ© := exists_orthonormalBasis_of_posDef Q hsymm hpos
  have hsymmL : forall k, eâ‚€.symmL Real x (b k) = eâ‚€.localFrame b k x := fun k => by
    rw [eâ‚€.localFrame_apply_of_mem_baseSet (b := b) hxu0]
    simp [Bundle.Trivialization.basisAt]
  have hgram :
      forall i j,
        g.inner x (eâ‚€.localFrame b i x) (eâ‚€.localFrame b j x) =
          if i = j then 1 else 0 := by
    intro i j
    rw [â† hsymmL i, â† hsymmL j]
    simpa [Q, LinearMap.mkâ‚‚_apply] using hb i j
  refine âŸ¨b, ?_âŸ©
  intro eâ‚€' frame u' hframe hxu' i j
  have h1 : hframe.toBasisAt hxu' i = eâ‚€'.localFrame b i x :=
    IsLocalFrameOn.toBasisAt_coe hframe hxu' i
  have h2 : hframe.toBasisAt hxu' j = eâ‚€'.localFrame b j x :=
    IsLocalFrameOn.toBasisAt_coe hframe hxu' j
  rw [h1, h2]
  exact hgram i j

/-- First positive-order connection-difference epsilon estimate.

This is the public `k = 1` endpoint.  The orthonormal trivialization frame
hypothesis of `connDiffEpsBound_one_of_trivON` is discharged pointwise by
`exists_trivFrame_orthonormal_basis`, so no orthonormal-frame data is exposed to
the caller. -/
theorem connDiffEpsBound_one
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 2 â‰¤ p) (heps_lt : eps < 1) :
    ConnDiffEpsBoundOn (I := I) K eps g h 1
      (connDiffOneConst (Fin (Module.finrank Real E))) := by
  classical
  have key :
      forall x : M, x âˆˆ K ->
        exists basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
          let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
          let frame : Fin (Module.finrank Real E) -> (y : M) -> TangentSpace I y :=
            fun i y => eâ‚€.localFrame basisE i y
          let u : Set M := eâ‚€.baseSet
          let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
            eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
          let hxu : x âˆˆ u :=
            mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
          forall i j : Fin (Module.finrank Real E),
            g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
              if i = j then 1 else 0 :=
    fun x _ => exists_trivFrame_orthonormal_basis (I := I) g x
  choose basisE hON using key
  exact connDiffEpsBound_one_of_trivON (I := I) Happrox hp heps_lt basisE hON

/-- Second positive-order connection-difference epsilon estimate.

This is the public `k = 2` endpoint.  It chooses the same pointwise
orthonormal trivialization basis used by the `k = 1` endpoint, so no local-frame
data is exposed to callers. -/
theorem connDiffEpsBound_two
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 3 â‰¤ p) (heps_lt : eps < 1) :
    ConnDiffEpsBoundOn (I := I) K eps g h 2
      (connDiffTwoConst (Fin (Module.finrank Real E))) := by
  classical
  have key :
      forall x : M, x âˆˆ K ->
        exists basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
          let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
          let frame : Fin (Module.finrank Real E) -> (y : M) -> TangentSpace I y :=
            fun i y => eâ‚€.localFrame basisE i y
          let u : Set M := eâ‚€.baseSet
          let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
            eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
          let hxu : x âˆˆ u :=
            mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
          forall i j : Fin (Module.finrank Real E),
            g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
              if i = j then 1 else 0 :=
    fun x _ => exists_trivFrame_orthonormal_basis (I := I) g x
  choose basisE hON using key
  exact connDiffEpsBound_two_of_trivON (I := I) Happrox hp heps_lt basisE hON

/-- Public `k = 0` connection-difference epsilon estimate with no frame data
exposed to the caller.  The pointwise orthonormal tangent basis is chosen from
the canonical tangent trivialization. -/
theorem connDiffEpsBound_zero_std
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 1 <= p) (heps_lt : eps < 1) :
    ConnDiffEpsBoundOn (I := I) K eps g h 0 12 := by
  classical
  have key :
      forall x : M, x âˆˆ K ->
        exists basisE : Module.Basis (Fin (Module.finrank Real E)) Real E,
          let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
          let frame : Fin (Module.finrank Real E) -> (y : M) -> TangentSpace I y :=
            fun i y => eâ‚€.localFrame basisE i y
          let u : Set M := eâ‚€.baseSet
          let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
            eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) basisE
          let hxu : x âˆˆ u :=
            mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
          forall i j : Fin (Module.finrank Real E),
            g.inner x (hframe.toBasisAt hxu i) (hframe.toBasisAt hxu j) =
              if i = j then 1 else 0 :=
    fun x _ => exists_trivFrame_orthonormal_basis (I := I) g x
  choose basisE hON using key
  let basis : forall x : M, x âˆˆ K ->
      Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x) :=
    fun x hx =>
      let eâ‚€ := trivializationAt E (TangentSpace I : M -> Type _) x
      let frame : Fin (Module.finrank Real E) -> (y : M) -> TangentSpace I y :=
        fun i y => eâ‚€.localFrame (basisE x hx) i y
      let u : Set M := eâ‚€.baseSet
      let hframe : IsLocalFrameOn I E (âˆž : WithTop â„•âˆž) frame u :=
        eâ‚€.isLocalFrameOn_localFrame_baseSet I (âˆž : WithTop â„•âˆž) (basisE x hx)
      let hxu : x âˆˆ u :=
        mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x
      hframe.toBasisAt hxu
  have hinv : forall x : M, forall hx : x âˆˆ K,
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x (basis x hx)
        (Tensor0SBundle.identityInvMetric
          (Idx := Fin (Module.finrank Real E))) := by
    intro x hx
    exact
      metricInverseInBasis_identity_of_orthonormal
        (I := I) g (basis x hx) (by
          intro i j
          dsimp [basis]
          simpa using hON x hx i j)
  exact connDiffEpsBound_zero (I := I) Happrox hp heps_lt basis hinv

/-- Constants for the checked connection-difference epsilon controls below
order two. -/
def connDiffEpsConst_two
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    [Module.Finite Real E] : Nat -> Real
  | 0 => 12
  | _ + 1 => connDiffOneConst (Fin (Module.finrank Real E))

/-- Constants for the checked connection-difference epsilon controls below
order three. -/
def connDiffEpsConst_three
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace Real E]
    [Module.Finite Real E] : Nat -> Real
  | 0 => 12
  | 1 => connDiffOneConst (Fin (Module.finrank Real E))
  | _ => connDiffTwoConst (Fin (Module.finrank Real E))

/-- Public connection-difference epsilon controls for orders `0` and `1`.

This is the uniform package consumed before starting the genuine higher-order
Christoffel/product-rule induction. -/
theorem connDiffEpsBounds_two
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 2 <= p) (heps_lt : eps < 1) :
    ConnDiffEpsBoundsBelow (I := I) K eps g h 2
      (connDiffEpsConst_two E) := by
  intro k hk
  cases k with
  | zero =>
      simpa [connDiffEpsConst_two] using
        connDiffEpsBound_zero_std (I := I) Happrox
          (le_trans (by norm_num : 1 <= 2) hp) heps_lt
  | succ k =>
      cases k with
      | zero =>
          simpa [connDiffEpsConst_two] using
            connDiffEpsBound_one (I := I) Happrox hp heps_lt
      | succ k =>
          omega

/-- Public connection-difference epsilon controls for orders `0`, `1`, and `2`.

This packages the checked base range before the genuinely general higher-order
Christoffel/product-rule induction. -/
theorem connDiffEpsBounds_three
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsTwoSidedApproxIsometryOn (I := I) K eps p g h)
    (hp : 3 <= p) (heps_lt : eps < 1) :
    ConnDiffEpsBoundsBelow (I := I) K eps g h 3
      (connDiffEpsConst_three E) := by
  intro k hk
  cases k with
  | zero =>
      simpa [connDiffEpsConst_three] using
        connDiffEpsBound_zero_std (I := I) Happrox
          (le_trans (by norm_num : 1 <= 3) hp) heps_lt
  | succ k =>
      cases k with
      | zero =>
          simpa [connDiffEpsConst_three] using
            connDiffEpsBound_one (I := I) Happrox
              (le_trans (by norm_num : 2 <= 3) hp) heps_lt
      | succ k =>
          cases k with
          | zero =>
              simpa [connDiffEpsConst_three] using
                connDiffEpsBound_two (I := I) Happrox hp heps_lt
          | succ k =>
              omega

set_option backward.isDefEq.respectTransparency false in
/-- Component form of the first-order connection-change identity.

This is the local-frame wrapper used for the `r = 1` case of MSM135 Chapter 4,
Lemma "Norms of covariant derivatives of tensors, I".  It specializes the
tensor identity `totalNablaSub_eq_connActTensor` to Levi-Civita connections of
`h` and `g`, so the difference of the supplied total covariant derivatives is
the zeroth-order connection-difference action on `T`. -/
theorem nabla_component_eq_base_plus_connAct_components_trivFrame
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {g h : SmoothRiemannianMetric I M}
    {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r s)
    (nablaH nablaG : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r (s + 1))
    (hrealH : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) T nablaH)
    (hrealG : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) T nablaG)
    (Î² : (Fin r -> Idx) -> (y : M) -> Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (Xfield : Idx ->
      ContMDiffSection I E (âˆž : WithTop â„•âˆž) (TangentSpace I : M -> Type _))
    (V : Idx -> (y : M) -> TangentSpace I y)
    (hX_at : forall i : Idx, Xfield i x = basis i)
    (hÎ²_at : forall upper : Fin r -> Idx,
      Î² upper x = Tensor0SBundle.basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x = basis i)
    (hT_diff : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => (T y (Î² upper y)) (fun a : Fin s => V (lower a.succ) y)) x)
    (hÎ²_diff : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Î² upper y (fun a : Fin r => V (slots a) y)) x)
    (hÎ²model : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r x (Î² upper))
      (Set.range I) (extChartAt I x x))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (ð•œ := Real) (I := I) x (V i))
        (Set.range I) (extChartAt I x x))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          (Module.finBasis Real E).coord j
            (TensorLieDeriv.tangentFieldModelInChart
              (ð•œ := Real) (I := I) x (V i) (extChartAt I x y))) x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    Tensor0SBundle.componentRS (I := I) basis (nablaH x - nablaG x) upper lower =
      Tensor0SBundle.connActComp
        (fun l i j =>
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' =>
          Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
        upper lower := by
  let covh := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let covg := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  have htensor :
      nablaH x - nablaG x =
        Tensor0SBundle.connActTensorAt (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
          (T x) :=
    Tensor0SBundle.totalNablaSub_eq_connActTensor
      (I := I) (r := r) (s := s) (Idx := Idx)
      covh covg T nablaH nablaG hrealH hrealG Î² x basis
      Xfield V hX_at hÎ²_at hV_at hT_diff hÎ²_diff hÎ²model hV hVmodel hcoord
  calc
    Tensor0SBundle.componentRS (I := I) basis (nablaH x - nablaG x) upper lower
        =
      Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.connActTensorAt (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
          (T x)) upper lower := by rw [htensor]
    _ = Tensor0SBundle.connActComp
        (fun l i j =>
          Tensor0SBundle.componentRS (I := I) basis
            (Tensor0SBundle.connectionDifferenceTensorAt
              (I := I)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
              (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)
            (fun _ : Fin 1 => l)
            (fun q : Fin 2 => if q = 0 then i else j))
        (fun upper' lower' =>
          Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
        upper lower := by
      rw [Tensor0SBundle.connActTensorAt_comp]

/-- F3 component-action estimate at order one.

This is the component-level consequence of `connDiff_le_approx`: the
connection-difference action on one component of a mixed tensor is bounded by
the connection-difference norm times the tensor norm, with a coarse finite
constant depending only on valence and dimension.  The orientation is
`leviCivita(h) - leviCivita(g)`, matching `connDiff_le_approx`; the later
`nabla` comparison chooses the corresponding sign. -/
theorem connAct_le_approx
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat} (T : Tensor0SBundle.TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx) :
    |Tensor0SBundle.connActComp
      (fun l i j =>
        Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)
          (fun _ : Fin 1 => l)
          (fun q : Fin 2 => if q = 0 then i else j))
      (fun upper' lower' => Tensor0SBundle.componentRS (I := I) basis T upper' lower')
      upper lower| <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
  let A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    Tensor0SBundle.connectionDifferenceTensorAt
      (I := I)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x
  have hbase :=
    Tensor0SBundle.abs_connActTensor_le
      (I := I) h x basis hinv A T upper lower
  have hdiff :=
    connDiff_le_approx
      (I := I) Happrox hx hp basis hinv
  have hT_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hvalence_nonneg :
      0 <= ((r + s : Nat) : Real) := by
    positivity
  have hdim_nonneg :
      0 <= (Fintype.card Idx : Real) := by
    positivity
  have hconst :
      Tensor0SBundle.connActConst (Idx := Idx) r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) 1 2 A))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold Tensor0SBundle.connActConst
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hdiff hT_nonneg)
        hdim_nonneg)
      hvalence_nonneg
  exact hbase.trans hconst

set_option backward.isDefEq.respectTransparency false in
/-- F3 order-one component estimate for covariant derivatives of a mixed tensor.

This combines the manifold component identity
`Tensor0SBundle.componentRS_nablaRSFun_sub` with the approximate-isometry
connection-difference estimate `connAct_le_approx`.  It is still a local-frame
component statement: the later F3 induction/norm packaging consumes this
component estimate and the existing finite-dimensional tensor norm comparison. -/
theorem nablaRS_component_le_approx
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (X : ContMDiffSection I E (âˆž : WithTop â„•âˆž) (TangentSpace I : M -> Type _))
    (T : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r s)
    (Î² : (y : M) -> Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (V : Idx -> (y : M) -> TangentSpace I y)
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx)
    (hX_at : X x = basis (lower 0))
    (hÎ²_at : Î² x = Tensor0SBundle.basisTensor0S (I := I) basis upper)
    (hV_at : forall i : Idx, V i x = basis i)
    (hpairT : MDifferentiableAt I ð“˜(Real, Real)
      (fun y : M => (T y (Î² y)) (fun a : Fin s => V (lower a.succ) y)) x)
    (hpairÎ² : forall slots : Fin r -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Î² y (fun a : Fin r => V (slots a) y)) x)
    (hÎ²model : DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r x Î²)
      (Set.range I) (extChartAt I x x))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (ð•œ := Real) (I := I) x (V i))
        (Set.range I) (extChartAt I x x))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          (Module.finBasis Real E).coord j
            (TensorLieDeriv.tangentFieldModelInChart
              (ð•œ := Real) (I := I) x (V i) (extChartAt I x y))) x) :
    |Tensor0SBundle.componentRS (I := I) basis
        (Tensor0SBundle.nablaRSFun
            (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
            r s (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) X T x -
          Tensor0SBundle.nablaRSFun
            (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
            r s (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) X T x)
        upper (fun b : Fin s => lower b.succ)| <=
      Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s (T x))) := by
  let covh := LeviCivita.leviCivitaConnectionOfMetric (I := I) h
  let covg := LeviCivita.leviCivitaConnectionOfMetric (I := I) g
  have hcomp := Tensor0SBundle.componentRS_nablaRSFun_sub
    (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) covh covg X T Î² x basis V upper lower
    hX_at hÎ²_at hV_at hpairT hpairÎ² hÎ²model hV hVmodel hcoord
  have hconn :
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.nablaRSFun
              (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
              r s covh X T x -
            Tensor0SBundle.nablaRSFun
              (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
              r s covg X T x)
          upper (fun b : Fin s => lower b.succ) =
        Tensor0SBundle.connActComp
          (fun l i j =>
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
          upper lower := by
    calc
      Tensor0SBundle.componentRS (I := I) basis
          (Tensor0SBundle.nablaRSFun
              (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
              r s covh X T x -
            Tensor0SBundle.nablaRSFun
              (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
              r s covg X T x)
          upper (fun b : Fin s => lower b.succ)
          =
        (âˆ‘ a : Fin r, âˆ‘ k : Idx,
          basis.coord (upper a)
            (((CovariantDerivative.difference covh covg x) (basis k)) (basis (lower 0))) *
            Tensor0SBundle.componentRS (I := I) basis (T x) (Function.update upper a k)
              (fun b : Fin s => lower b.succ)) -
        (âˆ‘ b : Fin s, âˆ‘ k : Idx,
          basis.coord k
            (((CovariantDerivative.difference covh covg x) (basis (lower b.succ)))
              (basis (lower 0))) *
            Tensor0SBundle.componentRS (I := I) basis (T x) upper
              (Function.update (fun c : Fin s => lower c.succ) b k)) := hcomp
      _ =
        Tensor0SBundle.connActComp
          (fun l i j =>
            Tensor0SBundle.componentRS (I := I) basis
              (Tensor0SBundle.connectionDifferenceTensorAt (I := I) covh covg x)
              (fun _ : Fin 1 => l)
              (fun q : Fin 2 => if q = 0 then i else j))
          (fun upper' lower' =>
            Tensor0SBundle.componentRS (I := I) basis (T x) upper' lower')
          upper lower := by
          simp [Tensor0SBundle.connActComp, Tensor0SBundle.basisTensor0S_apply]
          rfl
  rw [hconn]
  exact connAct_le_approx
    (I := I) Happrox hx hp basis hinv (T x) upper lower

/-- F3c norm packaging at order one.

If every component of the covariant-derivative difference satisfies the
component estimate supplied by `nablaRS_component_le_approx`, then the full
pointwise mixed-tensor norm is bounded by the corresponding finite-dimensional
component-count factor.  This is the final finite-sum step in the `p = 1`
part of MSM135 Chapter 4, Lemma "Norms of covariant derivatives of tensors,
I"; producing the component bounds is handled by `nablaRS_component_le_approx`.
-/
theorem nablaRS_norm_le_approx_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      |Tensor0SBundle.componentRS (I := I) basis A upper lower| <=
        Tensor0SBundle.connActConst (Idx := Idx) r s
          ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
          (Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := h) (x := x) r s T))) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r (s + 1) A) <=
      Real.sqrt
        ((Fintype.card (Fin r -> Idx) : Real) *
          ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
            (Tensor0SBundle.connActConst (Idx := Idx) r s
              ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
              (Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := h) (x := x) r s T))) ^ 2)) := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hcoef_nonneg :
      0 <= (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps) := by
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) heps_nonneg)
  have hT_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hvalence_nonneg : 0 <= ((r + s : Nat) : Real) := by
    positivity
  have hcard_nonneg : 0 <= (Fintype.card Idx : Real) := by
    positivity
  have hB :
      0 <= Tensor0SBundle.connActConst (Idx := Idx) r s
        ((3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps))
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcard_nonneg (mul_nonneg hcoef_nonneg hT_nonneg))
  exact Tensor0SBundle.sqrt_normRS_le_comps
    (I := I) h x r (s + 1) basis hinv A hB hcomp

/-- Coefficient from the checked connection-difference estimate used in the
order-one F3 bounds. -/
def connDiffCoeff (eps : Real) : Real :=
  (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)

/-- Component-action bound with the connection-difference coefficient inserted. -/
def connActApproxBound
    (Idx : Type*) [Fintype Idx] (eps : Real) (r s : Nat) (Tnorm : Real) : Real :=
  Tensor0SBundle.connActConst (Idx := Idx) r s (connDiffCoeff eps) Tnorm

/-- The explicit `p = 1` error term in the `g` norm for the F3d assembly. -/
def nablaRSOneError
    (eps : Real)
    {g : SmoothRiemannianMetric I M}
    {Idx : Type*} [Fintype Idx]
    {x : M} (r s : Nat)
    (T : Tensor0SBundle.TensorRSSpace r s I x) : Real :=
  Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt ((1 + eps) ^ (r + s)) *
              Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := g) (x := x) r s T))) ^ 2))

/-- Component hypothesis consumed by the order-one F3 norm assembly. -/
def NablaDiffCompBound
    (eps : Real)
    {h : SmoothRiemannianMetric I M}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x) : Prop :=
  forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
    |Tensor0SBundle.componentRS (I := I) basis A upper lower| <=
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T))

set_option maxHeartbeats 600000 in
/-- The `|T|_h` component-error bound is dominated by the explicit F3d
`|T|_g` error factor. -/
theorem nablaRSOneError_hpart
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K)
    {Idx : Type*} [Fintype Idx]
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x) :
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt
              (Tensor0SBundle.normSqRS
                (I := I) (g := h) (x := x) r s T))) ^ 2)) <=
    Real.sqrt
      ((Fintype.card (Fin r -> Idx) : Real) *
        ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
          (connActApproxBound (Idx := Idx) eps r s
            (Real.sqrt ((1 + eps) ^ (r + s)) *
              Real.sqrt
                (Tensor0SBundle.normSqRS
                  (I := I) (g := g) (x := x) r s T))) ^ 2)) := by
  have hT_h_g :=
    Happrox.sqrt_normRS_upper (I := I) hx r s T
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hcoef_nonneg :
      0 <= connDiffCoeff eps := by
    unfold connDiffCoeff
    exact mul_nonneg (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) heps_nonneg)
  have hT_h_nonneg :
      0 <= Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := h) (x := x) r s T) :=
    Real.sqrt_nonneg _
  have hT_g_nonneg :
      0 <= Real.sqrt ((1 + eps) ^ (r + s)) *
        Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := g) (x := x) r s T) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hvalence_nonneg : 0 <= ((r + s : Nat) : Real) := by
    positivity
  have hcardIdx_nonneg : 0 <= (Fintype.card Idx : Real) := by
    positivity
  have hB_h_nonneg :
      0 <= connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcardIdx_nonneg (mul_nonneg hcoef_nonneg hT_h_nonneg))
  have hB_g_nonneg :
      0 <= connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_nonneg hvalence_nonneg
      (mul_nonneg hcardIdx_nonneg (mul_nonneg hcoef_nonneg hT_g_nonneg))
  have hB_le :
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T)) <=
      connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T)) := by
    unfold connActApproxBound Tensor0SBundle.connActConst
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hT_h_g hcoef_nonneg)
        hcardIdx_nonneg)
      hvalence_nonneg
  have hBsq_le :
      (connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt
          (Tensor0SBundle.normSqRS
            (I := I) (g := h) (x := x) r s T))) ^ 2 <=
      (connActApproxBound (Idx := Idx) eps r s
        (Real.sqrt ((1 + eps) ^ (r + s)) *
          Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s T))) ^ 2 :=
    (sq_le_sqâ‚€ hB_h_nonneg hB_g_nonneg).2 hB_le
  have hcardUpper_nonneg :
      0 <= (Fintype.card (Fin r -> Idx) : Real) := by
    positivity
  have hcardLower_nonneg :
      0 <= (Fintype.card (Fin (s + 1) -> Idx) : Real) := by
    positivity
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hBsq_le hcardLower_nonneg)
      hcardUpper_nonneg)

/-- Component-packaged derivative difference is bounded by the explicit F3d
error term in the `g` norm. -/
theorem nablaRSOneError_of_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (A : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : NablaDiffCompBound (I := I) (h := h) (Idx := Idx) eps basis T A) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) A) <=
      nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
  have hdiff_h :=
    nablaRS_norm_le_approx_comps
      (I := I) Happrox basis hinv T A
      (by
        intro upper lower
        simpa [NablaDiffCompBound, connActApproxBound, connDiffCoeff] using
          hcomp upper lower)
  have hdiff_g_h :=
    Tensor0SBundle.sqrt_normRS_lower_le_of_equiv
      (I := I) g h x r (s + 1) Happrox.uniform_equiv.1
      (Happrox.uniform_equiv.2 x hx) A
  have hdiff_h_g :=
    nablaRSOneError_hpart (I := I) (Idx := Idx) Happrox hx T
  calc
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) A)
        <= Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
            Real.sqrt
              (Tensor0SBundle.normSqRS
                (I := I) (g := h) (x := x) r (s + 1) A) :=
          hdiff_g_h
    _ <= Real.sqrt ((1 + eps) ^ (r + (s + 1))) *
            Real.sqrt
              ((Fintype.card (Fin r -> Idx) : Real) *
                ((Fintype.card (Fin (s + 1) -> Idx) : Real) *
                  (connActApproxBound (Idx := Idx) eps r s
                    (Real.sqrt
                      (Tensor0SBundle.normSqRS
                        (I := I) (g := h) (x := x) r s T))) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left hdiff_h (Real.sqrt_nonneg _)
    _ <= nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
          exact mul_le_mul_of_nonneg_left hdiff_h_g (Real.sqrt_nonneg _)

set_option maxHeartbeats 2000000 in
/-- F3d, order-one book-form norm inequality.

This is the algebraic assembly of the `p = 1` case of MSM135 Chapter 4,
Lemma "Norms of covariant derivatives of tensors, I": triangle inequality in
the `g` norm, the component estimate packaged by
`nablaRS_norm_le_approx_comps`, and the mixed-tensor norm comparison under the
`C^0` part of the approximate-isometry hypothesis.  The component hypothesis is
kept explicit so callers can supply it from `nablaRS_component_le_approx` with
their chosen local frame data. -/
theorem nablaRS_one_le_approx_comps
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basis (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSSpace r s I x)
    (nablaH nablaG : Tensor0SBundle.TensorRSSpace r (s + 1) I x)
    (hcomp : NablaDiffCompBound
      (I := I) (h := h) (Idx := Idx) eps basis T
      (Tensor0SBundle.metricSubRS
        (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG)) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) nablaG) <=
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1) nablaH) +
        nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T := by
  have htri :=
    Tensor0SBundle.sqrt_normRS_le_add_metricSub
      (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG
  have hdiff_g_bound :
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (Tensor0SBundle.metricSubRS
            (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG)) <=
        nablaRSOneError (I := I) (g := g) (Idx := Idx) eps r s T :=
    nablaRSOneError_of_comps
      (I := I) Happrox hx basis hinv T
      (Tensor0SBundle.metricSubRS
        (I := I) (g := g) (x := x) r (s + 1) nablaH nablaG) hcomp
  exact htri.trans (add_le_add_right hdiff_g_bound _)

/-- Total-derivative `p = 1` form of MSM135 Lemma "Norms of covariant
derivatives of tensors, I".

This is the checked base case in the natural total-covariant-derivative
language: supplied realizations of `nabla_h T` and `nabla_g T` satisfy the
book estimate with the zero-order connection-difference epsilon bound.  The
remaining higher-order Lemma 4.5 work is the iterated product-rule realization
for repeated `h`-derivatives of the connection-difference action. -/
theorem nablaRS_one_le_approx_total
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisG basisH : Module.Basis Idx Real (TangentSpace I x))
    (hinvG :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basisG (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hinvH :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basisH (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r s)
    (nablaH nablaG : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r (s + 1))
    (hrealH : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) T nablaH)
    (hrealG : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) T nablaG)
    (Î² : (Fin r -> Idx) -> (y : M) -> Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (Xfield : Idx ->
      ContMDiffSection I E (âˆž : WithTop â„•âˆž) (TangentSpace I : M -> Type _))
    (V : Idx -> (y : M) -> TangentSpace I y)
    (hX_at : forall i : Idx, Xfield i x = basisG i)
    (hÎ²_at : forall upper : Fin r -> Idx,
      Î² upper x = Tensor0SBundle.basisTensor0S (I := I) basisG upper)
    (hV_at : forall i : Idx, V i x = basisG i)
    (hpairT : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => (T y (Î² upper y)) (fun a : Fin s => V (lower a.succ) y)) x)
    (hpairÎ² : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Î² upper y (fun a : Fin r => V (slots a) y)) x)
    (hÎ²model : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r x (Î² upper))
      (Set.range I) (extChartAt I x x))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (ð•œ := Real) (I := I) x (V i))
        (Set.range I) (extChartAt I x x))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          (Module.finBasis Real E).coord j
            (TensorLieDeriv.tangentFieldModelInChart
              (ð•œ := Real) (I := I) x (V i) (extChartAt I x y))) x) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaG x)) <=
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaH x)) +
        eps * Tensor0SBundle.connActNormConst (Idx := Idx) r s 12
          (Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s (T x))) := by
  have heps_nonneg : 0 <= eps := by
    have hC := Happrox.uniform_equiv.1
    linarith
  have hA :
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) 1 2
          (Tensor0SBundle.connectionDifferenceTensorAt
            (I := I)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
            (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) x)) <=
        eps * 12 := by
    have hraw :=
      connDiff_le_eps_g
        (I := I) Happrox hx hp heps_lt basisH hinvH
    simpa [mul_comm] using hraw
  exact Tensor0SBundle.totalNablaNorm_bound
    (I := I) (M := M) (Idx := Idx) g
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) h)
    (LeviCivita.leviCivitaConnectionOfMetric (I := I) g)
    T nablaH nablaG hrealH hrealG Î² x basisG hinvG Xfield V
    hX_at hÎ²_at hV_at hpairT hpairÎ² hÎ²model hV hVmodel hcoord
    heps_nonneg hA le_rfl

/-- Book-facing first-order estimate in MSM135 Chapter 4, Lemma
"Norms of covariant derivatives of tensors, I".

This is the `r = 1` case of the induction, phrased as an HCG endpoint.  It
uses only the zero-order connection-difference estimate
`|Î“_g - Î“_h|_g <= C * eps`; derivatives of `Î“_g - Î“_h` belong to the later
higher-order producer. -/
theorem hcg_first_order_nabla_norm_estimate
    [IsManifold I ((âˆž : WithTop â„•âˆž) + 1) M]
    {K : Set M} {eps : Real} {p : Nat}
    {g h : SmoothRiemannianMetric I M}
    (Happrox : IsApproxIsometryOn (I := I) K eps p g h)
    {x : M} (hx : x âˆˆ K) (hp : 1 <= p) (heps_lt : eps < 1)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (basisG basisH : Module.Basis Idx Real (TangentSpace I x))
    (hinvG :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) g x basisG (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    (hinvH :
      Tensor0SBundle.MetricInverseInBasis
        (I := I) h x basisH (Tensor0SBundle.identityInvMetric (Idx := Idx)))
    {r s : Nat}
    (T : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r s)
    (nablaH nablaG : Tensor0SBundle.TensorRSField
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (âˆž : WithTop â„•âˆž)) r (s + 1))
    (hrealH : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) h) T nablaH)
    (hrealG : Tensor0SBundle.TotalNablaRSRealizes
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r s
      (LeviCivita.leviCivitaConnectionOfMetric (I := I) g) T nablaG)
    (Î² : (Fin r -> Idx) -> (y : M) -> Tensor0SBundle.Tensor0SSpace
      (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r y)
    (Xfield : Idx ->
      ContMDiffSection I E (âˆž : WithTop â„•âˆž) (TangentSpace I : M -> Type _))
    (V : Idx -> (y : M) -> TangentSpace I y)
    (hX_at : forall i : Idx, Xfield i x = basisG i)
    (hÎ²_at : forall upper : Fin r -> Idx,
      Î² upper x = Tensor0SBundle.basisTensor0S (I := I) basisG upper)
    (hV_at : forall i : Idx, V i x = basisG i)
    (hT_diff : forall upper : Fin r -> Idx, forall lower : Fin (s + 1) -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => (T y (Î² upper y)) (fun a : Fin s => V (lower a.succ) y)) x)
    (hÎ²_diff : forall upper : Fin r -> Idx, forall slots : Fin r -> Idx,
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M => Î² upper y (fun a : Fin r => V (slots a) y)) x)
    (hÎ²model : forall upper : Fin r -> Idx, DifferentiableWithinAt Real
      (TensorLieDeriv.tensor0SModelInChart
        (ð•œ := Real) (E := E) (H := H) (I := I) (M := M) r x (Î² upper))
      (Set.range I) (extChartAt I x x))
    (hV : forall i : Idx, MDiffAt (T% (V i)) x)
    (hVmodel : forall i : Idx,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart (ð•œ := Real) (I := I) x (V i))
        (Set.range I) (extChartAt I x x))
    (hcoord : forall i : Idx, forall j : Fin (Module.finrank Real E),
      MDifferentiableAt I ð“˜(Real, Real)
        (fun y : M =>
          (Module.finBasis Real E).coord j
            (TensorLieDeriv.tangentFieldModelInChart
              (ð•œ := Real) (I := I) x (V i) (extChartAt I x y))) x) :
    Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaG x)) <=
      Real.sqrt
        (Tensor0SBundle.normSqRS
          (I := I) (g := g) (x := x) r (s + 1)
          (nablaH x)) +
        eps * Tensor0SBundle.connActNormConst (Idx := Idx) r s 12
          (Real.sqrt
            (Tensor0SBundle.normSqRS
              (I := I) (g := g) (x := x) r s (T x))) := by
  exact
    nablaRS_one_le_approx_total
      (I := I) Happrox hx hp heps_lt basisG basisH hinvG hinvH
      T nablaH nablaG hrealH hrealG Î² Xfield V hX_at hÎ²_at hV_at
      hT_diff hÎ²_diff hÎ²model hV hVmodel hcoord

end FixedDomain

end HCGCompactness
end DifferentialGeometry
```
