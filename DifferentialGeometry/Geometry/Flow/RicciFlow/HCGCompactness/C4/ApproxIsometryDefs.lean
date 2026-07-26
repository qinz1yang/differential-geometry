import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Metric.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.Unit
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Approximate-isometry definitions (MSM135 Chapter 4 interface)

The green, durable *interface* of the (formerly broken) `ApproximateIsometry.lean`
monolith: the book-facing approximate-isometry data structures (MSM135 Def 4.1),
the same-domain comparison predicates the F-track consumes, the realized
connection-difference vocabulary, and the dimension constants.

Extracted 2026-06-11 from `ApproximateIsometry.lean` (a never-green 5769-line
file; its broken F1/F3 norm-comparison proofs are archived in
`ApproximateIsometryArchive.md`).  Two mechanical revivals were applied to the
realized-derivative defs: `LeviCivita.leviCivitaConnectionOfMetric` →
`Integral.Connection.leviCivitaConnectionOfMetric` (project-wide rename) and
`Tensor0SBundle.fieldNormRS` (never ported) → `√ Tensor0SBundle.normSqRS …`
(its definitional meaning).  The `connActConst`-dependent error defs
(`connActApproxBound`, `nablaRSOneError`, `NablaDiffCompBound`) are NOT here:
they depend on the unported `connActConst` and remain in the archive.
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
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-! ## ① Book-facing approximate-isometry data (MSM135 Definition 4.1) -/

section MapLevel

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [T2Space N] [IsManifold I ∞ N] [SigmaCompactSpace N]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]

/-- Concrete pullback metric tensor data for a smooth map.

For a general smooth map this is not packaged as a Riemannian metric: it is the
actual covariant `(0,2)` tensor whose value is
`h_{Phi x}(d Phi_x -, d Phi_x -)`.  The smooth tensor field is supplied as data,
and the formula field pins it to the map. -/
structure PullbackMetricTensorData
    (Phi : M -> N) (h : SmoothRiemannianMetric I N) where
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))

/-- The pointwise norm of the metric-error tensor `A - g`, measured by `g`. -/
noncomputable def metricTensorErrorNorm
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
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
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (gRef : SmoothRiemannianMetric I M) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A
    (fun a Aprev =>
      metricCovDerivStep (I := I) gRef a Aprev)

/-- Pointwise norm `|nabla_cov^a A|_norm` for a smooth `(0,2)` tensor field. -/
noncomputable def tensor02CovDerivNormWith
    (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
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
  smooth : ContMDiff I I (∞ : WithTop ℕ∞) Phi
  pullbackData : PullbackMetricTensorData (I := I) Phi h
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullbackData.pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullbackData.pullback g g x <= eps

/-- MSM135 Definition 4.1, localized two-sided data for diffeomorphisms.

The forward field is the pre-approximate isometry on the source set.  The
reverse field is the same condition for the inverse map on the target set.

WARNING (`lbl397` role): this carrier takes a **global** diffeomorphism
`M ≃ₘ N`.  The Chapter 4 comparison maps `F_{kℓ;r}` are diffeomorphisms of a
ball onto an image (`lbl397`), and members of a bounded-geometry sequence need
not be globally diffeomorphic — use `BookApproxIsoPartialData` below for the
`lbl397`/Step B/C role.  This global form remains correct for genuinely total
maps (e.g. the `lbl374` isometry limits). -/
structure BookApproxIsometryData
    (K : Set M) (L : Set N) (eps : Real) (p : Nat)
    (Phi : M ≃ₘ⟮I, I⟯ N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  forward : PreApproxIsometryData (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsometryData (I := I) L eps p (Phi.symm : N -> M) h g

/-- MSM135 Definition 4.1 localized to `K`, for a map that is only smooth near `K`
(the coercion of a partial diffeomorphism).  Unlike `PreApproxIsometryData`, the
smoothness is `ContMDiffOn … K` and the pullback `(0,2)` tensor field is pinned to
the map **on `K` only** — off `K` the supplied smooth field is unconstrained
extension data (a general partial map has junk values there, so a global
`pullback_apply` is unsatisfiable). -/
structure PreApproxIsoDataOn
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= eps
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= eps

/-- **MSM135 Proposition `lbl397` carrier** — two-sided `(eps, p)` approximate-isometry
data for a **partial** diffeomorphism, witnessed on `K ⊆ Phi.source` and its image
`Phi '' K`.  The book's `F_{kℓ;r} : B(O_k, r) → F_{kℓ;r}(B(O_k, r)) ⊆ M_ℓ` is a
diffeomorphism of a ball onto its image, never a global map: sequence members of a
bounded-geometry sequence can have different topologies, so the global-`Diffeomorph`
carrier `BookApproxIsometryData` is unprovable in this role. -/
structure BookApproxIsoPartialData
    (K : Set M) (eps : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : PreApproxIsoDataOn (I := I) K eps p (Phi : M -> N) g h
  reverse : PreApproxIsoDataOn (I := I) ((Phi : M -> N) '' K) eps p (Phi.symm : N -> M) h g

/-- Partial-map pre-approximate-isometry data with separate `C^0` and higher
covariant-derivative tolerances.

This is a D1b-facing bookkeeping carrier.  It keeps the supplied pullback field,
smoothness, and pointwise formulas from `PreApproxIsoDataOn`, but does not force
the tensor-error and covariant-derivative bounds to share one book epsilon. -/
structure PreApproxIsoSep
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : M -> N)
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  c0_nonneg : 0 <= c0
  cov_nonneg : 0 <= cov
  smoothOn : ContMDiffOn I I (∞ : WithTop ℕ∞) Phi K
  pullback :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2
  pullback_apply :
    forall x : M, x ∈ K -> forall v : Fin 2 -> TangentSpace I x,
      pullback x v =
        h.inner (Phi x)
          (mfderiv I I Phi x (v 0))
          (mfderiv I I Phi x (v 1))
  c0_small :
    forall x : M, x ∈ K ->
      metricTensorErrorNorm (I := I) pullback g x <= c0
  cov_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        tensor02CovDerivNormWith (I := I) a pullback g g x <= cov

/-- Wrap separated partial-map data into the book carrier once both ledgers fit
under the requested book epsilon. -/
def PreApproxIsoSep.toBook
    {K : Set M} {c0 cov eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    PreApproxIsoDataOn (I := I) K eps p Phi g h where
  eps_pos := heps0
  eps_lt_one := heps1
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := fun x hx => le_trans (D.c0_small x hx) hc0
  cov_deriv_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x hx) hcov

/-- Two-sided partial-map separated data for a partial diffeomorphism. -/
structure BookApproxIsoSep
    (K : Set M) (c0 cov : Real) (p : Nat)
    (Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric I N) where
  source_sub : K ⊆ Phi.source
  forward : PreApproxIsoSep (I := I) K c0 cov p (Phi : M -> N) g h
  reverse : PreApproxIsoSep (I := I) ((Phi : M -> N) '' K) c0 cov p (Phi.symm : N -> M) h g

/-- Wrap two-sided separated partial data into `BookApproxIsoPartialData` once
both ledgers fit under the requested book epsilon. -/
def BookApproxIsoSep.toBook
    {K : Set M} {c0 cov eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoSep (I := I) K c0 cov p Phi g h)
    (heps0 : 0 < eps) (heps1 : eps < 1)
    (hc0 : c0 <= eps) (hcov : cov <= eps) :
    BookApproxIsoPartialData (I := I) K eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toBook heps0 heps1 hc0 hcov
  reverse := D.reverse.toBook heps0 heps1 hc0 hcov

/-- Regard ordinary book pre-data as separated data with equal `C^0` and covariant
ledgers. -/
def PreApproxIsoDataOn.toSep
    {K : Set M} {eps : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoDataOn (I := I) K eps p Phi g h) :
    PreApproxIsoSep (I := I) K eps eps p Phi g h where
  c0_nonneg := le_of_lt D.eps_pos
  cov_nonneg := le_of_lt D.eps_pos
  smoothOn := D.smoothOn
  pullback := D.pullback
  pullback_apply := D.pullback_apply
  c0_small := D.c0_small
  cov_small := D.cov_deriv_small

/-- Regard ordinary book partial data as separated data with equal `C^0` and
covariant ledgers. -/
def BookApproxIsoPartialData.toSep
    {K : Set M} {eps : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoPartialData (I := I) K eps p Phi g h) :
    BookApproxIsoSep (I := I) K eps eps p Phi g h where
  source_sub := D.source_sub
  forward := D.forward.toSep
  reverse := D.reverse.toSep

/-- Separated pre-data is monotone in the zone and in both ledgers. -/
def PreApproxIsoSep.mono
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat} {Phi : M -> N}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : PreApproxIsoSep (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    PreApproxIsoSep (I := I) K' c0' cov' p Phi g h where
  c0_nonneg := le_trans D.c0_nonneg hc0
  cov_nonneg := le_trans D.cov_nonneg hcov
  smoothOn := D.smoothOn.mono hK
  pullback := D.pullback
  pullback_apply := fun x hx v => D.pullback_apply x (hK hx) v
  c0_small := fun x hx => le_trans (D.c0_small x (hK hx)) hc0
  cov_small := fun a h1 h2 x hx =>
    le_trans (D.cov_small a h1 h2 x (hK hx)) hcov

/-- Two-sided separated partial data is monotone in the zone and both ledgers. -/
def BookApproxIsoSep.mono
    {K K' : Set M} {c0 c0' cov cov' : Real} {p : Nat}
    {Phi : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (D : BookApproxIsoSep (I := I) K c0 cov p Phi g h)
    (hK : K' ⊆ K) (hc0 : c0 <= c0') (hcov : cov <= cov') :
    BookApproxIsoSep (I := I) K' c0' cov' p Phi g h where
  source_sub := fun _ hx => D.source_sub (hK hx)
  forward := D.forward.mono hK hc0 hcov
  reverse := D.reverse.mono (Set.image_mono hK) hc0 hcov

end MapLevel

/-! ## ② Same-domain approximate-isometry predicates -/

/-- Same-domain version of the MSM135 Chapter 4 approximate-isometry hypotheses.

The map-level pullback metric has already been constructed and its `C^0` tensor
error converted into vector metric equivalence.  Higher-order F3 estimates use
`IsTwoSidedApproxIsometryOn`, which also records the inverse-side derivative
smallness. -/
structure IsApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  uniform_equiv : MetricUniformEquivalentOn (I := I) K g h (1 + eps)
  cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
        metricCovDerivNorm (I := I) a h g x <= eps

/-- Same-domain version of the two-sided approximate-isometry hypotheses in
MSM135 Chapter 4. -/
structure IsTwoSidedApproxIsometryOn
    (K : Set M) (eps : Real) (p : Nat)
    (g h : SmoothRiemannianMetric I M) : Prop where
  forward : IsApproxIsometryOn (I := I) K eps p g h
  reverse_cov_deriv_small :
    forall a : Nat, 1 <= a -> a <= p ->
      forall x : M, x ∈ K ->
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

/-! ## Realized connection-difference vocabulary

`fieldNormRS` (never ported) is replaced by its definitional meaning
`√ normSqRS …`; the connection is the project-canonical
`Integral.Connection.leviCivitaConnectionOfMetric`. -/

/-- A supplied mixed tensor field realizes the connection-difference tensor
`Gamma_g - Gamma_h`. -/
def ConnDiffFieldRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M)
    (D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2) : Prop :=
  forall x : M,
    D x =
      Tensor0SBundle.connectionDifferenceTensorAt
        (I := I)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) g)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h) x

/-- Pointwise `g`-norm of a supplied `k`-th `h`-covariant derivative of the
connection-difference tensor. -/
noncomputable def connDiffDerivNorm
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2))
    (x : M) : Real :=
  Real.sqrt
    (Tensor0SBundle.normSqRS (I := I) (g := g) (x := x) 1 (k + 2) (Dk x))

/-- A supplied mixed tensor field realizes the `k`-th `h`-covariant derivative
of `Gamma_g - Gamma_h`, the orientation used in MSM135 Chapter 4. -/
def ConnDiffDerivRealizes
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g h : SmoothRiemannianMetric I M) (k : Nat)
    (Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2)) : Prop :=
  exists D : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2,
    ConnDiffFieldRealizes (I := I) g h D ∧
      Tensor0SBundle.HigherCovDerivRSRealizes
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) h) D k Dk

/-! ## ③ Bound predicates and dimension constants -/

/-- Uniform bound on the `g`-norm of a realized `k`-th connection-difference
derivative on `K`. -/
def ConnDiffDerivBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) :
    Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C

/-- Book-facing F3-hi epsilon control for a realized `k`-th `h`-covariant
derivative of `Gamma_g - Gamma_h`. -/
def ConnDiffEpsBoundOn
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (k : Nat) (C : Real) : Prop :=
  forall Dk : Tensor0SBundle.TensorRSField
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 (k + 2),
    ConnDiffDerivRealizes (I := I) g h k Dk ->
      forall x : M, x ∈ K ->
        connDiffDerivNorm (I := I) g k Dk x <= C * eps

/-- Uniform book-facing F3-hi epsilon controls for all orders below `m`. -/
def ConnDiffEpsBoundsBelow
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (K : Set M) (eps : Real)
    (g h : SmoothRiemannianMetric I M) (m : Nat)
    (C : Nat -> Real) : Prop :=
  forall k : Nat, k < m ->
    ConnDiffEpsBoundOn (I := I) K eps g h k (C k)

/-- A coarse dimension constant for the first positive-order
connection-difference epsilon estimate in a finite index frame. -/
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

/-- The connection-difference coefficient (book eq. 3.7/3.8 factor). -/
def connDiffCoeff (eps : Real) : Real :=
  (3 / 2 : Real) * (Real.sqrt ((1 + eps) ^ 3) * eps)

end FixedDomain

end HCGCompactness
end DifferentialGeometry
