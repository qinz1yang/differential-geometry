import DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothBridge

/-!
# Dirichlet variant of the variational Laplacian (with-boundary, half-space model)

For a closed Riemannian manifold-with-boundary `(M, g)` modelled on the
canonical Euclidean half-space `EuclideanHalfSpace n`, this file packages the
**Dirichlet** variant of the variational Laplacian's H¹ Hilbert completion,
its L² inclusion, and its resolvent.

## Construction

The Dirichlet domain `H¹₀(M)` is the closure (in the H¹ topology) of the
*compactly-interior-supported* smooth scalar functions on `M` — that is,
smooth functions whose topological support is contained in `I.interior M`.
This captures the Dirichlet boundary condition: every test function vanishes
on `∂M`.

In our completion-based setting, this is exactly the H¹ Hilbert completion
of `InteriorSmoothScalar g`, which we re-export here under Dirichlet-themed
names. The smooth bridge for these test functions is identical to the
interior-supported case (boundary terms vanish trivially).

## Re-exports

* `SmoothScalarDirichlet g`, `H1ComplDirichlet g`,
  `smoothToH1ComplDirichlet`, `H1ComplDirichletToLp`, `resolventDirichlet`,
  and `smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap`: aliased
  from the interior-supported infrastructure.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-- Local abbreviation for the canonical Euclidean half-space model. -/
private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

/-- The Dirichlet variant smooth scalar (interior-supported smooth real-valued
function on a closed manifold-with-boundary; equivalently a test function
with vanishing boundary trace). -/
abbrev SmoothScalarDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  InteriorSmoothScalar g

/-- The Dirichlet H¹₀ Hilbert completion. -/
abbrev H1ComplDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  H1ComplInterior g

/-- **Explicit definition of `H1ComplDirichlet g` as a Hausdorff completion.**

`H1ComplDirichlet g` is the Hausdorff completion of the pre-Hilbert space of
compactly-interior-supported smooth scalar functions on `M`, equipped with
the Riemannian H¹ inner product. By construction it is therefore the
H¹-closure of the test-function space, which is the standard definition of
`H¹₀(M)`. -/
theorem H1ComplDirichlet_eq_completion (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g = UniformSpace.Completion (SmoothScalarDirichlet g) := rfl

/-- The canonical embedding of Dirichlet smooth scalars into `H¹₀`. -/
noncomputable def smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g :=
  smoothToH1ComplInterior g

/-- **Density of test functions in `H¹₀(M)`.**

The image of the Dirichlet test-function space `SmoothScalarDirichlet g`
(compactly interior-supported smooth scalars) under the canonical embedding
is dense in `H1ComplDirichlet g`. This is the universal property of the
Hausdorff completion specialised to test functions. -/
theorem denseRange_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToH1ComplDirichlet g) := by
  change DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g)
  rw [show (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g → H1ComplDirichlet g) =
      ((↑) : SmoothScalarDirichlet g →
        UniformSpace.Completion (SmoothScalarDirichlet g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- The Dirichlet L² inclusion. -/
noncomputable def smoothToLpDirichlet (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpInterior g

/-- The Dirichlet H¹₀ → L² inclusion. -/
noncomputable def H1ComplDirichletToLp (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  H1ComplInteriorToLp g

@[simp] lemma H1ComplDirichletToLp_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : SmoothScalarDirichlet g) :
    H1ComplDirichletToLp g (smoothToH1ComplDirichlet g f) =
      smoothToLpDirichlet g f :=
  H1ComplInteriorToLp_smoothToH1ComplInterior g f

/-- The Dirichlet resolvent `(1 - Δ_g)⁻¹ : Lp ℝ 2 μ_g →L[ℝ] H1ComplDirichlet g`. -/
noncomputable def resolventDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  resolventInterior g

/-- Defining property of the Dirichlet resolvent. -/
theorem resolventDirichlet_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplDirichlet g) :
    ⟪resolventDirichlet g f, v⟫_ℝ = ⟪H1ComplDirichletToLp g v, f⟫_ℝ :=
  resolventInterior_inner_eq_lpFunctional g f v

/-- **Smooth bridge for the Dirichlet variant.** For an interior-supported
smooth scalar `u` (a Dirichlet test function), the H¹₀ lift solves the
variational equation: it equals the Dirichlet resolvent applied to the L²
class of `(u - Δ_g_with_boundary u)`. -/
theorem smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    smoothToH1ComplDirichlet g u = resolventDirichlet g u.oneSubLapClassicalLp :=
  smoothToH1ComplInterior_eq_resolventInterior_oneSubLap u

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  resolventDirichlet g

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
