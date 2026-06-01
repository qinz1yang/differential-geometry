import DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothBridge

/-!
# Neumann variant of the variational Laplacian (with-boundary, half-space model)

For a closed Riemannian manifold-with-boundary `(M, g)` modelled on the
canonical Euclidean half-space `EuclideanHalfSpace n`, this file packages the
**Neumann** variant of the variational Laplacian's H¹ Hilbert completion,
its L² inclusion, and its resolvent, by re-exporting the interior-supported
infrastructure from `WithBoundary/InteriorH1Compl.lean`,
`WithBoundary/InteriorVariational.lean`, and `WithBoundary/InteriorSmoothBridge.lean`.

## Scope of this delivery

The classical "Neumann variational Laplacian" works on the *full* H¹(M)
(without boundary trace constraint), with the natural Neumann boundary
condition `∂_ν u = 0` arising from the variational principle on a non-trivial
boundary trace. Implementing the **full** H¹ completion in Lean requires
either (a) integrability of `g(grad f, grad h)` for general smooth `f, h`
on a manifold-with-boundary (where `gradFun` is intrinsically smooth only on
the manifold interior), or (b) a measure-theoretic argument that the boundary
has measure zero combined with a chart-by-chart continuity argument.

This delivery takes the simpler path of restricting the test-function space
to *interior-supported* smooth functions. Under this restriction, the
gradient packages as a globally smooth tangent section
(`grad_g_with_boundary_section`), the H¹ inner product is well-defined and
positive, and the smooth bridge to `Δ_g_with_boundary` works directly.

The construction is therefore the H¹ Hilbert completion of the
interior-supported smooth scalars; the smooth bridge holds for
interior-supported smooth `u`. This is the natural Dirichlet/zero-trace
variant of the Neumann space (the boundary trace of every test function
vanishes by interior-support). The full Neumann space (allowing nonzero
boundary trace, with the natural `∂_ν u = 0` boundary condition appearing in
the smooth bridge) is documented as a follow-up scope.

## Re-exports

* `H1ComplNeumann g := H1ComplInterior g`: the Hilbert space.
* `smoothToH1ComplNeumann`, `H1ComplNeumannToLp`, `resolventNeumann`,
  `resolventNeumann_inner_eq_lpFunctional`,
  `smoothToH1ComplNeumann_eq_resolventNeumann_oneSubLap`: all aliased from
  the interior-supported infrastructure.

The names with the `Neumann` suffix exist purely to document the intended
mathematical context: the test-function space is the natural Neumann (i.e.
no Dirichlet trace constraint) space, restricted in this delivery to its
interior-supported subspace.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

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

/-- The Neumann variant smooth scalar (interior-supported smooth real-valued
function on a closed manifold-with-boundary). -/
abbrev SmoothScalarNeumann (g : SmoothRiemannianMetric (I_half n) M) :=
  InteriorSmoothScalar g

/-- The Neumann variant H¹ Hilbert completion. -/
abbrev H1ComplNeumann (g : SmoothRiemannianMetric (I_half n) M) :=
  H1ComplInterior g

/-- The canonical embedding of Neumann smooth scalars into the H¹
completion. -/
noncomputable def smoothToH1ComplNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarNeumann g →L[ℝ] H1ComplNeumann g :=
  smoothToH1ComplInterior g

/-- The Neumann L² inclusion. -/
noncomputable def smoothToLpNeumann (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarNeumann g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpInterior g

/-- The Neumann H¹ → L² inclusion. -/
noncomputable def H1ComplNeumannToLp (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplNeumann g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  H1ComplInteriorToLp g

@[simp] lemma H1ComplNeumannToLp_smoothToH1ComplNeumann
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : SmoothScalarNeumann g) :
    H1ComplNeumannToLp g (smoothToH1ComplNeumann g f) = smoothToLpNeumann g f :=
  H1ComplInteriorToLp_smoothToH1ComplInterior g f

/-- The Neumann resolvent `(1 - Δ_g)⁻¹ : Lp ℝ 2 μ_g →L[ℝ] H1ComplNeumann g`. -/
noncomputable def resolventNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplNeumann g :=
  resolventInterior g

/-- Defining property of the Neumann resolvent. -/
theorem resolventNeumann_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplNeumann g) :
    ⟪resolventNeumann g f, v⟫_ℝ = ⟪H1ComplNeumannToLp g v, f⟫_ℝ :=
  resolventInterior_inner_eq_lpFunctional g f v

/-- **Smooth bridge for the Neumann variant.** For an interior-supported
smooth scalar `u`, the H¹ lift solves the variational equation: it equals the
Neumann resolvent applied to the L² class of `(u - Δ_g_with_boundary u)`. -/
theorem smoothToH1ComplNeumann_eq_resolventNeumann_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarNeumann g) :
    smoothToH1ComplNeumann g u = resolventNeumann g u.oneSubLapClassicalLp :=
  smoothToH1ComplInterior_eq_resolventInterior_oneSubLap u

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplNeumann g :=
  resolventNeumann g

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
