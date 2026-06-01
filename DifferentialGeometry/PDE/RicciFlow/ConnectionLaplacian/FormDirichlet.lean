import DifferentialGeometry.PDE.RicciFlow.ConnectionLaplacian.L2PMap

/-!
# Dirichlet form associated to the connection Laplacian

For a closed Riemannian manifold `(M, g)`, the connection (rough)
Laplacian `Δ_∇` on `(r, s)`-tensor fields admits a natural Dirichlet
quadratic form

  𝓓(T, S) = ⟨∇T, ∇S⟩_{L²(M, g)}

on the smooth, compactly-supported sections `T, S : SmoothCcTensor g r s`.
By the divergence theorem on the closed manifold `M`, the form coincides
with the negative inner-product pairing of `Δ_∇ T` against `S`, i.e.

  𝓓(T, S) = -⟨Δ_∇ T, S⟩_{L²}.

We adopt this latter form as the working definition, packaged through the
partially-defined operator `connLaplacianL2` and the canonical inclusion
of every smooth compactly-supported representative into its domain
(`toL2_mem_connLaplacianL2_domain`).

## Main definitions

* `dirichletForm g r s` — the bilinear form
  `SmoothCcTensor g r s → SmoothCcTensor g r s → ℝ`, sending a pair
  `(T, S)` to `-⟪Δ_∇ T, S⟫_{L²(M, g)}`.

## Main results

* `dirichletForm_eq_neg_inner_laplacian` — the definitional identity
  connecting the form to the `L²` pairing against the rough Laplacian.

Symmetry and diagonal positivity require integration-by-parts for the
raw tensor connection Laplacian, which is not yet available in this
layer. Those results will be added when the IBP infrastructure lands.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace ConnectionLaplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- The **Dirichlet quadratic form** associated to the connection
Laplacian on `(r, s)`-tensor fields, defined on smooth compactly-supported
sections by the integration-by-parts expression

  𝓓(T, S) = -⟨Δ_∇ T, S⟩_{L²}.

By integration by parts on a closed manifold this equals
`⟨∇T, ∇S⟩_{L²(M, g)}`. The IBP identity itself awaits the tensor-valued
divergence-theorem infrastructure for the raw connection Laplacian. -/
def dirichletForm (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    SmoothCcTensor g r s → SmoothCcTensor g r s → ℝ :=
  fun T S => - (@inner ℝ _ _
      ((connLaplacianL2 (I := I) g r s)
        ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T,
          toL2_mem_connLaplacianL2_domain (I := I) g r s T⟩)
      (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S))

set_option linter.unusedSectionVars false in
/-- **Definitional identity.** The Dirichlet form equals the negative
`L²` pairing of the rough Laplacian `Δ_∇ T` against `S`,

  𝓓(T, S) = -⟨Δ_∇ T, S⟩_{L²}.

Holds by definition (with the membership witness `hT` identified by
`Prop`-proof-irrelevance with the canonical one). -/
theorem dirichletForm_eq_neg_inner_laplacian
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : SmoothCcTensor g r s)
    (hT : SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T ∈
      (connLaplacianL2 (I := I) g r s).domain) :
    dirichletForm (I := I) g r s T S =
      - (@inner ℝ _ _
          ((connLaplacianL2 (I := I) g r s)
            ⟨SmoothCcTensor.toL2 (g := g) (r := r) (s := s) T, hT⟩)
          (SmoothCcTensor.toL2 (g := g) (r := r) (s := s) S)) := by
  unfold dirichletForm
  rfl

end ConnectionLaplacian
end RicciFlow
end PDE
end DifferentialGeometry

end
