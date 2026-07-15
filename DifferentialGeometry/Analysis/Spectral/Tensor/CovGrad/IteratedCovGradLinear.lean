import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm

/-! # `ℝ`-linearity of the iterated covariant gradient

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
single-step section-level covariant gradient `covGrad g r s` is `ℝ`-linear in its section
(`covGrad_add`, `covGrad_smul`, `covGrad_zero`).  This file propagates that linearity through the
iteration `iteratedCovGrad g r s j` (the `j`-fold covariant gradient, an `(r, s + j)`-tensor),
recording its additivity, negation and subtraction in the section.

These are the elementary algebraic identities of the covariant calculus: the `j`-fold covariant
gradient is built by `iteratedCovGrad_succ` as `covGrad` of the `(j-1)`-fold gradient, so an
induction on `j` carries the single-step linearity at the changing rank `s + j` up to every order.
They are the structural building blocks every higher-order covariant-jet estimate needs (e.g. to
split the covariant jet of a tensor *difference* into the difference of covariant jets), liberated
to the covariant-calculus layer as first-class API rather than re-derived per consumer. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- The single-step covariant gradient negates with the section: `∇(-w) = -∇w`.  This is
`covGrad_smul` at the scalar `-1`, after `neg_one_smul`. -/
theorem covGrad_neg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (-w) = -covGrad g r s w := by
  rw [← neg_one_smul ℝ w, covGrad_smul, neg_one_smul]

/-- The single-step covariant gradient distributes over subtraction:
`∇(w₁ - w₂) = ∇w₁ - ∇w₂`.  This combines `covGrad_add` with `covGrad_neg`. -/
theorem covGrad_sub (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    covGrad g r s (w₁ - w₂) = covGrad g r s w₁ - covGrad g r s w₂ := by
  rw [sub_eq_add_neg, covGrad_add, covGrad_neg, sub_eq_add_neg]

/-- **The iterated covariant gradient is additive in the section.**  For every gradient order `j`,
`∇^j (w₁ + w₂) = ∇^j w₁ + ∇^j w₂`.  Proven by induction on `j`: the base case is
`iteratedCovGrad_zero`, and the successor step rewrites `∇^{j+1}` as `∇(∇^j ·)`
(`iteratedCovGrad_succ`), applies the induction hypothesis, and distributes the single-step
gradient over the sum (`covGrad_add`). -/
theorem iteratedCovGrad_add (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ + w₂)
      = iteratedCovGrad g r s j w₁ + iteratedCovGrad g r s j w₂ := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_add]

/-- **The iterated covariant gradient negates with the section.**  For every gradient order `j`,
`∇^j (-w) = -∇^j w`.  Proven by induction on `j` from `iteratedCovGrad_zero`, `iteratedCovGrad_succ`
and `covGrad_neg`. -/
theorem iteratedCovGrad_neg (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (-w) = -iteratedCovGrad g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_neg]

/-- **The iterated covariant gradient distributes over subtraction.**  For every gradient order `j`,
`∇^j (w₁ - w₂) = ∇^j w₁ - ∇^j w₂`.  This combines `iteratedCovGrad_add` with
`iteratedCovGrad_neg`; it is the order-`j` covariant-jet analogue of `rawTensorConnLapSmooth_sub`,
the identity that splits the covariant jet of a tensor difference into the difference of covariant
jets. -/
theorem iteratedCovGrad_sub (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (w₁ w₂ : Integral.L2.SmoothCcTensor g r s) :
    iteratedCovGrad g r s j (w₁ - w₂)
      = iteratedCovGrad g r s j w₁ - iteratedCovGrad g r s j w₂ := by
  rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, sub_eq_add_neg]

end RicciFlow
end PDE
end DifferentialGeometry

end
