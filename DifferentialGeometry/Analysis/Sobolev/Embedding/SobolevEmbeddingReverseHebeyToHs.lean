import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebey
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace

/-!
# The reverse Hebey-Sobolev bridge in intrinsic `toHs`-norm form

The companion file `SobolevEmbeddingReverseHebey` proves the reverse Hebey-Sobolev
comparison phrased through the partition-of-unity-weighted chart-Sobolev seminorm
`tensorPouSobolevHsNorm`. This file re-states the very same bound through the norm of the
intrinsic `H^k` Hilbert space embedding `SmoothCcTensor.toHs`, using the on-disk identity
`tensorPouSobolevHilbert_norm_eq` (`‖T.toHs k‖ = (tensorPouSobolevHsNorm g k T).toReal`):

  `‖T.toHs k‖ ≤ C · ∑_{j ∈ range (2k + 1)} tensorL2Norm g r (s + j) (∇^j T).toFun`.

The order-`2k` intrinsic chart-Sobolev (`H^k`) norm of a smooth compactly-supported
`(r, s)`-tensor section `T` is dominated, by a single per-`(g, r, s, k)` constant, by the
covariant-jet `L²` data of `T`: the sum, over the finite range `j ≤ 2k`, of the intrinsic
metric `L²` norms of the iterated covariant gradients `∇^j T` (each at its own valence
`(r, s + j)`). It is the missing direction of the classical chart-Sobolev ≅ covariant-Sobolev
equivalence on a closed manifold, phrased in the Hilbert-space norm in which downstream
quasilinear Nemytskii estimates are stated.

No supercriticality or dimension hypothesis is needed: the comparison is the pure
Christoffel-controlled chart-vs-covariant norm equivalence, valid for every order `k` on a
closed manifold (the finite partition of unity / atlas supplies uniform Christoffel-jet
constants). The dependence on the order is the finite covariant-jet range `j ≤ 2k` together
with the single comparison constant `C`.

## Main result

* `exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum` — the reverse Hebey-Sobolev bridge
  in `toHs`-norm form, at general `(r, s)` valence and arbitrary order `k`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The reverse Hebey-Sobolev bridge in intrinsic `toHs`-norm form.** There is a
non-negative constant `C` (depending only on `(g, r, s, k)`) such that for every smooth
compactly-supported `(r, s)`-tensor section `T`, the norm of its order-`k` intrinsic
chart-Sobolev (`H^k`) Hilbert-space embedding is controlled by the sum, over `j ≤ 2k`, of the
intrinsic metric `L²` norms of the iterated covariant gradients `∇^j T`:
`‖T.toHs k‖ ≤ C · ∑_{j ∈ range (2k + 1)} tensorL2Norm g r (s + j) (iteratedCovGrad g r s j T).toFun`.

This is the `toHs`-norm form of `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum`
(the same bound through the chart-Sobolev seminorm), obtained by rewriting `‖T.toHs k‖` as
`(tensorPouSobolevHsNorm g k T).toReal` via `tensorPouSobolevHilbert_norm_eq`. The finite
covariant-jet order `j ≤ 2k` and the single comparison constant carry the order dependence; no
supercriticality or dimension hypothesis is required (a closed manifold supplies uniform
Christoffel-jet constants over its finite atlas). -/
theorem exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        ‖IntrinsicSobolev.SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g r (s + j)
              (iteratedCovGrad g r s j T).toFun := by
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
      (I := I) (M := M) g r s k
  refine ⟨C, hC_nn, fun T => ?_⟩
  rw [IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq]
  exact hC T

end DifferentialGeometry.PDE.RicciFlow

end
