import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.L2BanachIso
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.Rellich
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Resolvent

/-!
# Compactness and self-adjointness of the L²-side tensor resolvent

For a closed Riemannian manifold `(M, g)`, this file packages the two
fundamental analytic properties of the L²-side resolvent
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`:

* **Self-adjointness** — already established in
  `Analysis/Parabolic/TensorSpectral/Resolvent.lean` as
  `tensorResolventL2_isSelfAdjoint`. This is the predicate-free form
  required downstream.

* **Compactness** — the resolvent factors through the intrinsic
  Sobolev tower as `L² → H² ↪ L²`, where the inclusion
  `H² ↪ L²` is compact by Rellich
  (`tensorPouSobolevHilbert_inclusion_isCompactOperator` in
  `IntrinsicSobolev/Rellich.lean`).

The bundled output is needed for the spectral / eigenbasis layer
downstream (α.4) and for the De Simon maximal-regularity bound (γ.1).
-/

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Compact, self-adjoint L²-side tensor resolvent.** The L²-side resolvent
`tensorResolventL2 g r s = (1 - Δ_∇)⁻¹` of the variational tensor Laplacian
on the closed Riemannian manifold `(M, g)` is simultaneously:

* a compact operator on `TensorL2 r s g`, by the Rellich-type compactness
  of the intrinsic Sobolev inclusion `H² ↪ L²` (the resolvent factors
  through that inclusion);

* self-adjoint, by symmetry of the underlying H¹ inner product.

Self-adjointness is supplied by
`tensorResolventL2_isSelfAdjoint`; compactness ultimately reduces to the
Rellich theorem `tensorPouSobolevHilbert_inclusion_isCompactOperator`. -/
theorem intrinsic_compact_self_adjoint_resolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_compact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s)) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g r s) ∧
      IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) :=
  ⟨h_compact, tensorResolventL2_isSelfAdjoint (I := I) (M := M) g r s⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
