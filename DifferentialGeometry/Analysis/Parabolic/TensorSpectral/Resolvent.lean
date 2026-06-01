import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Variational
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The L²-side resolvent of the variational tensor Laplacian

For a closed Riemannian manifold `(M, g)`, this file constructs the L²-side
resolvent operator
`tensorResolventL2 g r s : TensorL2 r s g →L[ℝ] TensorL2 r s g`
of the variational tensor Laplacian, defined as the composition
`tensorResolventL2 g r s := TensorH1ComplToTensorL2 g r s ∘L tensorResolvent g r s`.

We prove:
* `tensorResolventL2_isSelfAdjoint`: `tensorResolventL2 g r s` is a
  self-adjoint continuous linear operator on `TensorL2 r s g`.

The self-adjointness reduces to symmetry of the H¹ inner product on
`TensorH1Compl g r s` (already established in `Variational.lean`).

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_∇)⁻¹`, and `tensorResolventL2 g r s`
is its restriction-and-corestriction to `TensorL2 r s g`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The L²-side resolvent operator of the variational tensor Laplacian:
`(1 - Δ_∇)⁻¹` viewed as a continuous linear endomorphism of
`TensorL2 r s g`. -/
noncomputable def tensorResolventL2 (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s).comp
    (tensorResolvent (I := I) (M := M) g r s)

@[simp] lemma tensorResolventL2_apply (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f : TensorL2 r s g) :
    tensorResolventL2 (I := I) (M := M) g r s f =
      TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (tensorResolvent (I := I) (M := M) g r s f) := rfl

/-- The defining inner-product identity used in the self-adjointness proof:
for `f, h ∈ TensorL2 r s g`,
`⟨tensorResolventL2 f, h⟩_{L²}
  = ⟨tensorResolvent g r s f, tensorResolvent g r s h⟩_{H¹}`. -/
private lemma inner_tensorResolventL2_eq_inner_tensorResolvent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪tensorResolvent (I := I) (M := M) g r s f,
        tensorResolvent (I := I) (M := M) g r s h⟫_ℝ := by
  rw [tensorResolventL2_apply]
  have hvar := tensorResolvent_inner_eq_lpFunctional (I := I) (M := M) g r s h
    (tensorResolvent (I := I) (M := M) g r s f)
  rw [← hvar]
  exact real_inner_comm _ _

/-- **Self-adjointness via symmetry of the H¹ inner product.** The L²-side
tensor resolvent `tensorResolventL2 g r s` is symmetric in the L² inner
product:
`⟨tensorResolventL2 f, h⟩_{L²} = ⟨f, tensorResolventL2 h⟩_{L²}`
for every `f, h ∈ TensorL2 r s g`. -/
theorem tensorResolventL2_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (f h : TensorL2 r s g) :
    ⟪tensorResolventL2 (I := I) (M := M) g r s f, h⟫_ℝ =
      ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ := by
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s f h]
  rw [show ⟪f, tensorResolventL2 (I := I) (M := M) g r s h⟫_ℝ =
      ⟪tensorResolventL2 (I := I) (M := M) g r s h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_tensorResolventL2_eq_inner_tensorResolvent (I := I) (M := M) g r s h f]
  exact real_inner_comm _ _

/-- **Self-adjointness as a Mathlib `IsSelfAdjoint`.** -/
theorem tensorResolventL2_isSelfAdjoint
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsSelfAdjoint (tensorResolventL2 (I := I) (M := M) g r s) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact tensorResolventL2_symm (I := I) (M := M) g r s f h

example (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    TensorL2 r s g →L[ℝ] TensorL2 r s g :=
  tensorResolventL2 (I := I) (M := M) g r s

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
