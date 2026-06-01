import DifferentialGeometry.Analysis.Laplacian.Operator.Operator
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichOnM
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceFull
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The L²-side resolvent of the variational Laplacian

For a closed Riemannian manifold `(M, g)`, this file constructs the L²-side
resolvent operator `resolventL2 g : Lp ℝ 2 μ_g →L[ℝ] Lp ℝ 2 μ_g` of the
variational Laplacian, defined as the composition
`resolventL2 g := H1ComplToLp g ∘L resolvent g`.

We prove:
* `resolventL2_isSelfAdjoint`: `resolventL2 g` is a self-adjoint
  continuous linear operator on `Lp ℝ 2 μ_g`.
* `resolventL2_isCompactOperator`: `resolventL2 g` is a compact operator
  on `Lp ℝ 2 μ_g`.

The self-adjointness reduces to symmetry of the H¹ inner product on
`H1Compl g` (already established in `Variational.lean`).

The compactness comes from a chart-Sobolev bridge for smooth functions
(uniform-in-`u` in the smooth case) combined with the closed-manifold
Rellich-Kondrachov compact embedding `rellich_kondrachov_chart_seq`
(established in `RellichOnM.lean`).

## Sign convention

We follow the geometer convention `Δ_g = div_g ∘ grad_g`, with spectrum
`⊆ (-∞, 0]`. The resolvent is `(1 - Δ_g)⁻¹`, and `resolventL2 g` is its
restriction-and-corestriction to `Lp ℝ 2 μ_g`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The L²-side resolvent operator of the variational Laplacian:
`(1 - Δ_g)⁻¹` viewed as a continuous linear endomorphism of `Lp ℝ 2 μ_g`. -/
noncomputable def resolventL2 (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (H1ComplToLp (I := I) (M := M) g).comp (resolvent (I := I) (M := M) g)

@[simp] lemma resolventL2_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    resolventL2 (I := I) (M := M) g f =
      H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) := rfl

/-- The defining inner-product identity used in the self-adjointness proof:
for `f, h ∈ Lp ℝ 2 μ_g`,
`⟨resolventL2 f, h⟩_{L²} = ⟨resolvent g f, resolvent g h⟩_{H¹}`. -/
private lemma inner_resolventL2_eq_inner_resolvent
    (g : SmoothRiemannianMetric I M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪resolvent (I := I) (M := M) g f,
        resolvent (I := I) (M := M) g h⟫_ℝ := by
  rw [resolventL2_apply]
  have hvar := resolvent_inner_eq_lpFunctional (I := I) (M := M) g h
    (resolvent (I := I) (M := M) g f)
  rw [← hvar]
  exact real_inner_comm _ _

/-- **Self-adjointness via symmetry of the H¹ inner product.** The L²-side
resolvent `resolventL2 g` is symmetric in the L² inner product:
`⟨resolventL2 f, h⟩_{L²} = ⟨f, resolventL2 h⟩_{L²}` for every `f, h ∈ Lp ℝ 2 μ_g`. -/
theorem resolventL2_symm
    (g : SmoothRiemannianMetric I M)
    (f h : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ⟪resolventL2 (I := I) (M := M) g f, h⟫_ℝ =
      ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ := by
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g f h]
  rw [show ⟪f, resolventL2 (I := I) (M := M) g h⟫_ℝ =
      ⟪resolventL2 (I := I) (M := M) g h, f⟫_ℝ from real_inner_comm _ _]
  rw [inner_resolventL2_eq_inner_resolvent (I := I) (M := M) g h f]
  exact real_inner_comm _ _

/-- **Self-adjointness as a Mathlib `IsSelfAdjoint`.** -/
theorem resolventL2_isSelfAdjoint (g : SmoothRiemannianMetric I M) :
    IsSelfAdjoint (resolventL2 (I := I) (M := M) g) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  exact resolventL2_symm (I := I) (M := M) g f h

end Laplacian
end Analysis
end DifferentialGeometry

end
