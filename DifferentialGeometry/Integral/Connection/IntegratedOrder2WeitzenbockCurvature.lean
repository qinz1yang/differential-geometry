import DifferentialGeometry.Integral.Connection.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Integral.Connection.TensorRicciCommutator
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpHigherRankParseval

/-!
# The curvature characterisation of the order-`2` commutator defect

This file records the **curvature characterisation** of the rough-Laplacian /
covariant-gradient commutator defect `Curv = Δ_∇(∇S) − ∇(Δ_∇ S)` appearing in the
integrated order-`2` Weitzenböck identity `weitzenbock_integrated_covGrad_l2_normSq`.

Fibrewise, `Curv` is a sum of genuine curvature contractions `R_x(B_i, ·)(∇S)` —
both differentiation directions being honest frame / coordinate vector fields
(never the gradient slot read pointwise), so the bundled Ricci identity
`tensorSecondCovDeriv_antisymm_eq_riemannOp` applies directly to the gradient
field `∇S = covGrad g 0 s S`. The fibre norm of each such contraction is
controlled by the per-point curvature constant times the fibre norm of `∇S`; over
a closed manifold this is `‖R‖_∞ · rfns(∇S)`.

## Main results

* `secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen` — the Ricci identity on the
  gradient field at arbitrary covariant rank:
  `∇²_{X, Y}(∇S)(x) − ∇²_{Y, X}(∇S)(x) = R_x(X(x), Y(x))(∇S(x))`.
* `riemannOp_covGrad_fiberNormSq_le_gen` — the uniform curvature fibre-norm bound
  on the gradient field at arbitrary covariant rank:
  `rfns(R_x(v, w)(∇S(x))) ≤ Cx · g(v, v) · g(w, w) · rfns(∇S(x))`.

These are the rank-generic curvature ingredients consumed when bounding the
commutator cross term `⟨Curv, ∇S⟩_{L²}` by `‖R‖_∞ · (rfns(S) + rfns(∇S))` in the
integrated route.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
/-- **The Ricci identity on the gradient field** at arbitrary covariant rank. For
smooth tangent fields `X, Y`, the antisymmetric Hessian of the gradient field
`∇S = covGrad g 0 s S` equals the bundled Riemann operator on its fibre value:

```
∇²_{X, Y}(∇S)(x) − ∇²_{Y, X}(∇S)(x) = R_x(X(x), Y(x))(∇S(x)).
```

This is the rank-`(0, s + 1)` instance of `tensorSecondCovDeriv_antisymm_eq_riemannOp`
on the gradient section — both commuted directions are genuine vector fields. -/
theorem secondCovDeriv_covGrad_antisymm_eq_riemannOp_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X Y : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    tensorSecondCovDeriv (I := I) g 0 (s + 1) X Y
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x -
      tensorSecondCovDeriv (I := I) g 0 (s + 1) Y X
        (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x =
      riemannOp (tensorCov (I := I) g 0 (s + 1)) x (X x) (Y x)
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
  tensorSecondCovDeriv_antisymm_eq_riemannOp (I := I) g 0 (s + 1)
    (T := fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y)
    hX hY (covGrad (I := I) (M := M) g 0 s S).toSection.contMDiff

set_option linter.unusedSectionVars false in
/-- **Uniform curvature fibre-norm bound on the gradient field** at arbitrary
covariant rank. For any two tangent vectors `v, w` at `x`, the curvature
contraction of the gradient field `∇S = covGrad g 0 s S` satisfies

```
rfns(R_x(v, w)(∇S(x))) ≤ Cx · g(v, v) · g(w, w) · rfns(∇S(x)),
```

with `Cx ≥ 0` the per-point curvature constant, uniform in `(v, w)` and the
contracted tensor. This is the rank-`(0, s + 1)` curvature fibre bound; together
with the Ricci identity it controls each curvature summand of the commutator
defect by `‖R‖_∞ · rfns(∇S)`. -/
theorem riemannOp_covGrad_fiberNormSq_le_gen
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      ∀ v w : TangentSpace I x,
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ≤
          Cx * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le (I := I) (M := M) g (s + 1) x
  refine ⟨Cx, hCx_nonneg, fun v w => ?_⟩
  exact hbound v w ((covGrad (I := I) (M := M) g 0 s S).toSection x)

end Connection
end Integral
end DifferentialGeometry

end
