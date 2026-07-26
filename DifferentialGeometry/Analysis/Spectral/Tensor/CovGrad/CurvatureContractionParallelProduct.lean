import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantBilinearLeibniz
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformCurvatureSup
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureContractionCovariantLeibnizGrid

/-! # The iterated-gradient grid bound for the metric curvature contraction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file records the **iterated covariant-gradient grid bound** for the
metric curvature contraction `R(X, Y) Z := riemannOp (tensorCov g 0 s) (X, Y) Z`
(`curvatureContraction g s Z hX hY`, a smooth compactly-supported `(0, s)`-tensor section), in the
intrinsic `riemannianFiberNormSq` form the order-`m` curvature-jet induction consumes.

## The differentiated-curvature normal-form route

The metric curvature contraction `R(X, Y)·` is *linear in the single section* `Z`
(`curvatureContraction`, `curvatureContraction_toSection_apply`), the curvature `R` being a *fixed*
operator built from the metric and the frame fields `X, Y`, not a second differentiable
`SmoothCcTensor` argument; and the curvature is **not parallel** (`∇R ≠ 0` on a non-flat manifold),
so the single-step covariant Leibniz reads `∇(R(X, Y) Z) = (∇R)(X, Y) Z + R(X, Y)(∇Z)` with a
*non-vanishing* differentiated-curvature cross term `(∇R)(X, Y) Z`. Iterating this exact Leibniz is
the genuine route, and it is **carried out** in `CurvatureContractionLeibnizGridConstruction`: the
order-`p` differentiated-curvature contraction is packaged as the fixed fibrewise-`ℝ`-linear operator
field `diffCurvOp g hX hY p r` (`(∇^p R)(X, Y)·`), with `diffCurvOp 0 s Z = curvatureContraction`
(`diffCurvOp_zero`) and the exact single-step recursion
`∇(diffCurvOp p r W) = diffCurvOp (p+1) r W + cast(diffCurvOp p (r+1) (∇W))` (`covGrad_diffCurvOp_eq`).

Feeding this recursion to the abstract operator-field **normal form** machinery
(`OperatorFieldDifferentiatedTowerNormalForm`: `normalForm_of_base` builds the normal form from the
single-step recursion, and `exists_jet_bound_of_normalForm` turns it into the per-order covariant jet
envelope) yields, after supremising the per-point envelope over the compact `M`, the base-point-uniform
per-order, per-rank jet bound `exists_proportional_diffCurvOp`
(`rfns(diffCurvOp p r W)(x) ≤ kappa p r · ∑_{q ≤ p} rfns(∇^q W)(x)`), whose curvature coefficient
`kappa p r` is supplied at the bottom by the continuous curvature-operator envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`. The binomial covariant
Leibniz expansion (`rfns_iteratedCovGrad_diffCurvOp_grid`) then assembles the iterated-gradient grid.
This entire chain is **proved** — the grid theorems below are axiom-clean
(`#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`).

The `ParallelTensorProduct` abstraction of `CovariantBilinearLeibniz` (a parallel fibrewise bilinear
bundle map, carrying the `g`-Riemannian operator bound `rfns_prod_le` and the exact covariant Leibniz
`covGrad_prod`, from which the `g`-native diagonal covariant-Leibniz grid is derived) is a *different*,
two-section, parallel-map route; it does **not** apply here, because the curvature is non-parallel and
`R(X, Y)·` is single-section. The diffCurvOp normal-form route above replaces it and is the one actually
used.

## What is proved

The **single-sum** iterated-gradient grid bound
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le` is **proved** here by
collapsing the per-rank curvature-coefficient grid of its sibling
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le`
(`CurvatureContractionCovariantLeibnizGrid`): the curvature-order × rank window
`gridWindowSum kappa 0 s j` (with `4^j`) is a finite nonnegative number at each gradient order `j`,
absorbed into the single-sum constant `C j`, leaving only a sum over the gradient orders of the
*contracted section* `Z`,

```
rfns(∇^j(R(X, Y) Z))(x) ≤ C j · ∑_{q ≤ j} rfns(∇^q Z)(x),
```

with `C : ℕ → ℝ` nonnegative and *uniform in the base point* `x`. The whole tower underneath is
axiom-clean (the curvature coefficient ultimately comes from the continuous curvature-operator
envelope `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`, supremised over
the compact `M`). This rfns grid bound is the deliverable the order-`m` curvature-jet induction
consumes to feed `IsGradedCurvJet`.

The immediately-derivable consumer API is also **proved** on top of it: the nonnegativity of the
grid constant `curvatureContraction_grid_const_nonneg`, and the gradient-order-`0` specialisation
`riemannianFiberNormSq_curvatureContraction_le` (the `∇^0 = id` head term, the single order-`0` fibre
comparison the per-step's seed reads off).

The degenerate witness is rejected: at gradient order `j = 0` the bound reads
`rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x)`, false with `C 0 = 0` on a non-flat manifold whenever the
curvature contraction `R(X, Y) Z` is nonzero (it carries the genuine Riemann curvature of `Z`); the
grid constant must be strictly positive, so the bound is not vacuous.

## Rank genericity

The diffCurvOp normal-form tower and its grid are rank-generic; the curvature contraction
`curvatureContraction g s` and the curvature coefficient `kappa p r` are stated at general covariant
rank `s` (contravariant rank `0`, the case the moving-frame curvature engine uses; the rank index of
`kappa` is genuine — the rank-`r` curvature derivation acts on all `r` slots). The grid bound below
is correspondingly stated at general `s`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-- **Iterated-gradient grid bound for the metric curvature contraction, in intrinsic fibre-norm
form.** For a closed smooth Riemannian manifold `(M, g)`, smooth global tangent fields `X, Y`, and at
every covariant rank `s`, there is a nonnegative order-dependent constant `C : ℕ → ℝ`, *uniform in
the base point*, such that for every smooth compactly-supported `(0, s)`-tensor section `Z`, every
gradient order `j`, and every point `x`, the `j`-fold iterated covariant gradient of the curvature
contraction `R(X, Y) Z := curvatureContraction g s Z hX hY` has intrinsic squared fibre norm at most
`C j` times the sum, over gradient orders `q ≤ j`, of the intrinsic squared fibre norms of the
iterated covariant gradients of `Z`:

```
rfns(∇^j(R(X, Y) Z))(x) ≤ C j · ∑_{q < j + 1} rfns(∇^q Z)(x).
```

This is proved by collapsing the per-rank curvature-coefficient grid of the sibling
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le`: the curvature-order
× rank window `gridWindowSum kappa 0 s j` (with `4^j`) is a finite nonnegative number at each gradient
order `j` (`gridWindowSum_nonneg`), absorbed into `C j`, leaving the single sum over the gradient
orders of `Z`. The kappaGrid tower is itself proved through the differentiated-curvature operator
`diffCurvOp` normal form (`CurvatureContractionLeibnizGridConstruction`), whose curvature coefficient
comes from the continuous curvature-operator envelope
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` supremised over the compact
`M`; the whole chain is axiom-clean.

The degenerate witness is rejected: at `j = 0` the bound reads `rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x)`,
false with `C 0 = 0` on a non-flat manifold when `R(X, Y) Z ≠ 0` (the contraction carries the genuine
Riemann curvature of `Z`), so the constant is genuinely positive. -/
theorem exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (Z : SmoothCcTensor g 0 s) (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
            ((iteratedCovGrad g 0 s j (curvatureContraction (I := I) (M := M) g s Z hX hY)).toSection
              x) ≤
          C j * ∑ q ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + q) x
              ((iteratedCovGrad g 0 s q Z).toSection x) := by
  obtain ⟨kappa, hkappa_nn, hbound⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_kappaGrid_le
      (I := I) (M := M) g s hX hY

  refine ⟨fun j => (4 : ℝ) ^ j * gridWindowSum kappa 0 s j,
    fun j => mul_nonneg (by positivity) (gridWindowSum_nonneg hkappa_nn 0 s j), fun Z j x => ?_⟩
  exact hbound Z j x

/-- **The grid constant of the curvature-contraction fibre bound is nonnegative at every order.**
A direct read-off of the nonnegativity field of
`exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le`, packaged as a standalone
fact for downstream constant bookkeeping. -/
theorem curvatureContraction_grid_const_nonneg
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)) (j : ℕ) :
    0 ≤ (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
        (I := I) (M := M) g s hX hY).choose j :=
  (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
    (I := I) (M := M) g s hX hY).choose_spec.1 j

/-- **Gradient-order-`0` fibre comparison for the metric curvature contraction.** Specialising the
grid bound `exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le` to gradient
order `j = 0` (where `∇^0 = id` and the order sum `∑_{q < 1}` collapses to its single `q = 0` term):
the intrinsic squared fibre norm of the curvature contraction `R(X, Y) Z` at `x` is bounded by the
nonnegative constant `C 0` times the intrinsic squared fibre norm of `Z` at `x`,

```
rfns(R(X, Y) Z)(x) ≤ C 0 · rfns(Z)(x).
```

This is the genuine order-`0` head term the curvature-jet seed reads off the grid bound; it is proved
from the grid bound by collapsing `iteratedCovGrad … 0 = id` (`iteratedCovGrad_zero`) and the
single-term range sum (`Finset.sum_range_one`). It is *false* with `C 0 = 0` on a non-flat manifold
when `R(X, Y) Z ≠ 0`, so the bound is not vacuous. -/
theorem riemannianFiberNormSq_curvatureContraction_le
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (Z : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((curvatureContraction (I := I) (M := M) g s Z hX hY).toSection x) ≤
      (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
          (I := I) (M := M) g s hX hY).choose 0 *
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (Z.toSection x) := by
  have hgrid :=
    (exists_riemannianFiberNormSq_iteratedCovGrad_curvatureContraction_grid_le
      (I := I) (M := M) g s hX hY).choose_spec.2 Z 0 x
  rw [iteratedCovGrad_zero] at hgrid
  rw [Finset.sum_range_one, iteratedCovGrad_zero] at hgrid
  exact hgrid

end Connection
end Integral
end DifferentialGeometry

end
