import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CurvatureFrameEnergyContinuity
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs
import Mathlib.Topology.Order.Compact

/-!
# Uniform-over-`M` proportional fibre-norm bound for the tensor curvature operator

For a smooth Riemannian metric `g` on a *closed* manifold `M` (modelled on a real
inner-product space `E`), the bundled tensor curvature operator
`riemannOp (tensorCov g 0 t) x` is a continuous trilinear form
`T_x M × T_x M × (T^0_t)_x → (T^0_t)_x`. The per-point proportional fibre-norm bound
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le` already supplies, for each fixed
`x`, a nonnegative `C_x` with

```
riemannianFiberNormSq g 0 t x (R_x(v, w) T) ≤ C_x · g(v, v) · g(w, w) · riemannianFiberNormSq g 0 t x T
```

for all `(v, w, T)`. The genuine content of this file is the *uniformisation* of that
per-point constant over the compact manifold: a **single** nonnegative constant `C`,
independent of the base point, witnessing the same proportional bound at every `x`. This is
exactly the proportional curvature-operator fibre bound consumed by the moving-frame
third-order Weitzenböck remainder node
`pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder` (the `Gcurv` field, the
pure-Riemann frame-sum `R_x(B_i, ·)(∇S)`), uniformised so that the valence-dependent
constant `Cper s` does not depend on the base point `x`.

## Why the per-point constant cannot simply be supremised

The per-point constant produced by `exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le`
is the frame-pair-dual curvature energy
`C_x = ∑_{i,j,K,J} riemannianFiberNormSq g 0 t x (R_x(e_i, e_j)(dualTensorFrameRS g x 0 t e K J))`,
built from the `g`-orthonormal frame `e = stdOrthonormalBasis` at `x`. That frame is *not*
continuous in `x` (it is chosen pointwise by `stdOrthonormalBasis`), so `x ↦ C_x` is not, as
written, a continuous function and `IsCompact.bddAbove_image` does not apply to it directly.

The correct route packages the per-point bound by a genuinely **continuous** envelope
`Ccurv : M → ℝ` — the intrinsic curvature-operator norm, which is continuous because the
curvature operator is built from the smooth metric and the smooth Riemann tensor (whose
chart-coordinate components are uniformly bounded on the compact chart supports by
`exists_chartRiemannData_uniform_bound_compact`). With a continuous envelope in hand, the
uniform constant is the supremum of `Ccurv` over the compact `M`, extracted through the
image-compactness route `(isCompact_univ).image · |>.bddAbove`.

## Main results

* `exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional` — the posited
  *continuous* per-point proportional curvature-operator fibre bound (the genuinely-deep
  DG/analysis content; see its docstring for the precise truth justification and the
  chart-curvature-data construction it is discharged by).
* `riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound` — the headline:
  a single uniform nonnegative `C` witnessing the proportional fibre bound for
  `R_x(v, w)(∇S)` at every base point `x`, every `(v, w)` and every smooth tensor `S`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

set_option linter.unusedSectionVars false in
/-- Non-negativity of `g.inner x v v` for a smooth Riemannian metric. -/
private lemma metric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

/-- **Posited continuous per-point proportional curvature-operator fibre bound.** For a smooth
Riemannian metric `g` on a closed manifold `M` and any covariant rank `t`, there is a
*continuous* nonnegative function `Ccurv : M → ℝ` such that, at every base point `x`, for all
tangent vectors `v, w` and all `(0, t)`-tensors `T`,

```
riemannianFiberNormSq g 0 t x (R_x(v, w) T)
  ≤ Ccurv x · g(v, v) · g(w, w) · riemannianFiberNormSq g 0 t x T,
```

where `R = riemannOp (tensorCov g 0 t)` is the bundled tensor curvature operator.

**Why this is TRUE.** Fix `x`. The per-point proportional bound
`exists_Cx_riemannianFiberNormSq_riemannOp_tensorCovS_le` already supplies a nonnegative `C_x`
with exactly this inequality for all `(v, w, T)`, so the *value* of a valid pointwise envelope
exists at every point; the only additional content here is that the envelope can be chosen
**continuously** in `x`. The intrinsic curvature-operator norm
`x ↦ ‖riemannOp (tensorCov g 0 t) x‖_{op}` (the least constant for which the displayed
proportional bound holds, measured in the intrinsic `g`-fibre norms) is continuous because the
curvature operator is assembled from the smooth metric `g` and the smooth Levi-Civita Riemann
tensor: in any chart at `α`, the chart-coordinate Riemann coefficients
`chartRiemannTensor g α i j k l (ϕ_α b)` are `C^∞` (polynomial in the chart Christoffel symbols
and their first partials, `chartChristoffel_contDiffOn_interior`) and *uniformly bounded* on the
compact chart-`α` partition-of-unity support
(`exists_chartRiemannData_uniform_bound_compact`); the intrinsic fibre norm of the curvature
action is controlled, through the forward chart-frame Gram Rayleigh route
(`riemannianFiberNormSq_le_chartAlpha_summand_sum_on_pouTsupport`, `chartGramMatrix` continuous
on the chart base set) and its reverse companion, by these bounded smooth chart-data, yielding a
continuous (indeed locally Lipschitz) envelope `Ccurv` on the finitely-many compact chart
supports that cover `M` — patched to a global continuous function by the partition of unity.
This is the chart-locality-free route (no `HasLocallyConstantChartAt`, no chart-trivialisation
operator-norm scalar); the only chart objects are the bounded chart Christoffel / Riemann data
and the positive-definite chart Gram matrix.

**Non-vacuity.** A degenerate witness `Ccurv ≡ 0` is rejected on any non-flat manifold: at a
point `x` where the curvature operator is nonzero there exist `v, w, T` with
`R_x(v, w) T ≠ 0`, hence `riemannianFiberNormSq g 0 t x (R_x(v, w) T) > 0` while the right-hand
side `0 · g(v, v) · g(w, w) · riemannianFiberNormSq g 0 t x T = 0`, contradicting the bound. So
the envelope must carry the genuine curvature magnitude.

This is the genuinely-irreducible analytic content (continuity of the curvature-operator norm /
the bridge from uniformly-bounded chart curvature data to a continuous intrinsic-fibre-norm
curvature bound) posited here as the precise continuous-envelope primitive and discharged
separately; the *uniformisation* over the compact `M` (the supremum) is proved on top of it in
`riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound`. -/
theorem exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
    (g : SmoothRiemannianMetric I M) (t : ℕ) :
    ∃ Ccurv : M → ℝ, Continuous Ccurv ∧ (∀ x : M, 0 ≤ Ccurv x) ∧
      ∀ (x : M) (v w : TangentSpace I x) (T : TensorRSSpace 0 t I x),
        riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x v w T) ≤
          Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_energy⟩ :=
    exists_continuous_riemannOp_tensorCovS_frameEnergy_bound (I := I) (M := M) g t
  refine ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, ?_⟩
  intro x v w T
  obtain ⟨n, e, horth, hrepr, hvw⟩ :=
    riemannianFiberNormSq_riemannOp_tensorCovS_vw_factor_le (I := I) (M := M) g t x v w T
  have hvv_nonneg : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hww_nonneg : 0 ≤ g.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g x w
  have hvw_nonneg : 0 ≤ g.inner x v v * g.inner x w w := mul_nonneg hvv_nonneg hww_nonneg
  have henergy :
      (∑ i : Fin n, ∑ j : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 t x
            (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T)) ≤
        Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T :=
    hCcurv_energy x e horth hrepr T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 t x
        (riemannOp (tensorCov (I := I) g 0 t) x v w T)
        ≤ g.inner x v v * g.inner x w w *
            ∑ i : Fin n, ∑ j : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 t x
                (riemannOp (tensorCov (I := I) g 0 t) x (e i) (e j) T) := hvw
    _ ≤ g.inner x v v * g.inner x w w *
            (Ccurv x * riemannianFiberNormSq (I := I) (M := M) g 0 t x T) :=
          mul_le_mul_of_nonneg_left henergy hvw_nonneg
    _ = Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 t x T := by ring

/-- **Uniform-over-`M` proportional fibre-norm bound for the tensor curvature operator on the
gradient field.** For a smooth Riemannian metric `g` on a closed manifold `M` and any covariant
rank `s`, there is a *single* nonnegative constant `C`, independent of the base point, such that
for every `x : M`, every pair of tangent vectors `v, w` at `x`, and every smooth
compactly-supported `(0, s)`-tensor `S`,

```
riemannianFiberNormSq g 0 (s + 1) x (R_x(v, w)(∇S(x)))
  ≤ C · g(v, v) · g(w, w) · riemannianFiberNormSq g 0 (s + 1) x (∇S(x)),
```

where `R = riemannOp (tensorCov g 0 (s + 1))` is the bundled tensor curvature operator on the
`(0, s + 1)`-tensor covariant derivative and `∇S = covGrad g 0 s S` is the gradient field. This
is the base-point-uniform proportional curvature bound consumed by the moving-frame third-order
Weitzenböck remainder node `pointwiseTensorCurv_movingFrameWeitzenbock_namedRemainder` (its
`Gcurv` field, the pure-Riemann frame-sum `R_x(B_i, ·)(∇S)`): summing the bound over a
`g`-orthonormal frame `B_i` (with `g(B_i, B_i) = 1`) and using the fibre-norm subadditivity
gives the `(Cper s)² · rfns(∇S)` bound of that node, with `Cper s` independent of `x`.

The uniform constant `C` is the supremum over the compact `M` of the continuous per-point
proportional envelope `Ccurv` supplied by
`exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional`; it is extracted
through the image-compactness route (a continuous real function on a compact space has bounded
range). The bound is stated entirely in the intrinsic Riemannian fibre norm and the metric
inner products `g(v, v)`, `g(w, w)` — never in a bundle continuous-linear-map operator norm
(which is unavailable because of the `TangentSpace = E` norm diamond) and never through the
chart-trivialisation operator-norm scalar (genuinely unbounded on multi-chart manifolds). -/
theorem riemannianFiberNormSq_riemannOp_covGrad_uniform_proportional_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : M) (v w : TangentSpace I x) (S : SmoothCcTensor g 0 s),
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) ≤
          C * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  obtain ⟨Ccurv, hCcurv_cont, hCcurv_nonneg, hCcurv_bound⟩ :=
    exists_continuous_riemannianFiberNormSq_riemannOp_tensorCov_proportional
      (I := I) (M := M) g (s + 1)
  have hCpt := (isCompact_univ (X := M)).image hCcurv_cont
  obtain ⟨C₀, hC₀⟩ := hCpt.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x v w S
  have hCcurv_le : Ccurv x ≤ max C₀ 0 :=
    le_trans (hC₀ ⟨x, Set.mem_univ _, rfl⟩) (le_max_left _ _)
  have hfactor_nonneg :
      0 ≤ g.inner x v v * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
    mul_nonneg
      (mul_nonneg (metric_inner_self_nonneg (I := I) (M := M) g x v)
        (metric_inner_self_nonneg (I := I) (M := M) g x w))
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _)
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        (riemannOp (tensorCov (I := I) g 0 (s + 1)) x v w
          ((covGrad (I := I) (M := M) g 0 s S).toSection x))
        ≤ Ccurv x * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) :=
          hCcurv_bound x v w ((covGrad (I := I) (M := M) g 0 s S).toSection x)
    _ = Ccurv x * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) := by ring
    _ ≤ max C₀ 0 * (g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) :=
          mul_le_mul_of_nonneg_right hCcurv_le hfactor_nonneg
    _ = max C₀ 0 * g.inner x v v * g.inner x w w *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by ring

end Connection
end Integral
end DifferentialGeometry

end
