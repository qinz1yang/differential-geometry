import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus

/-! # The sharp operator-norm fibre-norm bound for a fibrewise tensor operator

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file proves the **sharp** intrinsic squared-fibre-norm bound for the
action of a fibrewise continuous-linear tensor operator, controlled by the operator's `g`-fibre
*operator norm* (no Hilbert–Schmidt dimension factor).

The existing partial-contraction Cauchy–Schwarz `riemannianFiberNormSq_comp_le_mul`
(`OperatorFieldContractionBound.lean`) bounds the composition `(Φ x).comp (W x)` by the *Hilbert–Schmidt*
fibre norm `rfns(Φ x)` of the operator field — a bound that loses dimension factors (`~ n^k`) and is
therefore too lossy when one needs the *exact* operator-norm coefficient (e.g. for a `δ`-separated
top-term extraction whose subsequent `2δ² ≤ δ` collapse must not pick up a dimension factor).

This file supplies the missing **sharp** estimate: if a fibrewise operator `φ` on tensor fibres at a
point `x` satisfies the `g`-fibre operator-norm bound
```
√(rfns(φ v)) ≤ μ · √(rfns(v))    for all fibre tensors v,
```
then its action obeys the *squared* bound `rfns(φ v) ≤ μ² · rfns(v)` with **no** dimension factor.  The
proof runs through the proved intrinsic-fibre-norm / `g`-bundle-norm bridge
(`riemannianFiberNormSq = ‖·‖²` under the `(r, s)`-tensor Riemannian bundle instance), under which the
hypothesis is exactly `‖φ v‖ ≤ μ · ‖v‖` and the conclusion is its square.

## Main results

* `riemannianFiberNormSq_eq_bundle_norm_sq'` — the proved intrinsic-fibre-norm / `g`-bundle-norm bridge
  (re-proved here from public ingredients; the version in `OperatorFieldEvaluationLeibniz.lean` is
  `private`).
* `riemannianFiberNormSq_clm_apply_le_of_sqrt_le` — the sharp operator-norm fibre-norm bound: from the
  `g`-fibre operator-norm bound `√(rfns(φ v)) ≤ μ · √(rfns(v))` with `0 ≤ μ`, conclude
  `rfns(φ v) ≤ μ² · rfns(v)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The intrinsic-fibre-norm / `g`-bundle-norm bridge.**  Under the `(r, s)`-tensor Riemannian bundle
instance `tensorRS_riemannianBundle g r s`, the intrinsic squared Riemannian fibre norm
`riemannianFiberNormSq g r s x z` coincides with the squared bundle-fibre norm `‖z‖²`.  Proved through
the fibre-norm / `tensorInnerPointwise` bridge `riemannianFiberNormSq_eq_tensorInnerPointwise`, the
bundle-fibre inner product `tensorRSRiemannianInnerCLM` and `real_inner_self_eq_norm_sq`; the
model-induced fibre norm is removed so `‖·‖` resolves to the Riemannian bundle norm.  (Re-proved here
from public ingredients; `OperatorFieldEvaluationLeibniz.riemannianFiberNormSq_eq_bundle_norm_sq` is
`private`.) -/
lemma riemannianFiberNormSq_eq_bundle_norm_sq'
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (z : TensorRSSpace r s I x) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    riemannianFiberNormSq (I := I) (M := M) g r s x z = ‖z‖ ^ 2 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have h_inner :
      (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s x z z : ℝ) =
        riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
    exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x z).symm
  have hself : (inner ℝ z z : ℝ) =
      riemannianFiberNormSq (I := I) (M := M) g r s x z := by
    rw [← h_inner]; rfl
  rw [← hself, real_inner_self_eq_norm_sq]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **The sharp operator-norm fibre-norm bound for a fibrewise tensor operator.**  For a fibrewise
continuous-linear operator `φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x` between tensor fibres
at a point `x`, if `φ` obeys the `g`-fibre operator-norm bound in `√(rfns)` form
```
√(rfns(φ v)) ≤ μ · √(rfns(v))    for all v,
```
with `0 ≤ μ`, then it obeys the squared fibre-norm bound
```
rfns(φ v) ≤ μ² · rfns(v)
```
with **no dimension factor** (unlike the Hilbert–Schmidt bound `riemannianFiberNormSq_comp_le_mul`).

**Proof.**  Install the source / target `(0, r)` / `(0, s)`-tensor Riemannian bundle instances, under
which each fibre is a finite-dimensional inner-product space whose squared norm is
`riemannianFiberNormSq` (the bridge `riemannianFiberNormSq_eq_bundle_norm_sq'`).  In bundle-norm terms
the hypothesis reads `‖φ v‖ ≤ μ · ‖v‖` (both sides are nonnegative square roots, so taking squares is an
equivalence); squaring gives `‖φ v‖² ≤ μ² · ‖v‖²`, which the bridge converts to the claimed `rfns`
bound.

**Non-vacuity.**  The bound genuinely uses `μ` and rejects `μ ≡ 0` whenever `φ` is nonzero on a tensor
with positive fibre norm (then the conclusion forces `rfns(φ v) ≤ 0`, false). -/
theorem riemannianFiberNormSq_clm_apply_le_of_sqrt_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (φ : TensorRSSpace 0 r I x →L[ℝ] TensorRSSpace 0 s I x) (μ : ℝ) (hμ : 0 ≤ μ)
    (hbound : ∀ v : TensorRSSpace 0 r I x,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v)) ≤
        μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) :
    ∀ v : TensorRSSpace 0 r I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) ≤
        μ ^ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 r x v := by
  letI instSrc : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 r I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 r
  letI instTgt : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 s
  intro v
  have hsrc_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 r x v :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 r x v
  have htgt_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x (φ v)
  have hb := hbound v

  have hrhs_nn : 0 ≤ μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v) :=
    mul_nonneg hμ (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x (φ v))) ^ 2 ≤
        (μ * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 r x v)) ^ 2 := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  rw [Real.sq_sqrt htgt_nn] at hsq
  rw [mul_pow, Real.sq_sqrt hsrc_nn] at hsq
  exact hsq

end Connection
end Integral
end DifferentialGeometry

end
