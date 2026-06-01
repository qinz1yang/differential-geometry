import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Intrinsic Riemannian fiber norm-squared on `(r,s)`-tensor fibers

For a smooth Riemannian metric `g` on a manifold `M`, this file defines a non-negative
real-valued quantity `riemannianFiberNormSq g r s b T` for any tensor
`T : TensorRSSpace r s I b`. The definition is built directly from the bilinear form
`g.inner b` on `TangentSpace I b` — without any reference to a chart trivialization or
chart selector — by:

1. Endowing `TangentSpace I b` locally with the inner-product-space structure determined
   by `g.inner b` (via `InnerProductSpace.Core` and `InnerProductSpace.ofCoreOfTopology`,
   which preserves the existing topology on the tangent space).
2. Picking an orthonormal basis `e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b)`
   produced by `stdOrthonormalBasis`.
3. Summing the squares of the real-number evaluations of `T` on multi-indexed tuples
   `(ω^I, e_J)` where `ω^I` is the basis covector built from the linear functionals
   `v ↦ ⟨v, e (I k)⟩_g` and `e_J k = e (J k)`.

## Main definitions

* `riemannianFiberNormSq g r s b T` — the non-negative real number assigning to a
  tensor `T : TensorRSSpace r s I b` its Riemannian fiber norm-squared at `b`.

## Main theorems

* `riemannianFiberNormSq_nonneg` — `0 ≤ riemannianFiberNormSq g r s b T`.
* `riemannianFiberNormSq_zero` — the norm-squared of the zero tensor is `0`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The basic summand-by-summand quantity: a real-valued function of multi-indices `K`,
`J` and an orthonormal basis `e` (with respect to `g`) of `TangentSpace I b`. We package
it as a separate function so the unfolding of `riemannianFiberNormSq` does not have to
expose the locally-bound `letI` instances. -/
noncomputable def fiberNormSqSummand
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) : ℝ :=
  ((T : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k))))
      (fun k => e (J k))) ^ 2

lemma fiberNormSqSummand_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (T : TensorRSSpace r s I b)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    0 ≤ fiberNormSqSummand (I := I) (M := M) g b r s T n e K J := by
  unfold fiberNormSqSummand
  exact sq_nonneg _

private lemma fiberNormSqSummand_zero
    (g : SmoothRiemannianMetric I M) (b : M) (r s : ℕ)
    (n : ℕ) (e : Fin n → TangentSpace I b)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    fiberNormSqSummand (I := I) (M := M) g b r s
      (0 : TensorRSSpace r s I b) n e K J = 0 := by
  unfold fiberNormSqSummand
  have h_inner : ((0 : TensorRSSpace r s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k)))) :
      Tensor0SSpace s I b) = 0 := rfl
  rw [show (((0 : TensorRSSpace r s I b)
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
        (fun k => g.inner b (e (K k)))))
      (fun k => e (J k)) : ℝ) = 0 from by rw [h_inner]; rfl]
  norm_num

/-- The Riemannian fiber norm-squared of an `(r,s)`-tensor at the point `b ∈ M`.

Concretely:
1. Equip `TangentSpace I b` with the inner-product structure induced by `g.inner b`
   (locally inside the definition, via `InnerProductSpace.ofCoreOfTopology`, which
   preserves the existing topology on the tangent space).
2. Pick an orthonormal basis `e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b)`
   produced by `stdOrthonormalBasis`, where `n = Module.finrank ℝ (TangentSpace I b)`.
3. For each pair of multi-indices `(K, J) : (Fin r → Fin n) × (Fin s → Fin n)`, form
   the test covariant tensor `ω^K ∈ Tensor0SSpace r I b` as the continuous multilinear
   map `(v_1, …, v_r) ↦ ∏_k g.inner b (e (K k)) v_k` (built via
   `ContinuousMultilinearMap.mkPiAlgebra` and `compContinuousLinearMap`),
   evaluate `T ω^K` (an `(0,s)`-tensor) on the `s`-tuple `e_J : Fin s → TangentSpace I b`
   with `e_J k = e (J k)`, square the resulting real number, and sum over all
   multi-indices.

The sum of squares is manifestly non-negative and vanishes when `T = 0`; these are the
two headline lemmas below. -/
noncomputable def riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) : ℝ := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I b) := g.toRiemannianMetric.toCore b
  have hc : ContinuousAt (fun v : TangentSpace I b => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt b
  have hb : Bornology.IsVonNBounded ℝ {v : TangentSpace I b |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded b
  letI : NormedAddCommGroup (TangentSpace I b) := cd.toNormedAddCommGroupOfTopology hc hb
  letI : InnerProductSpace ℝ (TangentSpace I b) :=
    InnerProductSpace.ofCoreOfTopology cd hc hb
  let n : ℕ := Module.finrank ℝ (TangentSpace I b)
  let e : OrthonormalBasis (Fin n) ℝ (TangentSpace I b) := stdOrthonormalBasis ℝ _
  exact ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
    fiberNormSqSummand (I := I) (M := M) g b r s T n (fun i => e i) K J

/-- The Riemannian fiber norm-squared is non-negative. This is immediate from the fact
that the definition is a finite sum of non-negative summands (each is a square). -/
theorem riemannianFiberNormSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    0 ≤ riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  classical
  unfold riemannianFiberNormSq
  refine Finset.sum_nonneg (fun K _ => ?_)
  refine Finset.sum_nonneg (fun J _ => ?_)
  exact fiberNormSqSummand_nonneg (I := I) (M := M) g b r s T _ _ K J

/-- The Riemannian fiber norm-squared of the zero tensor is `0`. Each summand vanishes
because the underlying continuous linear map of the zero tensor sends every covariant
input to the zero `(0,s)`-tensor, whose multilinear evaluation is `0 ∈ ℝ`. -/
theorem riemannianFiberNormSq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s b (0 : TensorRSSpace r s I b) = 0 := by
  classical
  unfold riemannianFiberNormSq
  refine Finset.sum_eq_zero (fun K _ => ?_)
  refine Finset.sum_eq_zero (fun J _ => ?_)
  exact fiberNormSqSummand_zero (I := I) (M := M) g b r s _ _ K J

end Connection
end Integral
end DifferentialGeometry
