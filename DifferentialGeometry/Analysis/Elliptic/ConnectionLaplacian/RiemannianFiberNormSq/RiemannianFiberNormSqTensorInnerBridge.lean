import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpVWFactorBound
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fibre-norm bridge: the two representations of the `g`-induced tensor fibre norm

For a smooth Riemannian metric `g` on a manifold `M`, the `g`-induced squared norm of an
`(r, s)`-tensor at a point `x` is represented in two ways in the project:

* `riemannianFiberNormSq g r s x T` (intrinsic, frame-based): built from a
  `g`-orthonormal frame `e` of the tangent space (via `stdOrthonormalBasis` of the local
  inner-product structure coming from `g`), as the double sum over multi-indices `(K, J)`
  of the squared frame components `T(ω^K)(e_J)`, where `ω^K = ∏_k g.inner x (e (K k))`.

* `tensorInnerPointwise g r s x M M` (model, Gram-matrix-based): built on the model fibre
  `TensorRSModel r s ℝ E` by lowering the `r` upper slots through the metric and contracting
  through the inverse Gram matrix `(gramMatrixAt g x)⁻¹` of the *fixed* model-space basis
  `chartModelBasis E`.

Both compute the **same** `g`-induced fibre inner product, but via genuinely different
routes (a `g`-orthonormal frame versus the inverse Gram matrix on a fixed basis). This file
proves they coincide:
```
riemannianFiberNormSq g r s x T
  = tensorInnerPointwise g r s x (TensorRSSpace.toModel T) (TensorRSSpace.toModel T).
```

The proof has two layers:

* **Model-side Parseval.** For any `g(x)`-orthonormal basis frame `E` of `T_xM`, the
  covariant `(0, N)` pointwise inner product `tensorInnerPointwise_0s` is the plain diagonal
  sum over the frame:
  ```
  tensorInnerPointwise_0s N g x S T = ∑_{φ : Fin N → Fin n} S(E ∘ φ) · T(E ∘ φ).
  ```
  This is `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`, proved by induction through the
  recursion's leading-slot contraction and the matrix identity `Sᵀ G⁻¹ S = 1` for the mixed
  Gram matrix of the orthonormal frame.

* **Index reindexing.** The lowering map `lowerAllUpperIndices` sends the model tensor
  `toModel T` to a `(0, r + s)`-tensor whose value on the appended frame tuple
  `Fin.append (e ∘ K) (e ∘ J)` is exactly the bundle-side frame component
  `fiberNormSqComponent g x r s T n e K J`. Reindexing the diagonal sum over
  `φ : Fin (r + s) → Fin n` by the splitting `φ ↔ (φ ∘ castAdd, φ ∘ natAdd)` matches the two
  representations summand-by-summand.

## Main results

* `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame` — model-side Parseval in a `g`-orthonormal
  frame.
* `riemannianFiberNormSq_eq_tensorInnerPointwise` — the headline bridge equality.
* `tensorL2Norm_sq_eq_integral_riemannianFiberNormSq` — the global `L²` corollary.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators Matrix RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The mixed Gram matrix `S i a = g.inner x (chartModelBasis E i) (frame a)` of a tangent
frame against the fixed model basis. -/
private noncomputable def mixedGram
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i a => g.inner x ((chartModelBasis E) i) (frame a)

@[simp] private lemma mixedGram_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (i a : Fin (Module.finrank ℝ E)) :
    mixedGram (I := I) (M := M) g x frame i a =
      g.inner x ((chartModelBasis E) i) (frame a) := rfl

/-- A `g(x)`-orthonormal basis expands every tangent vector through its `g`-projections. -/
private lemma orthoFrame_expansion
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (v : TangentSpace I x) :
    v = ∑ a : Fin (Module.finrank ℝ E), g.inner x v (frame a) • frame a := by
  classical
  conv_lhs => rw [← frame.sum_repr v]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  have hv : g.inner x v (frame a) =
      ∑ b : Fin (Module.finrank ℝ E),
        frame.repr v b * g.inner x (frame b) (frame a) := by
    conv_lhs => rw [show v = ∑ b : Fin (Module.finrank ℝ E),
      frame.repr v b • frame b from (frame.sum_repr v).symm]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hv, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba
    rw [horth b a, if_neg (by simpa [eq_comm] using hba), mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ a) hb

/-- The model Gram matrix factors as `G = S Sᵀ` through the mixed Gram matrix of a
`g(x)`-orthonormal basis frame. -/
private lemma gramMatrixAt_eq_mixedGram_mul_transpose
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    gramMatrixAt (I := I) (M := M) g x =
      mixedGram (I := I) (M := M) g x frame *
        (mixedGram (I := I) (M := M) g x frame)ᵀ := by
  classical
  ext i j
  rw [gramMatrixAt_apply, Matrix.mul_apply]
  have hexp : (chartModelBasis E) j =
      ∑ a : Fin (Module.finrank ℝ E),
        g.inner x ((chartModelBasis E) j) (frame a) • frame a :=
    orthoFrame_expansion (I := I) (M := M) g x frame horth ((chartModelBasis E) j)
  calc g.inner x ((chartModelBasis E) i) ((chartModelBasis E) j)
      = g.inner x ((chartModelBasis E) i)
          (∑ a : Fin (Module.finrank ℝ E),
            g.inner x ((chartModelBasis E) j) (frame a) • frame a) := by rw [← hexp]
    _ = ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a *
            (mixedGram (I := I) (M := M) g x frame)ᵀ a j := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul,
          mixedGram_apply, Matrix.transpose_apply, mixedGram_apply]
        ring

/-- The mixed Gram matrix of a `g(x)`-orthonormal basis frame is invertible. -/
private lemma mixedGram_isUnit
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    IsUnit (mixedGram (I := I) (M := M) g x frame) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det]
  have hG := gramMatrixAt_eq_mixedGram_mul_transpose (I := I) (M := M) g x frame horth
  have hdetG : (gramMatrixAt (I := I) (M := M) g x).det ≠ 0 := by
    have := gramMatrixAt_isUnit (I := I) (M := M) g x
    rwa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  rw [hG, Matrix.det_mul, Matrix.det_transpose] at hdetG
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h] at hdetG
  simp at hdetG

/-- **The key matrix identity** `Sᵀ G⁻¹ S = 1` for the mixed Gram matrix `S` of a
`g(x)`-orthonormal basis frame. -/
private lemma mixedGram_transpose_mul_inv_mul
    (g : SmoothRiemannianMetric I M) (x : M)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0) :
    (mixedGram (I := I) (M := M) g x frame)ᵀ *
        ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
          mixedGram (I := I) (M := M) g x frame) = 1 := by
  classical
  set S := mixedGram (I := I) (M := M) g x frame with hS_def
  have hS_unit : IsUnit S := mixedGram_isUnit (I := I) (M := M) g x frame horth
  have hG : gramMatrixAt (I := I) (M := M) g x = S * Sᵀ :=
    gramMatrixAt_eq_mixedGram_mul_transpose (I := I) (M := M) g x frame horth
  have hGinv : (gramMatrixAt (I := I) (M := M) g x)⁻¹ = Sᵀ⁻¹ * S⁻¹ := by
    rw [hG, Matrix.mul_inv_rev]
  rw [hGinv]
  have hSdet : IsUnit S.det := Matrix.isUnit_iff_isUnit_det _ |>.mp hS_unit
  have hSTdet : IsUnit Sᵀ.det := by
    rw [Matrix.det_transpose]; exact hSdet
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Sᵀ hSTdet,
    Matrix.one_mul, Matrix.nonsing_inv_mul S hSdet]

/-- Expansion of `tensorInnerPointwise_0s` over a finite sum of scalar-weighted tensors in
the first argument. -/
private lemma tensorInnerPointwise_0s_sum_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x (∑ i ∈ A, a i • ψ i) T =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x (ψ i) T := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_left]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_left,
        tensorInnerPointwise_0s_smul_left, ih, Finset.sum_insert hi]

/-- Expansion of `tensorInnerPointwise_0s` over a finite sum of scalar-weighted tensors in
the second argument. -/
private lemma tensorInnerPointwise_0s_sum_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (a : ι → ℝ)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (ψ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x S (∑ i ∈ A, a i • ψ i) =
      ∑ i ∈ A, a i *
        tensorInnerPointwise_0s (I := I) (M := M) s g x S (ψ i) := by
  classical
  induction A using Finset.induction with
  | empty => simp [tensorInnerPointwise_0s_zero_right]
  | insert i A hi ih =>
      rw [Finset.sum_insert hi, tensorInnerPointwise_0s_add_right,
        tensorInnerPointwise_0s_smul_right, ih, Finset.sum_insert hi]

/-- Double bilinear expansion of `tensorInnerPointwise_0s` over finite sums of
scalar-weighted tensors in both arguments. -/
private lemma tensorInnerPointwise_0s_bisum
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    {ι : Type*} (A : Finset ι) (c d : ι → ℝ)
    (ψ φ : ι → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) s g x
        (∑ a ∈ A, c a • ψ a) (∑ b ∈ A, d b • φ b) =
      ∑ a ∈ A, ∑ b ∈ A,
        (c a * d b) *
          tensorInnerPointwise_0s (I := I) (M := M) s g x (ψ a) (φ b) := by
  classical
  rw [tensorInnerPointwise_0s_sum_smul_left]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [tensorInnerPointwise_0s_sum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `curryLeft` of a continuous multilinear map commutes with finite sums of scalar
multiples in its leading vector argument. -/
private lemma curryLeft_sum_smul {s : ℕ}
    (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    {ι : Type*} (A : Finset ι) (c : ι → ℝ) (w : ι → E) :
    P.curryLeft (∑ a ∈ A, c a • w a) =
      ∑ a ∈ A, c a • P.curryLeft (w a) := by
  classical
  induction A using Finset.induction with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha, map_add, map_smul, ih, Finset.sum_insert ha]

private lemma tensorInnerPointwise_0s_succ_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) (s + 1) g x S T =
      ∑ a : Fin (Module.finrank ℝ E),
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame a)) := by
  classical
  rw [tensorInnerPointwise_0s_succ]
  have hmodel_exp : ∀ i : Fin (Module.finrank ℝ E),
      (chartModelBasis E) i =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a • frame a := by
    intro i
    have hexp := orthoFrame_expansion (I := I) (M := M) g x frame horth
      ((chartModelBasis E) i)
    rw [hexp]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [mixedGram_apply]
  have hcurry_exp : ∀ (P : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (i : Fin (Module.finrank ℝ E)),
      P.curryLeft ((chartModelBasis E) i) =
        ∑ a : Fin (Module.finrank ℝ E),
          mixedGram (I := I) (M := M) g x frame i a • P.curryLeft (frame a) := by
    intro P i
    rw [hmodel_exp i]
    exact curryLeft_sum_smul (E := E) P Finset.univ _ _
  have hstep : ∀ i j : Fin (Module.finrank ℝ E),
      (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) =
        ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (mixedGram (I := I) (M := M) g x frame i a *
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              mixedGram (I := I) (M := M) g x frame j b) *
            tensorInnerPointwise_0s (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro i j
    rw [hcurry_exp S i, hcurry_exp T j]
    rw [tensorInnerPointwise_0s_bisum (I := I) (M := M) g x s
      (A := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    ring
  rw [show (∑ i, ∑ j,
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        (mixedGram (I := I) (M := M) g x frame i a *
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b) *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b))
    from by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hstep i j]
  have hkey := mixedGram_transpose_mul_inv_mul (I := I) (M := M) g x frame horth
  set F := fun (i j a b : Fin (Module.finrank ℝ E)) =>
    (mixedGram (I := I) (M := M) g x frame i a *
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        mixedGram (I := I) (M := M) g x frame j b) *
      tensorInnerPointwise_0s (I := I) (M := M) s g x
        (S.curryLeft (frame a)) (T.curryLeft (frame b)) with hF_def
  have hreindex :
      ∑ i, ∑ j, ∑ a, ∑ b, F i j a b =
        ∑ a, ∑ b, ∑ i, ∑ j, F i j a b := by
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j a => ∑ b, F i j a b))]
    rw [Finset.sum_comm (f := fun i a => ∑ j, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm
      (f := fun j b => F i j a b))]
    rw [Finset.sum_comm (f := fun i b => ∑ j, F i j a b)]
  rw [hreindex]
  have hcollapse : ∀ a b : Fin (Module.finrank ℝ E),
      ∑ i, ∑ j, F i j a b =
        ((mixedGram (I := I) (M := M) g x frame)ᵀ *
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
              mixedGram (I := I) (M := M) g x frame)) a b *
          tensorInnerPointwise_0s (I := I) (M := M) s g x
            (S.curryLeft (frame a)) (T.curryLeft (frame b)) := by
    intro a b
    rw [Matrix.mul_apply]
    rw [show (∑ i, (mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGram (I := I) (M := M) g x frame) i b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ i, ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ *
            mixedGram (I := I) (M := M) g x frame) i b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply]
    rw [show ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ∑ j, (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      = ∑ j, ((mixedGram (I := I) (M := M) g x frame)ᵀ a i *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            mixedGram (I := I) (M := M) g x frame j b)) *
        tensorInnerPointwise_0s (I := I) (M := M) s g x
          (S.curryLeft (frame a)) (T.curryLeft (frame b))
      from by rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hF_def]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcollapse a b))]
  rw [hkey]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro b _ hba
    rw [Matrix.one_apply_ne (Ne.symm hba), zero_mul]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- **Model Parseval.** For a `g(x)`-orthonormal basis frame `frame`, the covariant `(0, N)`
pointwise inner product is the diagonal sum over the frame:
`tensorInnerPointwise_0s N g x S T = ∑_{φ} S(frame ∘ φ) · T(frame ∘ φ)`. -/
theorem tensorInnerPointwise_0s_eq_diag_sum_orthoFrame
    (g : SmoothRiemannianMetric I M) (x : M) (N : ℕ)
    (frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (horth : ∀ a b, g.inner x (frame a) (frame b) = if a = b then 1 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin N => E) ℝ) :
    tensorInnerPointwise_0s (I := I) (M := M) N g x S T =
      ∑ φ : Fin N → Fin (Module.finrank ℝ E),
        S (fun k => frame (φ k)) * T (fun k => frame (φ k)) := by
  classical
  induction N with
  | zero =>
      rw [tensorInnerPointwise_0s_zero_arity]
      rw [Finset.sum_eq_single (fun a : Fin 0 => a.elim0)]
      · congr 1 <;>
          (congr 1; funext a; exact a.elim0)
      · intro b _ hb
        exact absurd (funext fun a => a.elim0) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
  | succ s ih =>
      rw [tensorInnerPointwise_0s_succ_orthoFrame (I := I) (M := M) g x s frame horth S T]
      have hstep : ∀ a : Fin (Module.finrank ℝ E),
          tensorInnerPointwise_0s (I := I) (M := M) s g x
              (S.curryLeft (frame a)) (T.curryLeft (frame a)) =
            ∑ ψ : Fin s → Fin (Module.finrank ℝ E),
              S (fun k => frame ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
                T (fun k => frame
                  ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
        intro a
        rw [ih (S.curryLeft (frame a)) (T.curryLeft (frame a))]
        refine Finset.sum_congr rfl (fun ψ _ => ?_)
        have hS : (S.curryLeft (frame a)) (fun k => frame (ψ k)) =
            S (fun k => frame
              ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext k
          refine Fin.cases ?_ ?_ k
          · simp
          · intro m; simp
        have hT : (T.curryLeft (frame a)) (fun k => frame (ψ k)) =
            T (fun k => frame
              ((Fin.cons a ψ : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) := by
          rw [ContinuousMultilinearMap.curryLeft_apply]
          congr 1
          funext k
          refine Fin.cases ?_ ?_ k
          · simp
          · intro m; simp
        rw [hS, hT]
      rw [Finset.sum_congr rfl (fun a _ => hstep a)]
      rw [← Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (s + 1) => Fin (Module.finrank ℝ E)))
        (fun p => S (fun k => frame
            ((Fin.cons p.1 p.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)) *
          T (fun k => frame
            ((Fin.cons p.1 p.2 : Fin (s + 1) → Fin (Module.finrank ℝ E)) k)))
        (fun φ => S (fun k => frame (φ k)) * T (fun k => frame (φ k)))
        (fun p => rfl)]
      rw [Fintype.sum_prod_type]

/-- The lowered model-tensor evaluated on the appended frame tuple equals the bundle-side
frame component. -/
private lemma lower_toModel_append_eq_fiberNormSqComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x)
    (n : ℕ) (e : Fin n → TangentSpace I x)
    (K : Fin r → Fin n) (J : Fin s → Fin n) :
    lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T)
        (Fin.append (fun k => e (K k)) (fun j => e (J j)))
      = fiberNormSqComponent (I := I) (M := M) g x r s T n e K J := by
  rw [lowerAllUpperIndices_apply]
  simp only [Fin.append_left, Fin.append_right]
  unfold fiberNormSqComponent separableFormAt
  rfl

/-- **Frame witness for `riemannianFiberNormSq`.** There is a `g(x)`-orthonormal frame
`e : Fin n → TangentSpace I x` (with `n = Module.finrank ℝ (TangentSpace I x)`), packaged as
a `Module.Basis`, such that `riemannianFiberNormSq g r s x T` equals the double sum over
multi-indices of the squared frame components. -/
private lemma riemannianFiberNormSq_frame_witness
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x)
      (bse : Module.Basis (Fin n) ℝ (TangentSpace I x)),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i : Fin n, bse i = e i) ∧
      (∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) ∧
      ∀ T : TensorRSSpace r s I x,
        riemannianFiberNormSq (I := I) (M := M) g r s x T =
          ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
            fiberNormSqComponent (I := I) (M := M) g x r s T n e K J ^ 2 := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  letI nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  letI ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  have hinner_eq : ∀ u v : TangentSpace I x, (inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  refine ⟨n, fun i => eob i, eob.toBasis, rfl, ?_, ?_, ?_⟩
  · intro i
    rw [OrthonormalBasis.coe_toBasis]
  · intro a b
    have horth : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horth a b
    rw [← hinner_eq (eob a) (eob b)]
    exact hite
  · intro T
    rw [show riemannianFiberNormSq (I := I) (M := M) g r s x T =
        ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x r s T n (fun i => eob i) K J from rfl]
    refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => ?_))
    rfl

/-- **Fibre-norm bridge.** The intrinsic frame-based `g`-induced squared fibre norm
`riemannianFiberNormSq` coincides with the model Gram-matrix-based pointwise inner product
`tensorInnerPointwise` evaluated on the trivialized model tensor `TensorRSSpace.toModel T`.
Both compute the same `g`-induced fibre norm squared, via genuinely different routes (a
`g`-orthonormal frame versus the inverse Gram matrix on the fixed model basis); their
equality is the reconciliation of the two representations. -/
theorem riemannianFiberNormSq_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x T =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T)
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) T) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hrepr⟩ :=
    riemannianFiberNormSq_frame_witness (I := I) (M := M) g r s x
  have hn' : n = Module.finrank ℝ E := hn
  subst hn'
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then (1 : ℝ) else 0 := by
    intro a b; rw [hbse a, hbse b]; exact horth a b
  rw [hrepr T]
  set Tm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) T with hTm_def
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x Tm Tm =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm)
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (r + s)
    bse hbse_orth _ _]
  rw [← Fintype.sum_equiv (Fin.appendEquiv r s)
    (fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
      fiberNormSqComponent (I := I) (M := M) g x r s T (Module.finrank ℝ E) e p.1 p.2 ^ 2)
    (fun φ : Fin (r + s) → Fin (Module.finrank ℝ E) =>
      (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) (fun k => bse (φ k)) *
        (lowerAllUpperIndices (I := I) (M := M) g r s x Tm) (fun k => bse (φ k)))
    ?_]
  · rw [Fintype.sum_prod_type]
  · intro p
    have hbse_e : ∀ i : Fin (Module.finrank ℝ E), bse i = e i := hbse
    have happend :
        (fun k => bse ((Fin.appendEquiv r s) p k)) =
          Fin.append (fun k => e (p.1 k)) (fun j => e (p.2 j)) := by
      funext k
      simp only [hbse_e, Fin.appendEquiv_apply]
      induction k using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simp only [Fin.append_right]
    dsimp only
    rw [happend, hTm_def, pow_two]
    congr 1 <;>
      exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x T
        (Module.finrank ℝ E) e p.1 p.2).symm

/-- **Bilinear fibre-inner bridge in a frame.** For a `g(x)`-orthonormal frame `e`
(packaged as a `Module.Basis bse`, `n = Module.finrank ℝ (TangentSpace I x)`), the model
Gram-matrix-based pointwise inner product of two `(r, s)`-tensors `A`, `B` is the
double-multi-index sum of the products of their frame components. This is the bilinear
generalization of `riemannianFiberNormSq_eq_tensorInnerPointwise` (whose diagonal `A = B`
case is the squared-norm statement); the proof ports verbatim, using the *bilinear* model
Parseval `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame` and the per-component append
identity for each argument separately. -/
theorem tensorInnerPointwise_eq_sum_componentS_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ a b : Fin n, g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (A B : TensorRSSpace r s I x) :
    tensorInnerPointwise (I := I) (M := M) g r s x
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) A)
        (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
          (r := r) (s := s) (x := x) B) =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        fiberNormSqComponent (I := I) (M := M) g x r s A n e K J *
          fiberNormSqComponent (I := I) (M := M) g x r s B n e K J := by
  classical
  subst hn
  have hbse_orth : ∀ a b, g.inner x (bse a) (bse b) = if a = b then (1 : ℝ) else 0 := by
    intro a b; rw [hbse a, hbse b]; exact horth a b
  set Am := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) A with hAm_def
  set Bm := TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
    (r := r) (s := s) (x := x) B with hBm_def
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x Am Bm =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g x
        (lowerAllUpperIndices (I := I) (M := M) g r s x Am)
        (lowerAllUpperIndices (I := I) (M := M) g r s x Bm) from rfl]
  rw [tensorInnerPointwise_0s_eq_diag_sum_orthoFrame (I := I) (M := M) g x (r + s)
    bse hbse_orth _ _]
  rw [← Fintype.sum_equiv (Fin.appendEquiv r s)
    (fun p : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) =>
      fiberNormSqComponent (I := I) (M := M) g x r s A (Module.finrank ℝ E) e p.1 p.2 *
        fiberNormSqComponent (I := I) (M := M) g x r s B (Module.finrank ℝ E) e p.1 p.2)
    (fun φ : Fin (r + s) → Fin (Module.finrank ℝ E) =>
      (lowerAllUpperIndices (I := I) (M := M) g r s x Am) (fun k => bse (φ k)) *
        (lowerAllUpperIndices (I := I) (M := M) g r s x Bm) (fun k => bse (φ k)))
    ?_]
  · rw [Fintype.sum_prod_type]
  · intro p
    have hbse_e : ∀ i : Fin (Module.finrank ℝ E), bse i = e i := hbse
    have happend :
        (fun k => bse ((Fin.appendEquiv r s) p k)) =
          Fin.append (fun k => e (p.1 k)) (fun j => e (p.2 j)) := by
      funext k
      simp only [hbse_e, Fin.appendEquiv_apply]
      induction k using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right i => simp only [Fin.append_right]
    dsimp only
    rw [happend, hAm_def, hBm_def]
    congr 1
    · exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x A
        (Module.finrank ℝ E) e p.1 p.2).symm
    · exact (lower_toModel_append_eq_fiberNormSqComponent (I := I) (M := M) g r s x B
        (Module.finrank ℝ E) e p.1 p.2).symm

open MeasureTheory in
/-- Global `L²` corollary: the squared metric `L²` norm of a tensor section field equals the
integral of the intrinsic Riemannian fibre norm of its bundle lift. -/
theorem tensorL2Norm_sq_eq_integral_riemannianFiberNormSq
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : ∀ x, TensorRSSpace r s I x) :
    tensorL2Norm (I := I) (M := M) g r s
          (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := r) (s := s) (x := x) (T x)) ^ 2
      = ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (T x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [tensorL2Norm_def, Real.sq_sqrt (by
        unfold tensorL2Inner
        refine integral_nonneg (fun x => ?_)
        exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _)]
  unfold tensorL2Inner
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  exact (riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (T x)).symm

end Connection
end Integral
end DifferentialGeometry

end
