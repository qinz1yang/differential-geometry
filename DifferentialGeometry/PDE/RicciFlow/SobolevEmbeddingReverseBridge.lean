import DifferentialGeometry.PDE.RicciFlow.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseBase

/-!
# The reverse Hebey-Sobolev bridge: order-`2k` chart Hilbert-Schmidt norm
controlled by intrinsic `L²` norms of the iterated covariant gradients

This file composes the two halves of the reverse Sobolev comparison into the
single headline bound: the order-`2k` partition-of-unity-weighted chart-Sobolev
Hilbert-Schmidt norm of a smooth compactly-supported `(r, s)`-tensor `T` is
controlled by a single constant times the sum, over `j ≤ 2k`, of the intrinsic
metric `L²` norms of the iterated covariant gradients `∇^j T`:

  `(tensorPouSobolevHsNorm g k T).toReal
     ≤ C · ∑_{j ∈ range (2k + 1)} tensorL2Norm g r (s + j) (∇^j T).toFun`.

## Composition

* The **order-peeling half**
  `exists_tensorPouSobolevHsNorm_le_iteratedCovGrad_zero_sum` bounds, in
  `ℝ≥0∞`, the order-`2k` chart-Sobolev norm of `T` by `ofReal C_B` times the
  sum over `j ≤ 2k` of the order-`0` chart-Sobolev norms of `∇^j T`.

* The **base half** `tensorPouSobolevHsNorm_zero_le_tensorL2Norm` bounds the
  order-`0` chart-Sobolev norm of an `(r, s')`-tensor `S` (via its real part) by
  a constant times the intrinsic `L²` norm `tensorL2Norm g r s' S.toFun`.

Applying the base half at each valence `(r, s + j)` to `S = ∇^j T`, taking a
finite maximum of the per-`j` base constants over `j ∈ range (2k + 1)`, and
discharging the `ℝ≥0∞ ↔ ℝ` conversions with `tensorPouSobolevHsNorm_lt_top`
(every order-`0` norm is finite) and `ENNReal.toReal_le_of_le_ofReal`, yields the
headline real-valued bound.

## Main result

* `exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum` —
  the headline reverse Hebey-Sobolev bridge.
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

section ReverseBridge

/-- **The reverse Hebey-Sobolev bridge.** There is a non-negative constant `C`
(depending only on `(g, r, s, k)`) such that for every smooth
compactly-supported `(r, s)`-tensor section `T`, the order-`2k` Hilbert-Schmidt
partition-of-unity-weighted chart-Sobolev norm of `T` is controlled by the sum,
over `j ≤ 2k`, of the intrinsic metric `L²` norms of the iterated covariant
gradients `∇^j T`:
`(tensorPouSobolevHsNorm g k T).toReal ≤
  C · ∑_{j ∈ range (2k + 1)} tensorL2Norm g r (s + j) (iteratedCovGrad g r s j T).toFun`.

This is the reverse (lower-order recovery) half of the Hebey multi-order Sobolev
equivalence: the full order-`2k` chart-Sobolev content of `T` is bounded, up to
uniform Christoffel-controlled constants, by the bare `L²` content of the first
`2k` iterated covariant gradients. -/
theorem exists_tensorPouSobolevHsNorm_toReal_le_iteratedCovGrad_tensorL2Norm_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : SmoothCcTensor g r s,
        (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            tensorL2Norm (I := I) (M := M) g r (s + j)
              (iteratedCovGrad g r s j T).toFun := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    exists_tensorPouSobolevHsNorm_le_iteratedCovGrad_zero_sum
      (I := I) (M := M) g r s k
  set CAfun : ℕ → ℝ := fun j =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose with hCAfun_def
  have hCAfun_nn : ∀ j : ℕ, 0 ≤ CAfun j := fun j =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose_spec.1
  have hCAfun_spec : ∀ (j : ℕ) (S : SmoothCcTensor g r (s + j)),
      (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ≤
        CAfun j * tensorL2Norm (I := I) (M := M) g r (s + j) S.toFun := fun j S =>
    (tensorPouSobolevHsNorm_zero_le_tensorL2Norm
      (I := I) (M := M) g r (s + j)).choose_spec.2 S
  set CAmax : ℝ :=
    (Finset.range (2 * k + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos (2 * k))⟩ CAfun with hCAmax_def
  have hCAmax_nn : 0 ≤ CAmax :=
    le_trans (hCAfun_nn 0)
      (Finset.le_sup' CAfun (Finset.mem_range.mpr (Nat.succ_pos (2 * k))))
  have hCAfun_le_max : ∀ j ∈ Finset.range (2 * k + 1), CAfun j ≤ CAmax :=
    fun j hj => Finset.le_sup' CAfun hj
  refine ⟨CB * CAmax, mul_nonneg hCB_nn hCAmax_nn, fun T => ?_⟩
  set L : ℕ → ℝ := fun j =>
    tensorL2Norm (I := I) (M := M) g r (s + j) (iteratedCovGrad g r s j T).toFun
    with hL_def
  have hL_nn : ∀ j : ℕ, 0 ≤ L j := fun j =>
    tensorL2Norm_nonneg (I := I) (M := M) g r (s + j)
      (iteratedCovGrad g r s j T).toFun
  have h_term_le : ∀ j ∈ Finset.range (2 * k + 1),
      tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T) ≤
        ENNReal.ofReal (CAmax * L j) := by
    intro j hj
    have h_ne_top :
        tensorPouSobolevHsNorm (I := I) (M := M) g 0
          (iteratedCovGrad g r s j T) ≠ ⊤ :=
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g 0
        (iteratedCovGrad g r s j T)).ne
    rw [← ENNReal.ofReal_toReal h_ne_top]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (tensorPouSobolevHsNorm (I := I) (M := M) g 0
            (iteratedCovGrad g r s j T)).toReal
        ≤ CAfun j * L j := hCAfun_spec j (iteratedCovGrad g r s j T)
      _ ≤ CAmax * L j :=
          mul_le_mul_of_nonneg_right (hCAfun_le_max j hj) (hL_nn j)
  have h_sum_le :
      ∑ j ∈ Finset.range (2 * k + 1),
          tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T) ≤
        ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
    calc ∑ j ∈ Finset.range (2 * k + 1),
            tensorPouSobolevHsNorm (I := I) (M := M) g 0 (iteratedCovGrad g r s j T)
        ≤ ∑ j ∈ Finset.range (2 * k + 1), ENNReal.ofReal (CAmax * L j) :=
          Finset.sum_le_sum h_term_le
      _ = ENNReal.ofReal (∑ j ∈ Finset.range (2 * k + 1), CAmax * L j) :=
          (ENNReal.ofReal_sum_of_nonneg
            (fun j _ => mul_nonneg hCAmax_nn (hL_nn j))).symm
      _ = ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          rw [Finset.mul_sum]
  have h_enn :
      tensorPouSobolevHsNorm (I := I) (M := M) g k T ≤
        ENNReal.ofReal
          (CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
    refine (hCB T).trans ?_
    calc ENNReal.ofReal CB *
            ∑ j ∈ Finset.range (2 * k + 1),
              tensorPouSobolevHsNorm (I := I) (M := M) g 0
                (iteratedCovGrad g r s j T)
        ≤ ENNReal.ofReal CB *
            ENNReal.ofReal (CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          exact mul_le_mul_of_nonneg_left h_sum_le (zero_le _)
      _ = ENNReal.ofReal
            (CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j) := by
          rw [← ENNReal.ofReal_mul hCB_nn, mul_assoc]
  have h_rhs_nn :
      0 ≤ CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j :=
    mul_nonneg (mul_nonneg hCB_nn hCAmax_nn)
      (Finset.sum_nonneg (fun j _ => hL_nn j))
  have h_toReal :=
    ENNReal.toReal_le_of_le_ofReal h_rhs_nn h_enn
  calc (tensorPouSobolevHsNorm (I := I) (M := M) g k T).toReal
      ≤ CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1), L j := h_toReal
    _ = CB * CAmax * ∑ j ∈ Finset.range (2 * k + 1),
          tensorL2Norm (I := I) (M := M) g r (s + j)
            (iteratedCovGrad g r s j T).toFun := rfl

end ReverseBridge

end DifferentialGeometry.PDE.RicciFlow

end
