import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Order2Equivalence
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Sobolev.Embedding.RawConnLapToHsOrderDropping

/-!
# Discharge of the order-`2` Gårding norm-equivalence predicate `Order2NormEquivOnSmooth`

The predicate `Order2NormEquivOnSmooth g r s Nspec C₁ C₂`
(`SobolevScale/Order2Equivalence.lean`) packages the order-`2`
interior-elliptic-regularity ("Gårding") two-sided norm comparison between the
intrinsic order-`2` chart-Sobolev norm `(tensorPouSobolevHsNorm g 2 T).toReal`
and a reference spectral order-`2` norm `Nspec T`, on the common dense subspace
of smooth compactly-supported sections.

This file **discharges** that predicate — chart-locality-freely, with no
`HasLocallyConstantChartAt` hypothesis — for the rank-`(0, 2)` reference norm
```
Nspec T := ∑_{j ∈ range 3} ‖toL2 (Δ_∇^j T)‖_{L²},
```
the sum of the `L²` norms of the first three rough-connection-Laplacian iterates
`Δ_∇^j T = rawTensorConnLapIter g 0 2 j T` (`j = 0, 1, 2`).  Both directions are
now available unconditionally on disk:

* **PoU → spectral** (`(tensorPouSobolevHsNorm g 2 T).toReal ≤ C₂ · Nspec T`) is the
  all-orders intrinsic Gårding estimate
  `exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter g 2 2`
  (`AllOrderGardingConstant.lean`), now sorry-free, instantiated at order `k = 2`.

* **spectral → PoU** (`Nspec T ≤ C₁ · (tensorPouSobolevHsNorm g 2 T).toReal`) is
  assembled from the order-dropping completion bounds: each term
  `‖toL2 (Δ_∇^j T)‖ = ‖Δ_∇^j T‖` (`norm_toL2`) is controlled by
  `‖(Δ_∇^j T).toHs 0‖` (`exists_l2Norm_le_toHs_zero`), by `‖T.toHs j‖`
  (`exists_rawConnLapIter_toHs_le_toHs`, order-`0` target), and by `‖T.toHs 2‖`
  (`toHs_norm_mono`, `j ≤ 2`), which equals `(tensorPouSobolevHsNorm g 2 T).toReal`
  (`tensorPouSobolevHilbert_norm_eq`).

The resulting `exists_Order2NormEquivOnSmooth` is the precise consumer-needed
instance of `Order2NormEquivOnSmooth`: it is no longer an assumed hypothesis but
a proven theorem.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral
namespace SobolevScale

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The consumer-needed rank-`(0, 2)` spectral reference norm.**

`order2IterateNspec g T` is the sum of the `L²` norms of the first three
rough-connection-Laplacian iterates of a smooth compactly-supported
`(0, 2)`-tensor section `T`:
```
order2IterateNspec g T := ∑_{j ∈ range 3} ‖toL2 (Δ_∇^j T)‖_{L²},   Δ_∇^j = rawTensorConnLapIter g 0 2 j.
```
This is exactly the spectral-side ("`Δ_∇`-`L²`") order-`2` reference norm appearing
on the right of the all-orders Gårding estimate
`exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter` at order `k = 2`, i.e. the
`Nspec` for which the order-`2` Gårding norm-equivalence predicate
`Order2NormEquivOnSmooth` is discharged below. -/
def order2IterateNspec (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) : ℝ :=
  ∑ j ∈ Finset.range (2 + 1),
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖

/-- The reference norm `order2IterateNspec` is nonnegative. -/
theorem order2IterateNspec_nonneg (g : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) :
    0 ≤ order2IterateNspec (I := I) (M := M) g T :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- **The spectral → PoU direction of the order-`2` Gårding comparison.**

There is a nonnegative constant `C₁` such that for every smooth compactly-supported
`(0, 2)`-tensor section `T`,
```
∑_{j ∈ range 3} ‖toL2 (Δ_∇^j T)‖_{L²} ≤ C₁ · (tensorPouSobolevHsNorm g 2 T).toReal.
```
Each Laplacian-iterate term is controlled by the order-`2` chart-Sobolev norm by
peeling the rough Laplacian iterates onto the order axis: `‖toL2 (Δ_∇^j T)‖` equals
the metric `L²` norm `‖Δ_∇^j T‖` (`norm_toL2`), is bounded by `‖(Δ_∇^j T).toHs 0‖`
(`exists_l2Norm_le_toHs_zero`), by `‖T.toHs j‖` (`exists_rawConnLapIter_toHs_le_toHs`
at inner order `0`), and finally by `‖T.toHs 2‖` (`toHs_norm_mono`, since `j ≤ 2`),
which is `(tensorPouSobolevHsNorm g 2 T).toReal` (`tensorPouSobolevHilbert_norm_eq`).
Summing the three terms gives the constant `C₁`. -/
theorem exists_order2IterateNspec_le_tensorPouSobolevHsNorm
    (g : SmoothRiemannianMetric I M) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      ∀ T : SmoothCcTensor g 0 2,
        order2IterateNspec (I := I) (M := M) g T ≤
          C₁ * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
  classical

  obtain ⟨Cl2, hCl2_nn, hCl2⟩ :=
    exists_l2Norm_le_toHs_zero (I := I) (M := M) g

  set Cdrop : ℕ → ℝ := fun j =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose with hCdrop_def
  have hCdrop_nn : ∀ j : ℕ, 0 ≤ Cdrop j := fun j =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose_spec.1
  have hCdrop_spec : ∀ (j : ℕ) (T : SmoothCcTensor g 0 2),
      ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
          (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ := fun j T =>
    (exists_rawConnLapIter_toHs_le_toHs (I := I) (M := M) g j 0).choose_spec.2 T

  set Cj : ℕ → ℝ := fun j => Cl2 * Cdrop j with hCj_def
  have hCj_nn : ∀ j : ℕ, 0 ≤ Cj j := fun j => mul_nonneg hCl2_nn (hCdrop_nn j)

  have hterm : ∀ (j : ℕ), j ≤ 2 → ∀ T : SmoothCcTensor g 0 2,
      ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
        Cj j * (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal := by
    intro j hj T
    set N2 : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal with hN2_def
    have hN2_nn : 0 ≤ N2 := ENNReal.toReal_nonneg

    have hstep2 :
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
          Cl2 * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ :=
      hCl2 (rawTensorConnLapIter (I := I) g 0 2 j T)

    have hstep3 :
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ ≤
          Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ :=
      hCdrop_spec j T

    have hstep4 :
        ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖ ≤ N2 := by
      rw [hN2_def, ← tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g 2 T]
      have h0j : (0 + j) ≤ 2 := by omega
      exact toHs_norm_mono (I := I) (M := M) (g := g) (r := 0) (s := 2) h0j T
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖
        ≤ Cl2 * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) 0
            (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := hstep2
      _ ≤ Cl2 * (Cdrop j * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (0 + j) T‖) :=
            mul_le_mul_of_nonneg_left hstep3 hCl2_nn
      _ ≤ Cl2 * (Cdrop j * N2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hstep4 (hCdrop_nn j)) hCl2_nn
      _ = (Cl2 * Cdrop j) * N2 := by ring
      _ = Cj j * N2 := by rw [hCj_def]

  refine ⟨∑ j ∈ Finset.range (2 + 1), Cj j,
    Finset.sum_nonneg (fun j _ => hCj_nn j), fun T => ?_⟩
  set N2 : ℝ := (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal with hN2_def
  have hN2_nn : 0 ≤ N2 := ENNReal.toReal_nonneg
  calc order2IterateNspec (I := I) (M := M) g T
      = ∑ j ∈ Finset.range (2 + 1),
          ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)‖ := rfl
    _ ≤ ∑ j ∈ Finset.range (2 + 1), Cj j * N2 := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) T
    _ = (∑ j ∈ Finset.range (2 + 1), Cj j) * N2 := by
        rw [Finset.sum_mul]

/-- **The PoU → spectral direction of the order-`2` Gårding comparison.**

There is a nonnegative constant `C₂` such that for every smooth compactly-supported
`(0, 2)`-tensor section `T`,
```
(tensorPouSobolevHsNorm g 2 T).toReal ≤ C₂ · ∑_{j ∈ range 3} ‖toL2 (Δ_∇^j T)‖_{L²}.
```
This is exactly the order-`2` (`k = 2`) instance of the now-sorry-free all-orders
intrinsic Gårding estimate
`exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter g 2 2`. -/
theorem exists_tensorPouSobolevHsNorm_le_order2IterateNspec
    (g : SmoothRiemannianMetric I M) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ T : SmoothCcTensor g 0 2,
        (tensorPouSobolevHsNorm (I := I) (M := M) g 2 T).toReal ≤
          C₂ * order2IterateNspec (I := I) (M := M) g T := by
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    DifferentialGeometry.Integral.Connection.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 2
  exact ⟨C₂, hC₂_nn, fun T => hC₂ T⟩

/-- **Discharge of the order-`2` Gårding norm-equivalence predicate (rank `(0, 2)`).**

For the rank-`(0, 2)` spectral reference norm
`order2IterateNspec g T = ∑_{j ∈ range 3} ‖toL2 (Δ_∇^j T)‖_{L²}`, the order-`2`
two-sided norm comparison `Order2NormEquivOnSmooth g 0 2 (order2IterateNspec g) C₁ C₂`
holds with explicit nonnegative constants: it conjoins the spectral → PoU bound
`exists_order2IterateNspec_le_tensorPouSobolevHsNorm` and the PoU → spectral all-orders
Gårding estimate `exists_tensorPouSobolevHsNorm_le_order2IterateNspec` (the order-`2`
instance of `exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter`, now sorry-free).

This turns `Order2NormEquivOnSmooth` from an isolated hypothesis into a proven
theorem for the consumer-needed reference norm, chart-locality-freely (no
`HasLocallyConstantChartAt`). -/
theorem exists_Order2NormEquivOnSmooth (g : SmoothRiemannianMetric I M) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      Order2NormEquivOnSmooth (I := I) (M := M) g 0 2
        (order2IterateNspec (I := I) (M := M) g) C₁ C₂ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    exists_order2IterateNspec_le_tensorPouSobolevHsNorm (I := I) (M := M) g
  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    exists_tensorPouSobolevHsNorm_le_order2IterateNspec (I := I) (M := M) g
  exact ⟨C₁, C₂, hC₁_nn, hC₂_nn, hC₁, hC₂⟩

end SobolevScale
end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
