import DifferentialGeometry.Integral.Connection.TensorConnLapSecondGradientL2Bound

/-!
# The intrinsic order-`2` covariant Gårding `L²` estimate

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, this file assembles the **intrinsic order-`2` covariant Gårding
inequality** for a smooth compactly-supported `(0, 2)`-tensor field `T`:

```
‖∇²T‖²_{L²} ≤ C · (‖Δ_∇ T‖²_{L²} + ‖T‖²_{L²}),
```

where `∇²T = covGrad g 0 3 (covGrad g 0 2 T)` is the iterated covariant gradient
(a `(0, 4)`-tensor field), `∇T = covGrad g 0 2 T` is the covariant gradient (a
`(0, 3)`-tensor field), and `Δ_∇ T = rawTensorConnLapSmooth g 0 2 T` is the rough
(connection) Laplacian. This is the covariant core of the second-order
elliptic-regularity estimate: it controls the full second covariant derivative of
`T` in `L²` by the rough Laplacian and `T` itself, with the curvature obstruction
absorbed into the constant.

## The assembly

The estimate is the diagonal `(0, 3)` Green identity combined with the
rough-Laplacian / covariant-gradient commutator and the order-`1` covariant
gradient control:

* **Diagonal `(0, 3)` Green identity** (`covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner`):
  `‖∇²T‖²_{L²} = − ⟨Δ_∇(∇T), ∇T⟩_{L²}`, where `Δ_∇(∇T) = rawTensorConnLapSmooth
  g 0 3 (∇T)` is the rough Laplacian of the `(0, 3)`-tensor gradient field.

* **The rough-Laplacian / covariant-gradient commutator** (supplied as a
  hypothesis): `Δ_∇(∇T) = ∇(Δ_∇ T) + Curv` as `(0, 3)`-tensor fields, where
  `∇(Δ_∇ T) = covGrad g 0 2 (Δ_∇ T)` is the gradient of the rough Laplacian and
  `Curv` is the explicit third-order curvature defect produced when the rough
  Laplacian is commuted past one extra covariant direction (the curvature
  contraction of the once-derived tensor, summed over the frame).

* **The Laplacian-gradient `L²` collapse**
  (`covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq`):
  `⟨∇(Δ_∇ T), ∇T⟩_{L²} = − ‖Δ_∇ T‖²_{L²}` (self-adjointness of `Δ_∇` on the
  diagonal).

* **The curvature `L²` control** (supplied as a hypothesis): `‖Curv‖_{L²} ≤ C₀ ·
  ‖∇T‖_{L²}`. The constant `C₀` is uniform in `T` on a compact manifold (it is the
  sup norm of the Riemann curvature).

* **The order-`1` covariant gradient control**
  (`covGrad_l2NormSq_le_rawConnLap_mul_self`): `‖∇T‖²_{L²} ≤ ‖Δ_∇ T‖_{L²} ·
  ‖T‖_{L²}`.

Chaining these and applying Cauchy–Schwarz to the `⟨Curv, ∇T⟩` cross term, then
Young's inequality to the `‖Δ_∇ T‖ · ‖T‖` product, gives
`‖∇²T‖² ≤ (1 + C₀/2) · (‖Δ_∇ T‖² + ‖T‖²)`.

## Inputs

The two genuinely-curvature-dependent facts — the **commutator identity** and the
**curvature `L²` bound** — are exposed as explicit hypotheses on a packaged
defect field `Curv : SmoothCcTensor g 0 3`. They are the order-`2` Weitzenböck /
Ricci-curvature inputs; everything else (the two Green identities, the order-`1`
control, Cauchy–Schwarz, Young) is discharged here from the committed `L²`
machinery. This isolates the pure-analysis assembly from the pointwise
curvature-reconciliation algebra.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the tensor
rank from `(0, s)` to `(0, s + 1)`.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

set_option linter.unusedSectionVars false in
/-- **Cross-pairing split of the diagonal Green identity.** Assuming the
rough-Laplacian / covariant-gradient commutator
`Δ_∇(∇T) = ∇(Δ_∇ T) + Curv` (`hcomm`), the `L²` pairing of `Δ_∇(∇T)` with `∇T`
splits as minus the squared `L²` norm of `Δ_∇ T` plus the curvature cross term:

```
⟨Δ_∇(∇T), ∇T⟩_{L²} = − ‖Δ_∇ T‖²_{L²} + ⟨Curv, ∇T⟩_{L²}.
```
-/
theorem rawConnLap_three_l2Inner_covGrad_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv) :
    tensorL2Inner (I := I) (M := M) g 0 3
        (rawTensorConnLapSmooth (I := I) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun
        (covGrad (I := I) (M := M) g 0 2 T).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
        tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun
          (covGrad (I := I) (M := M) g 0 2 T).toFun := by
  classical
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T with hS_def
  set GΔ : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T) with hGΔ_def
  rw [hcomm]
  rw [SmoothCcTensor.toFun_add]
  rw [tensorL2Inner_add_left (I := I) (M := M) g 0 3 GΔ.toFun Curv.toFun S.toFun
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) GΔ S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv S)]
  rw [hGΔ_def, hS_def]
  rw [covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq (I := I) (M := M) g T]

set_option linter.unusedSectionVars false in
/-- **Intrinsic order-`2` covariant Gårding `L²` estimate.** For a smooth
compactly-supported `(0, 2)`-tensor field `T` on a closed Riemannian manifold,
given the rough-Laplacian / covariant-gradient commutator
`Δ_∇(∇T) = ∇(Δ_∇ T) + Curv` (`hcomm`) with an explicit curvature defect field
`Curv` satisfying the curvature `L²` bound `‖Curv‖_{L²} ≤ C₀ · ‖∇T‖_{L²}`
(`hcurv`), there is a nonnegative constant `C` with

```
‖∇²T‖²_{L²} ≤ C · (‖Δ_∇ T‖²_{L²} + ‖T‖²_{L²}),
```

where `∇²T = covGrad g 0 3 (covGrad g 0 2 T)`, `∇T = covGrad g 0 2 T`, and
`Δ_∇ T = rawTensorConnLapSmooth g 0 2 T`. The constant `C = 1 + C₀ / 2` is the
order-`2` elliptic-regularity constant: the leading `1` from the Laplacian-gradient
collapse, the `C₀ / 2` from absorbing the curvature cross term via Young's
inequality and the order-`1` control. -/
theorem secondCovGrad_l2NormSq_le_rawConnLap_add_self
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (Curv : SmoothCcTensor g 0 3) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hcomm :
      rawTensorConnLapSmooth (I := I) g 0 3 (covGrad (I := I) (M := M) g 0 2 T) =
        covGrad (I := I) (M := M) g 0 2 (rawTensorConnLapSmooth (I := I) g 0 2 T)
          + Curv)
    (hcurv :
      tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun ≤
        C₀ * tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T).toFun) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T)).toFun ^ 2 ≤
      (1 + C₀ / 2) *
        (tensorL2Norm (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun ^ 2 +
          tensorL2Norm (I := I) (M := M) g 0 2 T.toFun ^ 2) := by
  classical
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T with hS_def
  set nGrad : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 S.toFun with hnGrad_def
  set nLap : ℝ := tensorL2Norm (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun with hnLap_def
  set nT : ℝ := tensorL2Norm (I := I) (M := M) g 0 2 T.toFun with hnT_def
  set nCurv : ℝ := tensorL2Norm (I := I) (M := M) g 0 3 Curv.toFun with hnCurv_def
  have hnGrad_nn : 0 ≤ nGrad := tensorL2Norm_nonneg (I := I) (M := M) g 0 3 _
  have hnLap_nn : 0 ≤ nLap := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hnT_nn : 0 ≤ nT := tensorL2Norm_nonneg (I := I) (M := M) g 0 2 _
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3
            (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T
  have hsplit :
      tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3 S).toFun S.toFun =
        - nLap ^ 2 +
          tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hS_def, hnLap_def]
    exact rawConnLap_three_l2Inner_covGrad_eq (I := I) (M := M) g T Curv hcomm
  have hcombined :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        nLap ^ 2 - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun := by
    rw [hgreen, hsplit]; ring
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 Curv.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) Curv)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) Curv S)
  have hcross_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 Curv.toFun S.toFun ≤ nCurv * nGrad := by
    rw [hnCurv_def, hnGrad_def]
    exact le_trans (neg_le_abs _) hcs
  have hcurv' : nCurv ≤ C₀ * nGrad := by rw [hnCurv_def, hnGrad_def]; exact hcurv
  have hgrad_sq_nn : 0 ≤ nGrad := hnGrad_nn
  have hstep1 :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 ≤
        nLap ^ 2 + C₀ * nGrad ^ 2 := by
    rw [hcombined]
    have : nCurv * nGrad ≤ C₀ * nGrad * nGrad :=
      mul_le_mul_of_nonneg_right hcurv' hnGrad_nn
    nlinarith [hcross_le, this]
  have horder1 : nGrad ^ 2 ≤ nLap * nT := by
    rw [hnGrad_def, hS_def, hnLap_def, hnT_def]
    exact covGrad_l2NormSq_le_rawConnLap_mul_self (I := I) (M := M) g T
  have hyoung : nLap * nT ≤ (nLap ^ 2 + nT ^ 2) / 2 := by nlinarith [sq_nonneg (nLap - nT)]
  set nHess : ℝ := tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
    (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 with hnHess_def
  have hstep1' : nHess ≤ nLap ^ 2 + C₀ * nGrad ^ 2 := hstep1
  have hgrad_le : C₀ * nGrad ^ 2 ≤ C₀ * ((nLap ^ 2 + nT ^ 2) / 2) := by
    have h1 : C₀ * nGrad ^ 2 ≤ C₀ * (nLap * nT) := by nlinarith [horder1, hC₀]
    have h2 : C₀ * (nLap * nT) ≤ C₀ * ((nLap ^ 2 + nT ^ 2) / 2) := by nlinarith [hyoung, hC₀]
    linarith [h1, h2]
  nlinarith [hstep1', hgrad_le, sq_nonneg nT, hC₀]

end Connection
end Integral
end DifferentialGeometry

end
