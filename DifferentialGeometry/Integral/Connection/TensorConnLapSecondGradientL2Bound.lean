import DifferentialGeometry.Integral.Connection.TensorConnLapGreenDivergenceIdentityGeneral
import DifferentialGeometry.Integral.Connection.TensorConnLapGradientL2Bound
import DifferentialGeometry.Integral.L2.SmoothSections.Integrability
import DifferentialGeometry.Integral.L2.Pairing.CauchySchwarz

/-!
# The order-`2` second-covariant-gradient `L²` control from the `(0, 3)` Green identity

For a closed smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file extracts, from the integrated `(0, 3)`
connection-Laplacian Green identity
`tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three`, the second-order
elliptic-regularity inequality

```
‖∇²T‖²_{L²} ≤ ‖Δ_∇(∇T)‖_{L²} · ‖∇T‖_{L²}
```

for every smooth compactly-supported `(0, 2)`-tensor field `T`. Here `∇T` is the
covariant gradient `covGrad g 0 2 T` (a `(0, 3)`-tensor field) and `∇²T` is the
iterated covariant gradient `covGrad g 0 3 (covGrad g 0 2 T)` (a `(0, 4)`-tensor
field), whose diagonal `L²` self-pairing is `‖∇²T‖²_{L²}`. The rough Laplacian
`Δ_∇(∇T) = rawTensorConnLapSmooth g 0 3 (covGrad g 0 2 T)` acts on the `(0, 3)`
gradient field.

This is the genuine order-`2` analogue of the committed order-`1` control
`covGrad_l2NormSq_le_rawConnLap_mul_self` (which bounds `‖∇T‖²` by
`‖Δ_∇ T‖·‖T‖`): it is the diagonal specialisation of the `(0, 3)` Green
identity at `S := covGrad g 0 2 T`, combined with the global `L²`
Cauchy–Schwarz inequality.

## The mechanism

Specialising the rank-`(0, 3)` Green identity at `v := S := covGrad g 0 2 T`
gives `⟨∇S, ∇S⟩_{L²} = − ⟨Δ_∇ S, S⟩_{L²}`. The left side is the squared `L²`
norm of the iterated covariant gradient `∇²T` (a non-negative quantity); the
right side is bounded in absolute value, via the global Cauchy–Schwarz
inequality `abs_tensorL2Inner_le` together with the square-integrability of
smooth compactly-supported sections, by `‖Δ_∇ S‖_{L²} · ‖S‖_{L²}`.

## Main results

* `covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner` — the diagonal `(0, 3)`
  Green identity `⟨∇²T, ∇²T⟩_{L²} = − ⟨Δ_∇(∇T), ∇T⟩_{L²}`.
* `secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad` — the headline
  second-order control `‖∇²T‖²_{L²} ≤ ‖Δ_∇(∇T)‖_{L²} · ‖∇T‖_{L²}`.

## Sign / order conventions

Geometer convention `Δ_∇ = -∇*∇` for the rough Laplacian
`rawTensorConnLapSmooth`. The covariant gradient `covGrad g 0 s` raises the
tensor rank from `(0, s)` to `(0, s + 1)`; iterating it twice from rank `(0, 2)`
produces the rank-`(0, 4)` object `∇²T` whose diagonal `L²` self-pairing is the
squared `L²` norm of the iterated second covariant derivative.
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
/-- **Diagonal `(0, 3)` Green identity at the gradient field.** For a smooth
compactly-supported `(0, 2)`-tensor field `T₀`, writing `S := ∇T₀ =
covGrad g 0 2 T₀` for its `(0, 3)`-tensor covariant gradient, the diagonal
`L²` self-pairing of `∇S = ∇²T₀` equals minus the `L²` pairing of the rough
Laplacian `Δ_∇ S` with `S`:

```
⟨∇²T₀, ∇²T₀⟩_{L²} = − ⟨Δ_∇(∇T₀), ∇T₀⟩_{L²}.
```
-/
lemma covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_three (I := I) (M := M) g
    (covGrad (I := I) (M := M) g 0 2 T₀)
    (covGrad (I := I) (M := M) g 0 2 T₀)

set_option linter.unusedSectionVars false in
/-- **Second-order covariant-gradient `L²` control.** For a smooth
compactly-supported `(0, 2)`-tensor field `T₀`, the squared `L²` norm of the
iterated covariant gradient `∇²T₀ = covGrad g 0 3 (covGrad g 0 2 T₀)` is
bounded by the product of the `L²` norms of the rough Laplacian `Δ_∇(∇T₀)` and
of the covariant gradient `∇T₀`:

```
‖∇²T₀‖²_{L²} ≤ ‖Δ_∇(∇T₀)‖_{L²} · ‖∇T₀‖_{L²}.
```

This is the order-`2` analogue of the committed order-`1` control
`covGrad_l2NormSq_le_rawConnLap_mul_self`. The proof is the diagonal `(0, 3)`
Green identity combined with the global `L²` Cauchy–Schwarz inequality. -/
theorem secondCovGrad_l2NormSq_le_rawConnLap_three_mul_covGrad
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀)).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3
          (rawTensorConnLapSmooth (I := I) g 0 3
            (covGrad (I := I) (M := M) g 0 2 T₀)).toFun *
        tensorL2Norm (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 T₀).toFun := by
  set S : SmoothCcTensor g 0 3 := covGrad (I := I) (M := M) g 0 2 T₀ with hS_def
  set ΔS : SmoothCcTensor g 0 3 := rawTensorConnLapSmooth (I := I) g 0 3 S
    with hΔS_def
  change tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
        (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 ≤
      tensorL2Norm (I := I) (M := M) g 0 3 ΔS.toFun *
        tensorL2Norm (I := I) (M := M) g 0 3 S.toFun
  have hgreen :
      tensorL2Norm (I := I) (M := M) g 0 (3 + 1)
          (covGrad (I := I) (M := M) g 0 3 S).toFun ^ 2 =
        - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun := by
    rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 (3 + 1)
      (covGrad (I := I) (M := M) g 0 3 S)]
    rw [hΔS_def, hS_def]
    exact covGrad_two_l2Inner_self_eq_neg_rawConnLap_three_inner (I := I) (M := M) g T₀
  rw [hgreen]
  have hcs := abs_tensorL2Inner_le (I := I) (M := M) g 0 3 ΔS.toFun S.toFun
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) ΔS)
    (SmoothCcTensor.memL2_toFun (I := I) (M := M) S)
    (SmoothCcTensor.integrable_inner_cross (I := I) (M := M) ΔS S)
  have hneg_le :
      - tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun ≤
        |tensorL2Inner (I := I) (M := M) g 0 3 ΔS.toFun S.toFun| :=
    neg_le_abs _
  exact le_trans hneg_le hcs

set_option linter.unusedSectionVars false in
/-- **Laplacian-gradient `L²` collapse.** For a smooth compactly-supported
`(0, 2)`-tensor field `T₀`, the `L²` inner product of the covariant gradient of
`Δ_∇ T₀` with the covariant gradient of `T₀` equals minus the squared `L²` norm
of `Δ_∇ T₀`:

```
⟨∇(Δ_∇ T₀), ∇T₀⟩_{L²} = − ‖Δ_∇ T₀‖²_{L²}.
```

This is the `(0, 2)` Green identity `green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed`
applied at the pair `(T₀, Δ_∇ T₀)`, together with the symmetry `tensorL2Inner_symm`
of the global `L²` pairing. -/
theorem covGrad_rawConnLap_l2Inner_covGrad_eq_neg_rawConnLap_normSq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀)).toFun
        (covGrad (I := I) (M := M) g 0 2 T₀).toFun =
      - tensorL2Norm (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T₀).toFun ^ 2 := by
  set ΔT₀ : SmoothCcTensor g 0 2 := rawTensorConnLapSmooth (I := I) g 0 2 T₀
    with hΔT₀_def
  rw [tensorL2Inner_symm (I := I) (M := M) g 0 (2 + 1)
    (covGrad (I := I) (M := M) g 0 2 ΔT₀).toFun
    (covGrad (I := I) (M := M) g 0 2 T₀).toFun]
  rw [green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed (I := I) (M := M) g T₀ ΔT₀]
  rw [hΔT₀_def]
  rw [tensorL2Norm_sq_toFun (I := I) (M := M) g 0 2
    (rawTensorConnLapSmooth (I := I) g 0 2 T₀)]

end Connection
end Integral
end DifferentialGeometry

end
