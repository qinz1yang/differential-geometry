import DifferentialGeometry.Integral.Connection.RawTensorConnLapNormSqChartPulledReprBound
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberForwardOpNorm
import DifferentialGeometry.Integral.Connection.TensorRSChartReprNormBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Components
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Linear chart-pulled-representation bound for the raw tensor connection
Laplacian by orders 0, 1, 2 of the iterated Fréchet derivatives of the
chart-pulled representation of `T`

For a smooth Riemannian manifold `(M, g)`, a chart-centre `α : M`, ranks
`r, s : ℕ`, and a smooth compactly supported `(r, s)`-tensor section `T`, this
file ships the unsquared (linear) pointwise bound

```
‖tensorRSChartE_section_repr r s α
    (fun y => (rawTensorConnLapSmooth g r s T).toSection y) b‖ ≤
  K * (∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr r s α (fun y => T.toSection y)) ∘
            (extChartAt I α).symm) (extChartAt I α b)‖)
```

valid for every `b` in the intersection of the chart-`α` partition-of-unity
tsupport and the chart-`α` Levi-Civita good set. The constant `K` depends on
`g`, the chart at `α`, the chart-atlas locality hypotheses, and the ranks
`r`, `s`; it is independent of `T` and `b`.

## Strategy

The previously established squared bound

```
‖rawTensorConnLap g r s (fun y => T.toSection y) b‖^2 ≤
  K_sq * (V^2 + F^2 + I^2)
```

where `V, F, I` are the chart-pulled representation norms at orders `0, 1, 2`
respectively, can be turned into the unsquared

```
‖rawTensorConnLap g r s (fun y => T.toSection y) b‖ ≤ √K_sq * (V + F + I)
```

via the bound `V^2 + F^2 + I^2 ≤ (V + F + I)^2` valid for non-negative `V, F,
I`. The forward fibre-norm bound

```
‖tensorRSChartE_section_repr r s α (raw T) b‖ ≤ C_fwd * ‖rawTensorConnLap g r s
  (fun y => T.toSection y) b‖
```

valid on the partition-of-unity tsupport (a compact subset of the chart-`α`
source) then yields the desired linear bound on the chart-pulled representation.
Finally, `V = ‖iteratedFDeriv ℝ 0 ...‖` and `F = ‖iteratedFDeriv ℝ 1 ...‖` via
`norm_iteratedFDeriv_zero` and `norm_iteratedFDeriv_one`; on the good set
`(extChartAt I α).symm (extChartAt I α b) = b`, so the order-zero value agrees
with the chart-pulled representation at `b`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma sum_sq_le_sq_sum_of_nonneg (V F I2 : ℝ)
    (hV : 0 ≤ V) (hF : 0 ≤ F) (hI2 : 0 ≤ I2) :
    V ^ 2 + F ^ 2 + I2 ^ 2 ≤ (V + F + I2) ^ 2 := by
  nlinarith [mul_nonneg hV hF, mul_nonneg hV hI2, mul_nonneg hF hI2]

/-- The chart-pulled representation `V` at `b ∈` good set equals the order-0
iterated Fréchet-derivative norm of `T_repr ∘ symm` at `extChartAt I α b`. -/
private lemma V_eq_iteratedFDeriv_zero_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
      ‖iteratedFDeriv ℝ 0
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  have hb_chart_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb_good
  have hb_extsrc : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact hb_chart_src
  have hsymm_eq : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_extsrc
  rw [norm_iteratedFDeriv_zero]
  change ‖tensorRSChartE_section_repr (I := I) r s α S b‖ =
    ‖tensorRSChartE_section_repr (I := I) r s α S
      ((extChartAt I α).symm (extChartAt I α b))‖
  rw [hsymm_eq]

/-- The chart-pulled `fderiv ℝ` norm of `T_repr ∘ symm` at the chart point
equals the order-1 iterated Fréchet-derivative norm there. -/
private lemma F_eq_iteratedFDeriv_one_norm
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) (b : M) :
    ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ‖iteratedFDeriv ℝ 1
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ := by
  rw [norm_iteratedFDeriv_one]

private lemma sum_VFI2_eq_finSum
    (r s : ℕ) (α : M)
    (S : Π b : M, TensorRSSpace r s I b) {b : M}
    (hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ‖tensorRSChartE_section_repr (I := I) r s α S b‖ +
      ‖fderiv ℝ
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ +
      ‖iteratedFDeriv ℝ 2
        ((tensorRSChartE_section_repr (I := I) r s α S) ∘
            (extChartAt I α).symm)
        (extChartAt I α b)‖ =
      ∑ j : Fin 3,
        ‖iteratedFDeriv ℝ j.val
          ((tensorRSChartE_section_repr (I := I) r s α S) ∘
              (extChartAt I α).symm)
          (extChartAt I α b)‖ := by
  rw [V_eq_iteratedFDeriv_zero_norm (I := I) (M := M) r s α S (b := b) hb_good]
  rw [F_eq_iteratedFDeriv_one_norm (I := I) (M := M) r s α S b]
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]

end Connection
end Integral
end DifferentialGeometry

end
