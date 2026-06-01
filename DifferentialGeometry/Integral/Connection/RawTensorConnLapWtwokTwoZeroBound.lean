import DifferentialGeometry.Integral.Connection.RawTensorConnLapWtwokTwoZeroSquaredAggregate

/-!
# Linear chart-Sobolev-zero bound on the raw tensor connection Laplacian

For a closed smooth Riemannian manifold `(M, g)`, ranks `(r, s)`, and a smooth
compactly-supported `(r, s)`-tensor section `T`, this file ships the **linear**
chart-Sobolev-zero bound

```
wtwokTwoNorm g 0 (rawTensorConnLapSmooth g r s T)
    ≤ ENNReal.ofReal C · wtwokTwoNorm g 1 T
```

with a non-negative constant `C` independent of `T`.

The proof composes the previously established squared aggregate bound for the
finset sum of `L²` chart-component norms of the raw tensor connection Laplacian,
collapses the tsum defining `wtwokTwoNorm g 0 (raw T)` to a finset sum over the
canonical chart-atlas partition-of-unity finset (the chart components vanish
identically outside this finset since the partition-of-unity weight does), and
takes a square root step through `ENNReal` `pow_le_pow_left_iff`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open MeasureTheory
open scoped Manifold Topology Bundle ContDiff BigOperators ENNReal NNReal

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The Euclidean ambient space of dimension `Module.finrank ℝ E`. -/
local notation "EuclN" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- For `α` outside the canonical chart-atlas partition-of-unity finset, every
chart component of any smooth compactly-supported `(r, s)`-tensor section
vanishes identically. The partition-of-unity weight is zero everywhere for such
`α`, so the POU-weighted scalar component is the zero function on `M`, whose
chart push-forward is the zero function on the Euclidean ambient space. -/
private lemma tensorChartComp_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s S α Idx Jdx = (fun _ => (0 : ℝ)) := by
  classical
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s S α Idx Jdx hy]
    unfold tensorChartComponentPou
    rw [chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα _]
    ring
  · exact tensorChartComp_apply_of_notMem
      (I := I) (M := M) g r s S α Idx Jdx hy

/-- The chart-aggregating `tsum` defining `wtwokTwoNorm g 0 (rawTensorConnLapSmooth
g r s T)` collapses to a finset sum over `chartAtlasPOU_finset`. The per-`α`
summand vanishes for `α` outside this finset because each chart component is the
zero function there (the partition-of-unity weight vanishes), and the
`wkpNorm 0 2` of the zero function on any open set is zero. -/
private lemma wtwokTwoNorm_zero_rawTensorConnLap_eq_finset_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g 0
        (rawTensorConnLapSmooth (I := I) g r s T) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) 0 2
              (tensorChartComp (I := I) (M := M) g r s
                (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [wtwokTwoNorm_eq_tsum (I := I) (M := M) g 0
    (rawTensorConnLapSmooth (I := I) g r s T)]
  rw [show (2 * 0 : ℕ) = 0 from by norm_num]
  rw [tsum_eq_sum
    (s := chartAtlasPOU_finset (I := I) (M := M))
    (f := fun α : M =>
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) 0 2
            (tensorChartComp (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))]
  intro α hα
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [tensorChartComp_eq_zero_of_notMem_finset
    (I := I) (M := M) g r s (rawTensorConnLapSmooth (I := I) g r s T)
    hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- The order-zero `wkpNorm` over an open set equals the corresponding restricted
`eLpNorm`. A specialisation of `wkpNorm_zero` recorded for direct use below. -/
private lemma wkpNorm_zero_eq_eLpNorm
    (u : EuclN → ℝ) (Ω : Set EuclN) :
    wkpNorm (d := Module.finrank ℝ E) 0 2 u Ω =
      eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) :=
  wkpNorm_zero (d := Module.finrank ℝ E) 2 u Ω

end Connection
end Integral
end DifferentialGeometry

end
