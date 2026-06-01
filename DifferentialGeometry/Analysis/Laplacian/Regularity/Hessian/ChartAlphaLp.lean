import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.ChartAlphaFrobenius

/-!
# Lp-class assembly via chart-α tensor pairing

This module begins the Lp-class assembly of the smooth-case Hessian bridge.
Using the unconditional chart-α Frobenius invariance (from
`HessianChartAlphaFrobenius`), we package per-chart pointwise identification
of the **chart-α tensor pairing** with the chart-invariant Hess pairing.

The remaining gap to the full Lp-class equality
`hessPairingLpOnLapDom g φ ⟨smoothToH1Compl v, _⟩ = hessPairingSmoothLp g φ v`
is the partition-of-unity (POU) cancellation of the Christoffel-correction
difference between the LapDom-side chart-pushed Euclidean Hessian and the
chart-α tensor Hessian.

## Main results

* `smoothTensorPairing_eq_hessPairingChart_on_chartSource` — pointwise
  identification on the chart-α source: for `x ∈ (chartAt H α).source`,
  the chart-α tensor pairing evaluated at `toEuclidean (extChartAt α x)`
  equals the chart-invariant Hess pairing at `x`.

* `pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise` — for any
  `x ∈ M`, the POU-weighted sum of chart-α tensor pairings (over the POU
  finset) equals the chart-invariant Hess pairing at `x`. The sum is
  understood with the tensor pairing taking its junk value off the chart
  source, but the POU weights are zero there.

## Gap to full Lp-class equality

The Lp-class equality requires also showing that the LapDom-side pairing
(using `chartPushedEuclidHessian`) and the chart-α tensor pairing (using
`chartHessianVOnEuclid`) agree after POU summation. The difference, encoded
in `smoothPairingChristoffelDiff`, captures:
- Christoffel correction (built into chart-α tensor Hess, missing from
  chart-pushed Euclidean Hess).
- POU Leibniz cross-terms (chart-pushed function is `POU·v_chart_α`, whose
  second partial involves partials of POU).

The POU-weighted sum of these Christoffel diffs should vanish a.e. (via
`∑ POU = 1`, `∑ ∂_i POU = 0`, `∑ ∂_i ∂_j POU = 0`), but the proof requires
careful POU calculus tracking chart-α coordinate derivatives. This is
reserved for follow-up work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaFrobenius
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Pointwise identification on the chart-α source.** For smooth `φ : C^∞⟮I, M; ℝ⟯`,
smooth scalar `v : SmoothScalar g`, chart base point `α : M`, and manifold point
`x ∈ (chartAt H α).source`, the chart-α tensor pairing evaluated at
`toEuclidean (extChartAt α x)` equals the chart-invariant Hess pairing
`hessPairingChart g φ v_bundle x`. -/
theorem smoothTensorPairing_eq_hessPairingChart_on_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) {x : M} (hx : x ∈ (chartAt H α).source) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  have hx_src_ext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hx_tgt_ext : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hx_src_ext
  have h_toE_mem : (toEuclidean (E := E)) (extChartAt I α x) ∈
      chartTargetEuclid (I := I) (M := M) α := by
    unfold chartTargetEuclid
    simp only [Set.mem_image]
    exact ⟨extChartAt I α x, hx_tgt_ext, rfl⟩
  have h_bridge := smoothTensorPairingChart_eq_hessPairingChart_pullback
    (I := I) (M := M) g α φ v h_toE_mem
  rw [h_bridge]
  have h_toE_inv : (toEuclidean (E := E)).symm
      ((toEuclidean (E := E)) (extChartAt I α x)) = extChartAt I α x :=
    (toEuclidean (E := E)).symm_apply_apply _
  rw [h_toE_inv]
  rw [(extChartAt I α).left_inv hx_src_ext]

/-- **POU-weighted pointwise identification.** For smooth `φ` and `v`,
the POU-weighted sum (over the chart atlas POU finset) of the chart-α tensor
pairings evaluated at the chart-α image of `x` equals the chart-invariant
Hess pairing at `x`. The sum is finite (POU finset) and each non-zero term
satisfies `x ∈ (chartAt H α).source` (since POU(α) is supported in chart α
source). -/
theorem pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothTensorPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  have h_per_term : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
        smoothTensorPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
    intro α hα
    by_cases h_pou : (chartAtlasPOU I M α : M → ℝ) x = 0
    · rw [h_pou, zero_mul, zero_mul]
    · have h_x_supp : x ∈ tsupport ((chartAtlasPOU I M α : M → ℝ)) := by
        apply subset_tsupport _
        simp only [Function.mem_support, ne_eq]
        exact h_pou
      have h_tsupport_subset :
          tsupport ((chartAtlasPOU I M α : M → ℝ)) ⊆ (chartAt H α).source :=
        chartAtlasPOU_isSubordinate I M α
      have h_x_chart : x ∈ (chartAt H α).source := h_tsupport_subset h_x_supp
      congr 1
      exact smoothTensorPairing_eq_hessPairingChart_on_chartSource
        (I := I) (M := M) g α φ v h_x_chart
  rw [Finset.sum_congr rfl h_per_term]
  rw [← Finset.sum_mul]
  rw [chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x]
  rw [one_mul]

end HessianChartAlphaLp
end Laplacian
end Analysis
end DifferentialGeometry

end
