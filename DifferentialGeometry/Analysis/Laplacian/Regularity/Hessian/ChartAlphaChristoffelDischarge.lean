import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.ChartAlphaLp

/-!
# POU Christoffel discharge for the smooth-case Hess bridge

This module packages the **partition-of-unity (POU) Christoffel discharge**
that closes the smooth-case Hessian bridge between

* the LapDom chart-α Euclidean Hessian pairing
  `smoothEuclidHessianPairingChart g α φ v` (a.k.a. `chartPushedEuclidHessian`
  paired with `chartHessianPhiOnEuclid` via the chart-α inverse Gram), and
* the chart-α tensor Hessian pairing
  `smoothTensorPairingChart g α φ v` (Christoffel-corrected).

Their pointwise difference per chart is captured by `smoothPairingChristoffelDiff`
(see `HessianTensorChartSmooth`). The POU-weighted sum of these differences
over the chart atlas POU finset is the **Christoffel discharge residual**.

When the residual vanishes (an explicit pointwise hypothesis at each `x : M`),
the chart-α tensor invariance result
`pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise` lifts to:

```
∑_α POU(α)(x) · smoothEuclidHessianPairingChart α φ v (toE(extChartAt α x))
  = hessPairingChart g φ v x.
```

This pointwise identity is the **global manifold-side bridge** between the
LapDom-side Euclidean pairing and the chart-invariant smooth pairing
(modulo manifold-side ae-transfer from the chart-target ae-equality).

## Christoffel discharge hypothesis

The hypothesis is packaged at the global manifold level as

```
ChristoffelDischargeSmoothCase g φ v : ∀ x : M,
  ∑ α ∈ chartAtlasPOU_finset, POU(α)(x) ·
    smoothPairingChristoffelDiff g α φ v (toE(extChartAt α x)) = 0.
```

Mathematically, this follows from `∑_α POU(α) = 1`, hence `∑_α ∂POU(α) = 0`
and `∑_α ∂²POU(α) = 0`, combined with chart-α Leibniz expansion of the second
weak partial of `chartPushed POU·v.toFun` and the chart-α Christoffel
correction structure. The proof requires careful chart-α calculus tracking
POU derivatives, and is reserved for follow-up work.

## Main results

* `christoffelDischargeSmoothCase` — the discharge hypothesis predicate
  (a pointwise condition at every `x : M`).

* `pou_weighted_euclid_pairing_decompose` — the unconditional algebraic
  decomposition of the POU-weighted Euclidean pairing as the chart-invariant
  pairing plus the Christoffel residual.

* `pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge`
  — given the discharge hypothesis, the POU-weighted sum of the LapDom-side
  Euclidean pairings equals the chart-invariant smooth pairing pointwise.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaChristoffelDischarge

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
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Christoffel discharge hypothesis.** For smooth `φ` and `v`, the
POU-weighted sum of `smoothPairingChristoffelDiff` over the chart atlas POU
finset vanishes pointwise at every `x : M`. -/
def christoffelDischargeSmoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  ∀ x : M,
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) = 0

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma christoffelDischargeSmoothCase_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    christoffelDischargeSmoothCase (I := I) (M := M) g φ v ↔
      ∀ x : M,
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
            (chartAtlasPOU I M α : M → ℝ) x *
              smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
                ((toEuclidean (E := E)) (extChartAt I α x)) = 0 := Iff.rfl

/-- **Per-chart algebraic decomposition, lifted.** For smooth `φ` and `v`,
chart base point `α : M`, and `x : M`, the per-chart Euclidean pairing at
`toE(extChartAt α x)` equals the chart-α tensor pairing plus the Christoffel
diff at the same point. -/
theorem smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
        ((toEuclidean (E := E)) (extChartAt I α x)) =
      smoothTensorPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) +
        smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)) :=
  smoothEuclidHessianPairingChart_eq_tensor_plus_diff
    (I := I) (M := M) g α φ v ((toEuclidean (E := E)) (extChartAt I α x))

/-- **POU-weighted decomposition.** For smooth `φ` and `v`, the POU-weighted sum
of `smoothEuclidHessianPairingChart` over the chart atlas POU finset decomposes
as the chart-invariant smooth pairing plus the POU-weighted Christoffel diff
residual. This is an **unconditional** identity (no Christoffel discharge
hypothesis required). -/
theorem pou_weighted_euclid_pairing_decompose
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x +
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
  classical
  have h_per_term : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothTensorPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) +
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothPairingChristoffelDiff (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) := by
    intro α _
    rw [smoothEuclidHessianPairingChart_at_chartAt_eq_tensor_plus_diff
      (I := I) (M := M) g φ v α x]
    ring
  rw [Finset.sum_congr rfl h_per_term]
  rw [Finset.sum_add_distrib]
  rw [pou_weighted_tensor_pairing_eq_hessPairingChart_pointwise
    (I := I) (M := M) g φ v x]

/-- **Pointwise bridge under the discharge hypothesis.** For smooth `φ` and `v`,
given the Christoffel discharge hypothesis, the POU-weighted sum of
`smoothEuclidHessianPairingChart` over the chart atlas POU finset equals the
chart-invariant smooth pairing at every `x : M`. -/
theorem pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v)
    (x : M) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x)) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x := by
  classical
  rw [pou_weighted_euclid_pairing_decompose (I := I) (M := M) g φ v x]
  rw [h_discharge x]
  rw [add_zero]

omit [NeZero (Module.finrank ℝ E)] in
/-- **LapDom-side chart contribution, definitional form.** The LapDom-side
chart contribution at `x` equals `POU(α)(x) · hessPairingChartLocal`. -/
theorem hessPairingMChartContribution_smoothCase_eq_weighted_chartLocal
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (v : SmoothScalar g) (α : M) (x : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
      (chartAtlasPOU I M α : M → ℝ) x *
        hessPairingChartLocal (I := I) (M := M) g α φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

end HessianChartAlphaChristoffelDischarge
end Laplacian
end Analysis
end DifferentialGeometry

end
