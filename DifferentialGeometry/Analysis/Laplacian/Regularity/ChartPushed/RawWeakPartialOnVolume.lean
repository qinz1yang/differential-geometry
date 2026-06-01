import DifferentialGeometry.Analysis.Laplacian.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLMChartFormula
import DifferentialGeometry.Analysis.Laplacian.Regularity.LaplacianDomain.ChartData
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Chart-pushed raw weak partial: `Lp` class on the chart target

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and a
coordinate direction `j : Fin (Module.finrank ℝ E)`, this file packages the
chart-pushed *raw* weak partial of an element `u_h : H1Compl g`. The
construction parallels `chartPushedWeakPartialLp` (POU-weighted version) but
uses `chartPushedRaw α u_h.coeFn` (without the partition-of-unity multiplier)
as the function being differentiated.

## Construction overview

For a smooth scalar `v : SmoothScalar g`, the chart-pushed raw partial at a
point `y ∈ chartTargetEuclid α` is

```
chartPushedRawPartial g α j v y
  := fderiv ℝ (chartPushedRaw α v.toFun) y (EuclideanSpace.single j 1)
```

where `chartPushedRaw α v.toFun = v.toFun ∘ symm ∘ toE.symm` on the chart
target and `0` off it. On the chart target this equals the j-th chart-α
basis-direction directional derivative of `v.toFun` at the corresponding
manifold point.

To define the chart-pushed raw weak partial as a continuous linear map
`H1Compl g →L[ℝ] Lp ℝ 2 (chart-pulled-weighted-restrict chartTarget)`, the
construction needs a Lipschitz bound on the linear map on smooth scalars in
the H¹ pre-norm. We package this bound as a `ChartPushedRawPartialLipschitz`
structure, parallel to `ChartPushedPartialLipschitz`. Concrete instances of
the structure can be supplied by downstream files that have additional
structural control on the chart-α basis g-norm (e.g., a uniform bound on the
support of relevant functions).

## Main results

* `chartPushedRawPartial`: the pointwise chart-pushed raw partial of a smooth
  scalar, as a function `EuclN → ℝ`.

* `ChartPushedRawPartialLipschitz`: the Lipschitz-witness structure encoding
  the H¹-pre-norm continuity of the chart-pushed raw partial linear map.

* `chartPushedRawPartialLpLin_of_lipschitz`: given the Lipschitz witness, the
  chart-pushed raw partial map as a linear map `SmoothScalar g →ₗ[ℝ] Lp ℝ 2 (...)`.

* `chartPushedRawPartialCLM`: given the Lipschitz witness, the chart-pushed
  raw partial as a continuous linear map `SmoothScalar g →L[ℝ] Lp ℝ 2 (...)`.

* `chartPushedRawWeakPartialLp`: the chart-pushed raw weak partial extended
  to `H1Compl g`, given a Lipschitz witness.

* `chartPushedRawWeakPartialLp_smoothToH1Compl`: the smooth-case identity.

* `chartPushedRawWeakPartialLp_continuous`: continuity of the resulting map.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedRawWeakPartialOnVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- The chart-pushed raw partial of a smooth scalar `v` at a point `y : EuclN`
in the `j`-th coordinate direction. Defined as the fderiv of the raw
chart-pull `chartPushedRaw α v.toFun` at `y`, evaluated on
`EuclideanSpace.single j 1`. -/
noncomputable def chartPushedRawPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) : EuclN → ℝ :=
  fun y =>
    (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v.toFun) y)
      (EuclideanSpace.single j 1)

@[simp] lemma chartPushedRawPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) (y : EuclN) :
    chartPushedRawPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v.toFun) y)
        (EuclideanSpace.single j 1) := rfl

structure ChartPushedRawPartialLipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) where
  /-- The Lipschitz constant. -/
  C : ℝ
  /-- Non-negativity of the constant. -/
  C_nonneg : 0 ≤ C
  /-- The chart-pushed raw partial is in `MemLp 2` for every smooth scalar. -/
  memLp : ∀ v : SmoothScalar g,
    MemLp (chartPushedRawPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))
  /-- The H¹-Lipschitz bound. -/
  bound : ∀ v : SmoothScalar g,
    eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal C * (‖v‖₊ : ℝ≥0∞)
  /-- The chart-pushed raw partial is additive in `v`. -/
  add : ∀ v w : SmoothScalar g,
    chartPushedRawPartial (I := I) (M := M) g α j (v + w) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => chartPushedRawPartial (I := I) (M := M) g α j v y +
        chartPushedRawPartial (I := I) (M := M) g α j w y
  /-- The chart-pushed raw partial is `ℝ`-linear in `v`. -/
  smul : ∀ (c : ℝ) (v : SmoothScalar g),
    chartPushedRawPartial (I := I) (M := M) g α j (c • v) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => c * chartPushedRawPartial (I := I) (M := M) g α j v y

/-- The chart-pushed raw partial of a smooth scalar `v`, as an `Lp ℝ 2`
element on the chart-pulled weighted measure restricted to the chart target,
given a Lipschitz witness. -/
noncomputable def chartPushedRawPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (hLip.memLp v).toLp _

@[simp] lemma chartPushedRawPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ((chartPushedRawPartialLp (I := I) (M := M) g α j hLip v :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRawPartial (I := I) (M := M) g α j v := by
  unfold chartPushedRawPartialLp
  exact MeasureTheory.MemLp.coeFn_toLp _

lemma norm_chartPushedRawPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ‖chartPushedRawPartialLp (I := I) (M := M) g α j hLip v‖ =
      ENNReal.toReal (eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) := by
  unfold chartPushedRawPartialLp
  exact MeasureTheory.Lp.norm_toLp _ _

/-- The chart-pushed raw partial as a linear map on smooth scalars. -/
noncomputable def chartPushedRawPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) where
  toFun v := chartPushedRawPartialLp (I := I) (M := M) g α j hLip v
  map_add' v w := by
    classical
    apply MeasureTheory.Lp.ext
    have h_lhs_coe := chartPushedRawPartialLp_coeFn
      (I := I) (M := M) g α j hLip (v + w)
    have h_v_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v
    have h_w_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip w
    have h_add_aeEq := hLip.add v w
    have h_sum_coe := MeasureTheory.Lp.coeFn_add
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip w)
    refine h_lhs_coe.trans (h_add_aeEq.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_sum_coe, h_v_coe, h_w_coe] with y hy_sum hy_v hy_w
    rw [hy_sum, Pi.add_apply, hy_v, hy_w]
  map_smul' c v := by
    classical
    apply MeasureTheory.Lp.ext
    have h_lhs_coe := chartPushedRawPartialLp_coeFn
      (I := I) (M := M) g α j hLip (c • v)
    have h_v_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v
    have h_smul_aeEq := hLip.smul c v
    have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)
    refine h_lhs_coe.trans (h_smul_aeEq.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_smul_coe, h_v_coe] with y hy_smul hy_v
    change ((c • (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)) :
        Lp ℝ 2 _) y = c * chartPushedRawPartial (I := I) (M := M) g α j v y
    rw [hy_smul, Pi.smul_apply, hy_v, smul_eq_mul]

lemma chartPushedRawPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := rfl

/-- The norm of `chartPushedRawPartialLpLin v` equals (the toReal of) the
chart-pulled-weighted eLpNorm of `chartPushedRawPartial g α j v`. -/
lemma norm_chartPushedRawPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ‖chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v‖ =
      ENNReal.toReal (eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) := by
  rw [chartPushedRawPartialLpLin_apply]
  exact norm_chartPushedRawPartialLp (I := I) (M := M) g α j hLip v

/-- The chart-pushed raw partial promoted to a continuous linear map via the
Lipschitz hypothesis. -/
noncomputable def chartPushedRawPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip).mkContinuous hLip.C
    (by
      intro v
      rw [norm_chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v]
      have h_bd := hLip.bound v
      have h_nn := hLip.C_nonneg
      have h_norm_nn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
      have h_lhs_finite : eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
        (hLip.memLp v).2.ne
      have h_rhs_eq : ENNReal.ofReal hLip.C * (‖v‖₊ : ℝ≥0∞) =
          ENNReal.ofReal (hLip.C * ‖v‖) := by
        rw [show ((‖v‖₊ : ℝ≥0∞) : ℝ≥0∞) = ENNReal.ofReal ‖v‖ from by
          rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h_norm_nn]
          rfl]
        rw [← ENNReal.ofReal_mul h_nn]
      rw [h_rhs_eq] at h_bd
      have h_toReal := (ENNReal.toReal_le_toReal h_lhs_finite ENNReal.ofReal_ne_top).mpr h_bd
      rwa [ENNReal.toReal_ofReal (mul_nonneg h_nn h_norm_nn)] at h_toReal)

@[simp] lemma chartPushedRawPartialCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawPartialCLM (I := I) (M := M) g α j hLip v =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := rfl

/-- `smoothToH1Compl` has dense range. -/
private lemma denseRange_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

/-- `smoothToH1Compl` is uniform-inducing. -/
private lemma isUniformInducing_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

/-- The chart-pushed raw partial CLM, extended along the dense
uniform-inducing embedding `smoothToH1Compl`. -/
noncomputable def H1ComplRawPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    H1Compl g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  ContinuousLinearMap.extend
    (chartPushedRawPartialCLM (I := I) (M := M) g α j hLip)
    (smoothToH1Compl (I := I) (M := M) g)

@[simp] lemma H1ComplRawPartialCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    H1ComplRawPartialCLM (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedRawPartialCLM (I := I) (M := M) g α j hLip v := by
  unfold H1ComplRawPartialCLM
  exact ContinuousLinearMap.extend_eq
    (chartPushedRawPartialCLM (I := I) (M := M) g α j hLip)
    (e := smoothToH1Compl (I := I) (M := M) g)
    (denseRange_smoothToH1Compl_local (I := I) (M := M) g)
    (isUniformInducing_smoothToH1Compl_local (I := I) (M := M) g) v

/-- For `u_h : H1Compl g` and chart point `α`, the chart-pushed raw weak
partial is the L²-limit of the chart-pushed raw classical partials of any
smooth approximating sequence. The construction requires a Lipschitz witness
`hLip : ChartPushedRawPartialLipschitz g α j`. -/
noncomputable def chartPushedRawWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (u_h : H1Compl g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  H1ComplRawPartialCLM (I := I) (M := M) g α j hLip u_h

/-- The chart-pushed raw weak partial agrees with the chart-pushed raw
classical partial on smooth scalars. -/
@[simp] theorem chartPushedRawWeakPartialLp_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := by
  unfold chartPushedRawWeakPartialLp
  rw [H1ComplRawPartialCLM_smoothToH1Compl]
  rfl

/-- The chart-pushed raw weak partial is a continuous function of `u_h`. -/
theorem chartPushedRawWeakPartialLp_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    Continuous (chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip) := by
  unfold chartPushedRawWeakPartialLp
  exact (H1ComplRawPartialCLM (I := I) (M := M) g α j hLip).continuous

/-- The chart-pushed raw weak partial coincides (a.e. on the chart-pulled
weighted measure restricted to the chart target) with the pointwise
chart-pushed raw partial for smooth scalars. -/
theorem chartPushedRawWeakPartialLp_smoothToH1Compl_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ((chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRawPartial (I := I) (M := M) g α j v := by
  rw [chartPushedRawWeakPartialLp_smoothToH1Compl]
  exact chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v

end ChartPushedRawWeakPartialOnVolume
end Laplacian
end Analysis
end DifferentialGeometry

end
