import DifferentialGeometry.Analysis.Laplacian.Regularity.DiffChart.BilinearH1ComplResidual
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.CLMLeibniz

/-!
# A.e. linearity of `smoothFChartResidual` in the smooth scalar argument

For a closed Riemannian manifold `(M, g)`, a chart point `α : M`, and three
smooth scalars `v₁ v₂ v_diff : SmoothScalar g` with
`v_diff.toFun = v₁.toFun - v₂.toFun`, the chart-pulled smooth Leibniz
residual `smoothFChartResidual g α v` is a.e.-additive under the smooth
subtraction in the third argument:

```
smoothFChartResidual g α v_diff
  =ᵐ[volume.restrict (chartTargetEuclid α)]
fun y => smoothFChartResidual g α v₁ y - smoothFChartResidual g α v₂ y.
```

## Strategy

By definition,
`smoothFChartResidual g α v = fChartResidual g α (smoothToH1Compl g v)`,
and
`fChartResidual g α u_h
  = (chartPushedRawLpFromLp g α (fHLeibnizResidualLp g α u_h)).coeFn`.
The Lp class `fHLeibnizResidualLp g α u_h` is built as
`-(2 • gradInnerCLM g ρα u_h) - smoothMulLp g Δρα (H1ComplToLp g u_h)`,
which is linear in `u_h` since each of `gradInnerCLM g ρα`,
`smoothMulLp g Δρα`, and `H1ComplToLp g` is a continuous linear map.
`smoothToH1Compl g` is itself a continuous linear map, so
`smoothToH1Compl g v_diff = smoothToH1Compl g v₁ - smoothToH1Compl g v₂`
as soon as `v_diff = v₁ - v₂` (which follows from the structure-extensional
equality of `SmoothScalar g` under the `Sub` instance built on `toFun`).

Combining these:
* `fHLeibnizResidualLp g α (smoothToH1Compl v_diff)
    = fHLeibnizResidualLp g α (smoothToH1Compl v₁)
      - fHLeibnizResidualLp g α (smoothToH1Compl v₂)`
  as `Lp ℝ 2`-classes.
* By `chartPushedRawLpFromLp_coeFn_sub`, the chart-pull of an Lp-class
  subtraction is the pointwise subtraction (a.e. on the chart-pulled
  weighted measure restricted to the chart target).
* The plain volume measure is absolutely continuous w.r.t. the chart-pulled
  weighted measure on `chartTargetEuclid α` (the density is strictly
  positive there), so the a.e. equality transfers to the plain volume
  measure.

## Main result

* `smoothFChartResidual_ae_sub` — the headline a.e. linearity lemma.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualLinearity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- For `v_diff v₁ v₂ : SmoothScalar g` with `v_diff.toFun = v₁.toFun -
v₂.toFun`, we have `v_diff = v₁ - v₂` in `SmoothScalar g`. -/
private lemma smoothScalar_eq_sub_of_toFun_eq
    {g : SmoothRiemannianMetric I M}
    (v₁ v₂ v_diff : SmoothScalar g)
    (h_diff : v_diff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    v_diff = v₁ - v₂ := by
  apply SmoothScalar.ext
  rw [h_diff]
  rfl

/-- For `v_diff v₁ v₂ : SmoothScalar g` with `v_diff.toFun = v₁.toFun -
v₂.toFun`, the `H1Compl` embeddings satisfy
`smoothToH1Compl g v_diff = smoothToH1Compl g v₁ - smoothToH1Compl g v₂`. -/
private lemma smoothToH1Compl_eq_sub
    (g : SmoothRiemannianMetric I M)
    (v₁ v₂ v_diff : SmoothScalar g)
    (h_diff : v_diff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    smoothToH1Compl (I := I) (M := M) g v_diff =
      smoothToH1Compl (I := I) (M := M) g v₁ -
        smoothToH1Compl (I := I) (M := M) g v₂ := by
  rw [smoothScalar_eq_sub_of_toFun_eq v₁ v₂ v_diff h_diff]
  exact map_sub (smoothToH1Compl (I := I) (M := M) g) v₁ v₂

/-- `fHLeibnizResidualLp g α` is additive under `H1Compl` subtraction. -/
private lemma fHLeibnizResidualLp_sub
    (g : SmoothRiemannianMetric I M) (α : M)
    (u₁ u₂ : H1Compl (I := I) (M := M) g) :
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (u₁ - u₂) =
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u₁ -
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u₂ := by
  classical
  unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  set Δρα : C^∞⟮I, M; ℝ⟯ :=
    laplacianOfChartPOU (I := I) (M := M) g α with hΔρα_def
  have h_grad_sub :
      gradInnerCLM (I := I) (M := M) g ρα (u₁ - u₂) =
        gradInnerCLM (I := I) (M := M) g ρα u₁ -
          gradInnerCLM (I := I) (M := M) g ρα u₂ :=
    map_sub (gradInnerCLM (I := I) (M := M) g ρα) u₁ u₂
  have h_H1Compl_sub :
      H1ComplToLp (I := I) (M := M) g (u₁ - u₂) =
        H1ComplToLp (I := I) (M := M) g u₁ -
          H1ComplToLp (I := I) (M := M) g u₂ :=
    map_sub (H1ComplToLp (I := I) (M := M) g) u₁ u₂
  have h_lap_sub :
      smoothMulLp (I := I) (M := M) g Δρα
          (H1ComplToLp (I := I) (M := M) g (u₁ - u₂)) =
        smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g u₁) -
          smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g u₂) := by
    rw [h_H1Compl_sub]
    exact map_sub (smoothMulLp (I := I) (M := M) g Δρα) _ _
  rw [h_grad_sub, h_lap_sub]
  rw [smul_sub, neg_sub]
  abel

private lemma volume_restrict_absolutelyContinuous_chartPulledWeighted_restrict
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  intro A hA
  have h_chartTarget_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
      ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
    at hA
  rw [Measure.restrict_apply' h_chartTarget_meas]
  rw [Measure.restrict_apply' h_chartTarget_meas] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_chart⟩
  refine ⟨⟨?_, hy_A⟩, hy_chart⟩
  have h_pos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_chart
  exact (ENNReal.ofReal_pos.mpr h_pos).ne'

/-- **A.e. linearity of `smoothFChartResidual`**: for smooth scalars
`v₁ v₂ v_diff : SmoothScalar g` with
`v_diff.toFun = v₁.toFun - v₂.toFun`, the chart-pulled smooth Leibniz
residuals satisfy
```
smoothFChartResidual g α v_diff
  =ᵐ[volume.restrict (chartTargetEuclid α)]
fun y => smoothFChartResidual g α v₁ y - smoothFChartResidual g α v₂ y.
``` -/
theorem smoothFChartResidual_ae_sub
    (g : SmoothRiemannianMetric I M) (α : M)
    (v₁ v₂ v_diff : SmoothScalar g)
    (h_diff : v_diff.toFun = fun x => v₁.toFun x - v₂.toFun x) :
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α v_diff
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
    fun y =>
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α v₁ y -
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α v₂ y := by
  classical
  have h_smoothToH1Compl_sub :=
    smoothToH1Compl_eq_sub (I := I) (M := M) g v₁ v₂ v_diff h_diff
  have h_residual_sub_at :
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α
          (smoothToH1Compl (I := I) (M := M) g v_diff) =
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g v₁) -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g v₂) := by
    rw [h_smoothToH1Compl_sub]
    exact fHLeibnizResidualLp_sub (I := I) (M := M) g α _ _
  have h_chartPushed_eq :
      chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g v_diff)) =
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α
              (smoothToH1Compl (I := I) (M := M) g v₁) -
            DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α
              (smoothToH1Compl (I := I) (M := M) g v₂)) := by
    rw [h_residual_sub_at]
  have h_coeFn_sub :=
    chartPushedRawLpFromLp_coeFn_sub (I := I) (M := M) g α
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v₁))
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v₂))
  have h_residual_ae_weighted :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α
            (smoothToH1Compl (I := I) (M := M) g v_diff)) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α
              (smoothToH1Compl (I := I) (M := M) g v₁)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
        ((chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α
              (smoothToH1Compl (I := I) (M := M) g v₂)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    rw [h_chartPushed_eq]
    exact h_coeFn_sub
  have h_vol_abs :=
    volume_restrict_absolutelyContinuous_chartPulledWeighted_restrict
      (I := I) (M := M) g α
  unfold
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
  exact h_vol_abs.ae_le h_residual_ae_weighted

end SmoothFChartResidualLinearity
end Laplacian
end Analysis
end DifferentialGeometry

end
