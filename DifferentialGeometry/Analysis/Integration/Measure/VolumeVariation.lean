import DifferentialGeometry.Analysis.Integration.Measure.RealizedMetricForMeasure
import DifferentialGeometry.Analysis.Integration.Measure.FamilyDefs
import DifferentialGeometry.Analysis.Integration.Measure.Family
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.Integral.Measure

noncomputable section

open MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩


abbrev metricFamilyForMeasure
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t


abbrev metricFamilyForMeasureOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → SmoothRiemannianMetric I M :=
  fun t => G.metric t


abbrev volumeMeasureFamily [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasure (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamily_eq [T2Space M] [SigmaCompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real)
      (t : Real) :
    volumeMeasureFamily (I := I) (M := M) G t =
      Measure.volumeMeasureAt (I := I) (M := M) G t := rfl


abbrev volumeMeasureFamilyOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D) :
    Real → MeasureTheory.Measure M :=
  riemannianMeasureFamily (I := I) (M := M) (metricFamilyForMeasureOn (I := I) (M := M) G)

@[simp]
theorem volumeMeasureFamilyOn_eq [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D)
      (t : Real) :
    volumeMeasureFamilyOn (I := I) (M := M) G t =
      riemannianVolumeMeasure (I := I) (M := M)
        (G.metric t) := rfl

@[simp]
theorem volumeMeasureFamilyOn_eq_volumeMeasureOn [T2Space M] [SigmaCompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D) :
    volumeMeasureFamilyOn (I := I) (M := M) G (t : Real) =
      Measure.volumeMeasureOn (I := I) (M := M) G t := rfl


abbrev traceTimeDerivMetricAt
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real)
      (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricAt_eq
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real)
      (t : Real) (x : M) :
    traceTimeDerivMetricAt (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t x := rfl


abbrev traceTimeDerivMetricOn
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D)
      (t : Real) (x : M) :
    Real :=
  traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x

@[simp]
theorem traceTimeDerivMetricOn_eq
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D)
      (t : Real) (x : M) :
    traceTimeDerivMetricOn (I := I) G t x =
      traceTimeDerivMetric (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t x := rfl

theorem volume_variation_formula_clean
    [T2Space M] [CompactSpace M]
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    {f : ℝ → M → ℝ} {t₀ : ℝ}
    (hg : MetricFamilyRegularAt (I := I) g_fam t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : ℝ => ∫ x, f s x ∂(riemannianMeasureFamily (I := I) (M := M) g_fam s))
      (∫ x, (deriv (fun s : ℝ => f s x) t₀
              + (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x)
          ∂(riemannianMeasureFamily (I := I) (M := M) g_fam t₀))
      t₀ := by
  have hf_cont_joint : Continuous (fun p : ℝ × M => f p.1 p.2) := hf.continuous_joint
  have hf_cont : ∀ᶠ s in 𝓝 t₀, Continuous (f s) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (s, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have hft₀_cont : Continuous (f t₀) := by
    have : Continuous ((fun p : ℝ × M => f p.1 p.2) ∘ (fun x : M => (t₀, x))) := by
      refine hf_cont_joint.comp ?_
      exact continuous_const.prodMk continuous_id
    exact this
  have h_deriv_cont : Continuous (fun x : M => deriv (fun s : ℝ => f s x) t₀) := by
    have : Continuous ((fun p : ℝ × M => deriv (fun s : ℝ => f s p.2) p.1)
        ∘ (fun x : M => (t₀, x))) :=
      hf.continuous_deriv_joint.comp (continuous_const.prodMk continuous_id)
    exact this
  have hh_cont : Continuous (fun x : M =>
      deriv (fun s : ℝ => f s x) t₀ +
      (1/2) * traceTimeDerivMetric (I := I) g_fam t₀ x * f t₀ x) := by
    refine Continuous.add h_deriv_cont ?_
    refine Continuous.mul ?_ hft₀_cont
    refine Continuous.mul continuous_const ?_
    exact traceTimeDerivMetric_continuous (I := I) (M := M) hg
  refine volume_variation_formula_clean_of_chart_derivs
    (I := I) (M := M) g_fam f t₀ hf_cont hh_cont ?_
  intro α hα
  exact per_chart_hasDerivAt (I := I) (M := M) hg hf α hα


theorem volume_variation_formula_clean_at
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamily (I := I) (M := M) Real)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasure (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricAt (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamily (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamily, traceTimeDerivMetricAt] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasure (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

theorem volume_variation_formula_clean_on
    [T2Space M] [CompactSpace M]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (G : DifferentialGeometry.Geometry.Curvature.RealizedMetricFamilyOn (I := I) (M := M) D)
    {f : Real → M → Real} {t₀ : Real}
    (hg : MetricFamilyRegularAt (I := I) (metricFamilyForMeasureOn (I := I) (M := M) G) t₀)
    (hf : FunctionRegularAt f t₀) :
    HasDerivAt
      (fun s : Real => ∫ x, f s x ∂(volumeMeasureFamilyOn (I := I) (M := M) G s))
      (∫ x, (deriv (fun s : Real => f s x) t₀
            + (1 / 2 : Real) * traceTimeDerivMetricOn (I := I) G t₀ x * f t₀ x)
          ∂(volumeMeasureFamilyOn (I := I) (M := M) G t₀))
      t₀ := by
  simpa [volumeMeasureFamilyOn, traceTimeDerivMetricOn] using
    (volume_variation_formula_clean (I := I) (M := M)
      (g_fam := metricFamilyForMeasureOn (I := I) (M := M) G)
      (f := f) (t₀ := t₀) hg hf)

end


end DifferentialGeometry.Integral.Measure
