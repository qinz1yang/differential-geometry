import DifferentialGeometry.Geometry.Measure.ChartVolume
import DifferentialGeometry.Geometry.Metric.EuclideanChart
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory Filter DifferentialGeometry
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Metric
open scoped Manifold Topology ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def euclideanChartHaar (g : SmoothRiemannianMetric I M) (p : M) :
    MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  (modelHaar (E := E)).map (metricChartEuclideanEquiv g p)

instance euclideanChartHaar_isAddHaarMeasure (g : SmoothRiemannianMetric I M) (p : M) :
    (euclideanChartHaar g p).IsAddHaarMeasure :=
  (metricChartEuclideanEquiv g p).isAddHaarMeasure_map _

theorem ae_euclideanChart_symm_of_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (p : M)
    {P : M → Prop} (hP : ∀ᵐ x ∂riemannianVolumeMeasure I M g, P x)
    (s : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (hs : ∀ z ∈ s, (metricChartEuclideanEquiv g p).symm z ∈ (extChartAt I p).target) :
    ∀ᵐ z ∂(euclideanChartHaar g p).restrict s,
      P ((extChartAt I p).symm ((metricChartEuclideanEquiv g p).symm z)) := by
  let A := metricChartEuclideanEquiv g p
  have hemb : MeasurableEmbedding A := A.toHomeomorph.measurableEmbedding
  rw [euclideanChartHaar, hemb.restrict_map, hemb.ae_map_iff]
  have hsub : A ⁻¹' s ⊆ (extChartAt I p).target := by
    intro y hy
    simpa only [A, ContinuousLinearEquiv.symm_apply_apply] using hs (A y) hy
  have hraw := ae_restrict_of_ae_restrict_of_subset hsub
    (ae_extChartAt_symm_of_riemannianVolumeMeasure g p hP)
  simpa only [A, ContinuousLinearEquiv.symm_apply_apply] using hraw

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem exists_open_ae_norm_fderiv_euclideanChartExpression_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : Continuous f)
    (hdf : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      MDifferentiableAt I J f x → ∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) ≤
          Real.sqrt (g.inner x v v))
    (p : M) {K : ℝ} (hK : 1 < K) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))), MeasurableSet s →
        (∀ z ∈ s, (metricChartEuclideanEquiv g p).symm z ∈ (extChartAt I p).target ∧
          (extChartAt I p).symm ((metricChartEuclideanEquiv g p).symm z) ∈ U) →
        ∀ᵐ z ∂(euclideanChartHaar g p).restrict s,
          ‖fderiv ℝ (euclideanChartExpression g h f p (f p)) z‖ ≤ K ^ 2 := by
  have hdf' : ∀ᵐ x ∂riemannianVolumeMeasure I M g,
      ∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) ≤
          Real.sqrt (g.inner x v v) := by
    filter_upwards [hdf] with x hx
    by_cases hd : MDifferentiableAt I J f x
    · exact hx hd
    · intro v
      rw [mfderiv_zero_of_not_mdifferentiableAt hd]
      simpa only [_root_.zero_apply, map_zero, Real.sqrt_zero] using
        Real.sqrt_nonneg (g.inner x v v)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (eventually_norm_fderiv_euclideanChartExpression_le g h f hf p hK)
  refine ⟨U, hUopen, hpU, fun s hsm hs => ?_⟩
  have hpull := ae_euclideanChart_symm_of_riemannianVolumeMeasure g p hdf' s
    (fun z hz => (hs z hz).1)
  filter_upwards [hpull, ae_restrict_mem hsm] with z hz hzs
  have hx := hUsub (hs z hzs).2
  have hbound := hx.2.2 hz
  simpa only [(extChartAt I p).right_inv (hs z hzs).1,
    ContinuousLinearEquiv.apply_symm_apply] using hbound

end DifferentialGeometry.Geometry.Measure
