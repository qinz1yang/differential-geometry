import DifferentialGeometry.Geometry.Metric.FamilySourceDerivative
import DifferentialGeometry.Geometry.Connection.SourceCovariantPartial
import DifferentialGeometry.Geometry.Connection.SourceSectionRestriction



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem hasDerivAt_parameterMetricPartial
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {F : ℝ × A → M} {s : Set (ℝ × A)} (hs : IsOpen s)
    (hF : ContMDiffOn 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) ∞ F s)
    {z : A} (hz : (t, z) ∈ s) (v : A) :
    let V := fun p => mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F p (0, v)
    let W := fun q => mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, q) (1, 0)
    HasDerivAt (fun r => (G r).inner (F (r, z)) (V (r, z)) (V (r, z)))
      (deriv (fun r => (G r).inner (F (t, z)) (V (t, z)) (V (t, z))) t +
        2 * (G t).inner (F (t, z))
          (sourceSectionCovariantDerivative (G t) (fun q => F (t, q)) W z v) (V (t, z))) t := by
  dsimp only
  have hv := contMDiffOn_source_partial hs hF (m := ∞) (by simp) (0, v)
  have hc : ContDiffAt ℝ ∞ (fun r : ℝ => (r, z)) t :=
    contDiffAt_id.prodMk contDiffAt_const
  have hd := hasDerivAt_metricFamilySourcePairing hG ht hs hF hv hv hc hz
  have hcderiv : deriv (fun r : ℝ => (r, z)) t = (1, 0) := by
    exact ((hasDerivAt_id t).prodMk (hasDerivAt_const t z)).deriv
  rw [hcderiv] at hd
  change HasDerivAt _
    (deriv _ t +
      (G t).inner (F (t, z)) (sourceCovariantPartial (G t) F (t, z) (1, 0) (0, v)) _ +
      (G t).inner (F (t, z)) _ (sourceCovariantPartial (G t) F (t, z) (1, 0) (0, v))) t at hd
  rw [sourceCovariantPartial_symm (G t) hs hF hz (1, 0) (0, v)] at hd
  simp only [sourceCovariantPartial, sourceSectionCovariantDerivative_parameter_slice] at hd
  rw [(G t).symm (F (t, z))
    (mfderiv 𝓘(ℝ, ℝ × A) 𝓘(ℝ, E) F (t, z) (0, v))] at hd
  convert hd using 1
  ring

end DifferentialGeometry.Geometry
