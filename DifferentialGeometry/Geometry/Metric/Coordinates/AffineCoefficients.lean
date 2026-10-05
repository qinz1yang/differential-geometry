import DifferentialGeometry.Geometry.Metric.SourceCoefficients
import DifferentialGeometry.Topology.Manifold.AffineCharts



open Set Bundle Manifold DifferentialGeometry Filter
open scoped ContDiff Bundle Manifold Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology DifferentialGeometry.Analysis

variable {A E V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]





theorem iteratedFDeriv_affineChart_metricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {c : OpenPartialHomeomorph A M}
    (hc : ContMDiffOn 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ c c.source)
    (a : A) (L : V ≃L[ℝ] A) {x : V} (hx : a + L x ∈ c.source) (v w : V) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => g.inner (affineChart c a L y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y w)) x =
      (iteratedFDeriv ℝ k (fun y => g.inner (c y)
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L v))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L w))) (a + L x)).compContinuousLinearMap
          (fun _ : Fin k => (L : V →L[ℝ] A)) := by
  let H : A → ℝ := fun y => g.inner (c y)
    (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L v)) (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c y (L w))
  have hH : ContDiffOn ℝ k H c.source :=
    (contDiffOn_sourceMetricPairing g c.open_source hc (L v) (L w)).of_le
      (by exact_mod_cast le_top)
  have heq : (fun y => g.inner (affineChart c a L y)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y v)
      (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) (affineChart c a L) y w)) =ᶠ[𝓝 x]
      (fun y => g.inner (c (a + L y))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c (a + L y) (L v))
        (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) c (a + L y) (L w))) := by
    filter_upwards [(c.open_source.preimage
      (continuous_const.add L.continuous)).mem_nhds hx] with y hy
    have hcy := ((hc _ hy).contMDiffAt (c.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    rw [affineChart_mfderiv a L hcy v, affineChart_mfderiv a L hcy w, affineChart_apply]
  have hd := iteratedFDeriv_comp_affine (f := H) (k := k) c.open_source hH a
    (L : V →L[ℝ] A) hx
  exact (heq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds.trans hd

end DifferentialGeometry.Geometry
