import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

/-!
Actual curve lengths agree under boundary charts and their interior inverses when the
ambient metric is the original chart tensor. No boundaryless instance on M is required.
-/

set_option autoImplicit false

noncomputable section

open Manifold Set Bundle MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] {H : Type*}
  [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundaryChart_metricPathELength
    (g : SmoothRiemannianMetric I M) (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : M) (γ : ℝ → M) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b))
    (hsource : ∀ t ∈ Ioo a b, γ t ∈ (extChartAt I p).source)
    (hmetric : ∀ t ∈ Ioo a b, G.inner (extChartAt I p (γ t)) =
      metricFlatModelInChart g p (extChartAt I p (γ t))) :
    metricPathELength G ((extChartAt I p) ∘ γ) a b = metricPathELength g γ a b := by
  rw [metricPathELength_eq, metricPathELength_eq]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hs : γ t ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using hsource t ht
  have hgd :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  rw [mfderiv_comp_apply t (mdifferentiableAt_extChartAt hs) hgd]
  simp only [Function.comp_apply]
  congr 2
  change G.inner (extChartAt I p (γ t))
    (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t) (mfderiv 𝓘(ℝ) I γ t 1))
    (mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t) (mfderiv 𝓘(ℝ) I γ t 1)) = _
  let v : E := mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ t) (mfderiv 𝓘(ℝ) I γ t 1)
  have hcalc := metricFlatModelInChart_apply_of_target g p
    ((extChartAt I p).map_source (hsource t ht)) v v
  rw [(extChartAt I p).left_inv (hsource t ht)] at hcalc
  have hbase : γ t ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    simpa using hs
  have hv : (trivializationAt E (TangentSpace I) p).symmL ℝ (γ t) v =
      mfderiv 𝓘(ℝ) I γ t 1 := by
    dsimp only [v]
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hs]
    exact Trivialization.symmL_continuousLinearMapAt
      (R := ℝ) (trivializationAt E (TangentSpace I) p) hbase (mfderiv 𝓘(ℝ) I γ t 1)
  rw [hv] at hcalc
  exact (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v v) (hmetric t ht)).trans hcalc

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundaryChart_symm_metricPathELength
    (g : SmoothRiemannianMetric I M) (G : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (p : M) (γ : ℝ → E) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b))
    (htarget : ∀ t ∈ Ioo a b, γ t ∈ interior (extChartAt I p).target)
    (hmetric : ∀ t ∈ Ioo a b, G.inner (γ t) = metricFlatModelInChart g p (γ t)) :
    metricPathELength g ((extChartAt I p).symm ∘ γ) a b = metricPathELength G γ a b := by
  rw [metricPathELength_eq, metricPathELength_eq]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hsd := ((contMDiffOn_extChartAt_symm p).contMDiffAt
    (mem_interior_iff_mem_nhds.mp (htarget t ht))).mdifferentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hgd :=
    (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  rw [mfderiv_comp_apply t hsd hgd]
  simp only [Function.comp_apply]
  congr 2
  let v : E := mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t 1
  change g.inner ((extChartAt I p).symm (γ t))
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (γ t) v)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (γ t) v) = G.inner (γ t) v v
  exact (boundaryChart_metric_inner_of_interior g p (htarget t ht) v v).symm.trans
    (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v v) (hmetric t ht).symm)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
