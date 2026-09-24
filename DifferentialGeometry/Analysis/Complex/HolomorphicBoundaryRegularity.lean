import DifferentialGeometry.Geometry.HarmonicMap.DiskBoundaryRegularity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.Euclidean
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

section

noncomputable section

open Set Filter Manifold InnerProductSpace
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold

namespace Complex

private theorem planarTension_euclideanMetric_eq_zero_of_analyticAt
    {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    planarTension (euclideanMetric (E := ℂ)) F z = 0 := by
  have hFr : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 2 F z :=
    (hF.contDiffAt.restrict_scalars ℝ).contMDiffAt
  have h := chart_planarTension (euclideanMetric (E := ℂ)) hFr
    (a := F z) (mem_chart_source ℂ (F z))
  simp only [TangentBundle.continuousLinearMapAt_model_space,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    DifferentialGeometry.Geometry.Connection.chartChristoffelContraction_euclideanMetric,
    add_zero] at h
  exact h.trans (hF.harmonicAt.2.eq_of_nhds)

theorem contDiffOn_closedDisk_of_differentiableOn_of_embedded_loop
    {T : ℝ} (hT : 0 < T) {γ : AddCircle T → ℂ}
    (hγ : Topology.IsEmbedding γ)
    (hγc : ContDiff ℝ ∞ (fun s : ℝ => γ (s : AddCircle T)))
    (hγv : ∀ θ : ℝ, deriv (fun s : ℝ => γ (s : AddCircle T)) θ ≠ 0)
    {F : ℂ → ℂ} (hF : ContinuousOn F (Metric.closedBall (0 : ℂ) 1))
    (hFi : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (htrace : ∀ z : ℂ, ‖z‖ = 1 → F z ∈ range γ) :
    ContDiffOn ℝ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
  have hFa (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : AnalyticAt ℂ F z :=
    hFi.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hFs : ContDiffOn ℝ ∞ F (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact ((hFa z hz).contDiffAt.restrict_scalars ℝ).contDiffWithinAt
  have hconf (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      (euclideanMetric (E := ℂ)).inner (F z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z Complex.I) = 0 ∧
        (euclideanMetric (E := ℂ)).inner (F z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z (1 : ℂ))
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z (1 : ℂ)) =
        (euclideanMetric (E := ℂ)).inner (F z)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z Complex.I)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F z Complex.I) := by
    apply conformal_mfderiv_comp_complex (euclideanMetric (E := ℂ))
      (U := id) mdifferentiableAt_id (hFa z hz).differentiableAt
    · simp only [mfderiv_id, euclideanMetric_inner]
      change inner ℝ (1 : ℂ) Complex.I = 0
      norm_num
    · simp only [mfderiv_id, euclideanMetric_inner]
      change inner ℝ (1 : ℂ) (1 : ℂ) = inner ℝ Complex.I Complex.I
      simp only [real_inner_self_eq_norm_sq, norm_one, Complex.norm_I]
  have h := contMDiffOn_closedDisk_of_embedded_loop (euclideanMetric (E := ℂ))
    hT hγ hγc.contMDiff
    (fun θ => by simpa only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hγv θ)
    hF hFs.contMDiffOn htrace (fun z hz => (hconf z hz).1) (fun z hz => (hconf z hz).2)
    (fun z hz => planarTension_euclideanMetric_eq_zero_of_analyticAt (hFa z hz))
  exact h.contDiffOn

end Complex

end

end
