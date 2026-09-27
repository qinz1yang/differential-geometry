import DifferentialGeometry.Geometry.Metric.Construction.SmoothMetricFromCoefficients

noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_metric_of_bilinearField [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) :
    ∃ g : SmoothRiemannianMetric 𝓘(ℝ, E) E,
      ∀ x v w, g.inner x v w = B x v w := by
  apply Geometry.smoothMetric_of_localCoeff B hsymm hpos
  intro x₀ i j
  simp only [Geometry.frameVec, TangentBundle.symmL_model_space]
  exact ((hB.clm_apply contDiff_const).clm_apply contDiff_const).contMDiff.contMDiffOn

def smoothMetricOfBilinearField [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) : SmoothRiemannianMetric 𝓘(ℝ, E) E :=
  (exists_metric_of_bilinearField B hsymm hpos hB).choose

theorem smoothMetricOfBilinearField_inner [FiniteDimensional ℝ E]
    (B : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hsymm : ∀ x v w, B x v w = B x w v)
    (hpos : ∀ x v, v ≠ 0 → 0 < B x v v)
    (hB : ContDiff ℝ ∞ B) (x v w : E) :
    (smoothMetricOfBilinearField B hsymm hpos hB).inner x v w = B x v w :=
  (exists_metric_of_bilinearField B hsymm hpos hB).choose_spec x v w

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_metric_inner (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) :
    ContDiff ℝ ∞ (fun x : E =>
      (show E →L[ℝ] E →L[ℝ] ℝ from by exact g.inner x)) := by
  apply ContMDiff.contDiff
  intro x
  have hs := g.contMDiff x
  rw [contMDiffAt_section] at hs
  have heq : (fun y : E =>
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y => TangentSpace 𝓘(ℝ, E) y →L[ℝ]
          TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) x) ⟨y, g.inner y⟩).2) =
      (fun y : E => (show E →L[ℝ] E →L[ℝ] ℝ from by exact g.inner y)) := by
    funext y
    ext v w
    rw [Geometry.metricCoeffInModel_apply]
    · simp only [TangentBundle.symmL_model_space]
      rfl
    · exact Set.mem_univ y
  rwa [heq] at hs

end DifferentialGeometry.Geometry.Riemannian
