import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Compact
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

theorem ricci_flow_pullback_eq_of_initial_isometry
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (Φ : M ≃ₘ⟮I, I⟯ M) (hinit : Diffeomorph.pullbackMetric (g a) Φ = g a) :
    ∀ t ∈ Ico a b, Diffeomorph.pullbackMetric (g t) Φ = g t := by
  have hpullgram := chartGramMatrix_joint_contMDiffOn_of_pullback g (Ico a b) hjoint
    (fun t => Diffeomorph.pullbackMetric (g t) Φ) Φ Φ.contMDiff
    (fun t _ x v w => Diffeomorph.pullbackMetric_inner (g t) Φ x v w)
  have hpulljoint := metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => Diffeomorph.pullbackMetric (g t) Φ) (Ico a b) hpullgram
  apply ricci_flow_forward_unique_of_joint_contMDiffOn
    (fun t => Diffeomorph.pullbackMetric (g t) Φ) g hab
    hpulljoint hjoint ?_ hpde hinit
  intro t ht x v w
  simpa only [Diffeomorph.pullbackMetric_inner,
    DifferentialGeometry.HCGCompactness.ricciTensor_pullback] using
    hpde t ht (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)

end DifferentialGeometry.PDE.RicciFlow
