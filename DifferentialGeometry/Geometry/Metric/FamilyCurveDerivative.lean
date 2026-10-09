import DifferentialGeometry.Geometry.Metric.FamilySectionPairing
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Analysis.Calculus.Derivative.Diagonal



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_metricFamilyCurvePairing
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {t : ℝ} (ht : D.regular ∈ 𝓝 t)
    {γ : ℝ → M} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ t)
    {V W : ∀ s, TangentSpace 𝓘(ℝ, E) (γ s)}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun s => TotalSpace.mk' E (γ s) (V s)) t)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun s => TotalSpace.mk' E (γ s) (W s)) t) :
    HasDerivAt (fun s => (G s).inner (γ s) (V s) (W s))
      (deriv (fun s => (G s).inner (γ t) (V t) (W t)) t +
        (G t).inner (γ t) (covDerivAlong (G t) γ V t) (W t) +
        (G t).inner (γ t) (V t) (covDerivAlong (G t) γ W t)) t := by
  let F : ℝ × ℝ → ℝ := fun q => (G q.1).inner (γ q.2) (V q.2) (W q.2)
  have hF : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F (t, t) :=
    contMDiffAt_metricFamilySectionPairing hG contMDiffAt_fst
      (hγ.comp (t, t) contMDiffAt_snd) ht
      (hV.comp (t, t) contMDiffAt_snd) (hW.comp (t, t) contMDiffAt_snd)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hF
  have hFd : DifferentiableAt ℝ F (t, t) := hF.contDiffAt.differentiableAt (by simp)
  have hdiag : DifferentiableAt ℝ (fun s => F (s, s)) t :=
    hFd.comp (f := fun s : ℝ => (s, s)) t (differentiableAt_id.prodMk differentiableAt_id)
  have hinner := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) (G t) γ V W t hγ
    ((contDiffAt_chartRepAt_of_section hV).differentiableAt (by simp))
    ((contDiffAt_chartRepAt_of_section hW).differentiableAt (by simp))
  have he := DifferentialGeometry.Analysis.deriv_diagonal hFd
  dsimp only [F] at he hdiag
  rw [hinner.deriv] at he
  rw [← add_assoc] at he
  rw [← he]
  exact hdiag.hasDerivAt

end DifferentialGeometry.Geometry
