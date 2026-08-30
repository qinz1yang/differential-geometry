import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Integral
namespace Measure

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartDensity_family_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (α : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => chartDensity (I := I) (g p.1) α p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  have hdet :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          (chartGramMatrix (I := I) (g p.1) α p.2).det)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have heq :
        (fun p : ℝ × M =>
          (chartGramMatrix (I := I) (g p.1) α p.2).det) =
        fun p : ℝ × M =>
          ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
            (Equiv.Perm.sign σ : ℝ) *
              ∏ i, chartGramMatrix (I := I) (g p.1) α p.2 (σ i) i := by
      funext p
      rw [Matrix.det_apply]
      simp [Units.smul_def]
    rw [heq]
    refine contMDiffOn_finsetSum fun σ _ => ?_
    exact (contMDiffOn_const (c := (Equiv.Perm.sign σ : ℝ))).mul
      (contMDiffOn_finsetProd fun i _ => hgram (σ i) i)
  intro p hp
  have hne : (chartGramMatrix (I := I) (g p.1) α p.2).det ≠ 0 :=
    ne_of_gt (chartGramMatrix_det_pos (I := I) (g p.1) α hp.2)
  exact (Real.contDiffAt_sqrt hne).comp_contMDiffWithinAt
    (f := fun r : ℝ × M => (chartGramMatrix (I := I) (g r.1) α r.2).det)
    (hdet p hp)

variable [T2Space M] [SigmaCompactSpace M]

theorem riemannianVolumeDensity_family_contMDiffOn
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ} (hJ : IsOpen J)
    (hgram : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => riemannianVolumeDensity q (g p.1) p.2)
      (J ×ˢ (Set.univ : Set M)) := by
  rintro p ⟨hpJ, -⟩
  let α : M := p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  have hpbase : p.2 ∈ e.baseSet := by
    simpa only [e, α] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) p.2
  have hnum := chartDensity_family_contMDiffOn (I := I) g α (hgram α)
  have hden :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun r : ℝ × M => chartDensity (I := I) q α r.2)
        (J ×ˢ e.baseSet) := by
    exact (chartDensity_contMDiffOn (I := I) q α).comp contMDiffOn_snd
      (fun r hr => hr.2)
  have hratio :
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun r : ℝ × M =>
          chartDensity (I := I) (g r.1) α r.2 /
            chartDensity (I := I) q α r.2)
        (J ×ˢ e.baseSet) := by
    exact hnum.div₀ hden fun r hr =>
      ne_of_gt (chartDensity_pos (I := I) q α hr.2)
  have hratioAt :
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun r : ℝ × M =>
          chartDensity (I := I) (g r.1) α r.2 /
            chartDensity (I := I) q α r.2) p :=
    hratio.contMDiffAt ((hJ.prod e.open_baseSet).mem_nhds ⟨hpJ, hpbase⟩)
  have heq :
      (fun r : ℝ × M => riemannianVolumeDensity q (g r.1) r.2) =ᶠ[𝓝 p]
        fun r : ℝ × M =>
          chartDensity (I := I) (g r.1) α r.2 /
            chartDensity (I := I) q α r.2 := by
    filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds hpbase] with r hr
    exact riemannianVolumeDensity_apply_of_mem_chart_source
      (I := I) q (g r.1) α hr
  exact (hratioAt.congr_of_eventuallyEq heq).contMDiffWithinAt

theorem riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => riemannianVolumeDensity q (G.metric p.1) p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  apply riemannianVolumeDensity_family_contMDiffOn q G.metric D.regular_isOpen
  intro α i j
  exact MetricFamilySmoothOn.chartGramMatrix_contDiffOn
    (I := I) hG (Set.Subset.rfl) α i j

theorem riemannianVolumeDensity_swap_contMDiffOn_of_metricFamilySmoothOn
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => riemannianVolumeDensity (G.metric p.1) q p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  have hρ := riemannianVolumeDensity_contMDiffOn_of_metricFamilySmoothOn hG q
  refine ContMDiffOn.congr (hρ.inv₀ fun p _ => ne_of_gt
    (riemannianVolumeDensity_pos q (G.metric p.1) p.2)) ?_
  intro p _
  exact eq_inv_of_mul_eq_one_right
    (riemannianVolumeDensity_mul_swap q (G.metric p.1) p.2)

end Measure
end Integral
end DifferentialGeometry
