import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import Mathlib.Topology.Instances.Matrix

noncomputable section

namespace DifferentialGeometry.Integral.Measure

open Bundle _root_.Manifold Set Filter DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {P : Type*} [TopologicalSpace P]

theorem chartDensity_family_continuousOn
    (g : P → SmoothRiemannianMetric I M) {J : Set P} (α : M)
    (hgram : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun p : P × M => chartDensity (I := I) (g p.1) α p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  classical
  have hmatrix : ContinuousOn
      (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hgram i)
  have hdet : ContinuousOn
      (fun p : P × M => (chartGramMatrix (I := I) (g p.1) α p.2).det)
      (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    continuous_id.matrix_det.comp_continuousOn hmatrix
  exact Real.continuous_sqrt.comp_continuousOn hdet

variable [T2Space M] [SigmaCompactSpace M]

theorem riemannianVolumeDensity_family_continuousOn
    (q : SmoothRiemannianMetric I M) (g : P → SmoothRiemannianMetric I M) {J : Set P}
    (hgram : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : P × M => chartGramMatrix (I := I) (g p.1) α p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun p : P × M => riemannianVolumeDensity q (g p.1) p.2)
      (J ×ˢ (univ : Set M)) := by
  rintro p ⟨hpJ, _⟩
  let α : M := p.2
  let e := trivializationAt E (TangentSpace I : M → Type _) α
  have hpbase : p.2 ∈ e.baseSet := by
    simpa only [e, α] using
      mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) p.2
  have hnum := chartDensity_family_continuousOn (I := I) g α (hgram α)
  have hden : ContinuousOn (fun r : P × M => chartDensity (I := I) q α r.2)
      (J ×ˢ e.baseSet) :=
    (chartDensity_contMDiffOn (I := I) q α).continuousOn.comp continuousOn_snd
      (fun _ hr => hr.2)
  have hratio : ContinuousOn
      (fun r : P × M => chartDensity (I := I) (g r.1) α r.2 /
        chartDensity (I := I) q α r.2) (J ×ˢ e.baseSet) :=
    hnum.div hden fun r hr => ne_of_gt (chartDensity_pos (I := I) q α hr.2)
  have hlocal : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ (univ : Set M)] p := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds ((e.open_baseSet.preimage continuous_snd).mem_nhds hpbase)] with r hr hb
    exact ⟨hr.1, hb⟩
  have hratioAt := (hratio p ⟨hpJ, hpbase⟩).mono_of_mem_nhdsWithin hlocal
  have heq : (fun r : P × M => riemannianVolumeDensity q (g r.1) r.2) =ᶠ[𝓝 p]
      fun r : P × M => chartDensity (I := I) (g r.1) α r.2 /
        chartDensity (I := I) q α r.2 := by
    filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds hpbase] with r hr
    exact riemannianVolumeDensity_apply_of_mem_chart_source (I := I) q (g r.1) α hr
  exact hratioAt.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end DifferentialGeometry.Integral.Measure
