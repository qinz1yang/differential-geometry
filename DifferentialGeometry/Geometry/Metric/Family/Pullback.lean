import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem MetricFamilySmoothOn.of_pullback
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (h : ℝ → SmoothRiemannianMetric J N)
    (f : N → M) (hf : ContMDiff J I ∞ f)
    (hinner : ∀ t x (v w : TangentSpace J x),
      (h t).inner x v w = (g t).inner (f x) (mfderiv J I f x v) (mfderiv J I f x w)) :
    MetricFamilySmoothOn D h where
  coeff x v w := by
    simp only [hinner]
    exact hg.coeff (f x) _ _
  coeff_cont x v w := by
    simp only [hinner]
    exact hg.coeff_cont (f x) _ _
  metricTensor_cont := by
    apply tensor0SFamilyContinuousOnSet.congr
      (hg.metricTensor_cont.pullback_of_contMDiff _ f (hf.of_le (by norm_num)))
    intro t _ x
    ext slots
    exact (hinner t x (slots 0) (slots 1)).symm
  frameCompSmooth := by
    intro Idx _ frame u hframe i j
    have hmg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (D.regular ×ˢ (Set.univ : Set M)) := by
      intro p hp
      exact (hg.metricCLMSmoothAt (D.regular_isOpen.mem_nhds hp.1)).contMDiffWithinAt
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × N => (p.1, f p.2)) :=
      contMDiff_fst.prodMk (hf.comp contMDiff_snd)
    have hmg' := hmg.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩ :
      Set.MapsTo (fun p : ℝ × N => (p.1, f p.2)) (D.regular ×ˢ u) (D.regular ×ˢ Set.univ))
    have hv (k : Idx) : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F)) ∞
        (fun p : ℝ × N => TotalSpace.mk' F p.2 (frame k p.2)) (D.regular ×ˢ u) :=
      (hframe.contMDiffOn k).comp contMDiffOn_snd (fun p hp => hp.2)
    have hvf (k : Idx) := (hf.contMDiff_tangentMap le_rfl).comp_contMDiffOn (hv k)
    have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
      (b := fun p : ℝ × N => f p.2) hmg' (hvf i) (hvf j)
    have hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × N => (g p.1).inner (f p.2)
          (mfderiv J I f p.2 (frame i p.2)) (mfderiv J I f p.2 (frame j p.2)))
        (D.regular ×ˢ u) := by
      intro p hp
      have hs := happ p hp
      rw [Bundle.contMDiffWithinAt_totalSpace] at hs
      exact hs.2
    apply hscalar.congr
    intro p _
    exact hinner p.1 p.2 _ _


theorem MetricFamilySmoothOn.pullback
    [T2Space M]
    {D : RealTimeInterval}
    (g : ℝ → SmoothRiemannianMetric J N) (hg : MetricFamilySmoothOn (I := J) D g)
    (Φ : M ≃ₘ⟮I, J⟯ N) :
    MetricFamilySmoothOn (I := I) D (fun t => Diffeomorph.pullbackMetricCross (g t) Φ) :=
  hg.of_pullback (fun t => Diffeomorph.pullbackMetricCross (g t) Φ) Φ Φ.contMDiff
    (fun t x v w => Diffeomorph.pullbackMetricCross_inner (g t) Φ x v w)

end DifferentialGeometry.Geometry.Curvature

end
