import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
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

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y]

theorem metric_lower_on_compact_of_localPullMetric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric I X}
    (hG : MetricFamilySmoothOn (I := I) (M := X) D G)
    (g : ℝ → SmoothRiemannianMetric J Y)
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    {A B : Set ℝ} (hB : IsCompact B) (hBD : B ⊆ D.carrier) (hAB : A ⊆ B)
    {K : Set Y} (hK : IsCompact K) (hKrange : K ⊆ range f)
    (gRef : SmoothRiemannianMetric J Y)
    (hmetric : ∀ t ∈ A, G t = localPullMetric (g t) f hf) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ A, ∀ y ∈ K, ∀ v : TangentSpace J y,
      c * gRef.inner y v v ≤ (g t).inner y v v := by
  have hemb : _root_.Topology.IsOpenEmbedding f :=
    .of_continuous_injective_isOpenMap hf.contMDiff.continuous hinj hf.isOpenMap
  have hpre : IsCompact (f ⁻¹' K) :=
    hemb.isEmbedding.isInducing.isCompact_preimage' hK hKrange
  obtain ⟨c, hc, hbound⟩ := hG.metric_lower_on_compact_time hB hBD hpre
    (localPullMetric gRef f hf)
  refine ⟨c, hc, ?_⟩
  intro t ht y hy v
  obtain ⟨x, rfl⟩ := hKrange hy
  obtain ⟨w, hw⟩ := (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective v
  have hh := hbound t (hAB ht) x hy w
  rw [hmetric t ht, localPullMetric_inner, localPullMetric_inner] at hh
  change mfderiv I J f x w = v at hw
  simpa only [hw] using hh

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

end

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y] [T2Space Y]

theorem exists_pos_isCompact_riemannianClosedBallOf_metric_lower_of_localPullMetric
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric I X}
    (hG : MetricFamilySmoothOn (I := I) (M := X) D G)
    (g : ℝ → SmoothRiemannianMetric J Y)
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (p : Y) (hp : p ∈ range f) {A L : Set ℝ} (hL : IsCompact L) (hAL : A ⊆ L)
    (τ : ℝ → ℝ) (hτ : ContinuousOn τ L) (hτD : MapsTo τ L D.carrier)
    (gRef : SmoothRiemannianMetric J Y)
    (hmetric : ∀ u ∈ A, G (τ u) = localPullMetric (g (τ u)) f hf) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ IsCompact (riemannianClosedBallOf gRef p r) ∧
      riemannianClosedBallOf gRef p r ⊆ range f ∧
      ∀ u ∈ A, ∀ y ∈ riemannianClosedBallOf gRef p r, ∀ v : TangentSpace J y,
        c * gRef.inner y v v ≤ (g (τ u)).inner y v v := by
  obtain ⟨r, hr, hcpt, hball⟩ :=
    Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds
      gRef p (hf.isOpenMap.isOpen_range.mem_nhds hp)
  have hmet : ∀ t ∈ τ '' A, G t = localPullMetric (g t) f hf := by
    rintro t ⟨u, hu, rfl⟩
    exact hmetric u hu
  obtain ⟨c, hc, hbound⟩ := hG.metric_lower_on_compact_of_localPullMetric g f hf hinj
    (hL.image_of_continuousOn hτ) (by rintro t ⟨u, hu, rfl⟩; exact hτD hu)
    (image_mono hAL) hcpt hball gRef hmet
  exact ⟨r, c, hr, hc, hcpt, hball, fun u hu y hy v => hbound (τ u) ⟨u, hu, rfl⟩ y hy v⟩

end DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
