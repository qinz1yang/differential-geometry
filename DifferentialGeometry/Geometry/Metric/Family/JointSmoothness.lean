import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.ChartGram

noncomputable section

open Bundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartGramMatrix_joint_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  have hmetric := hg.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩ :
    J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet ⊆ J ×ˢ Set.univ)
  have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (Prod.snd : ℝ × M → M)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := contMDiffOn_snd
  have hv := (chartBasisVec_contMDiffOn (I := I) x₀ i).comp hsnd (fun p hp => hp.2)
  have hw := (chartBasisVec_contMDiffOn (I := I) x₀ j).comp hsnd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × M => p.2) hmetric hv hw
  intro p hp
  have h := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at h
  exact h.2

omit [FiniteDimensional ℝ E] in
private theorem metric_coeff_contDiffOn
    (J : Set ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M))) :
    ∀ x (X Y : TangentSpace I x),
      ContDiffOn ℝ ∞ (fun t : ℝ => (g t).inner x X Y) J := by
  intro x X Y
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun t : ℝ => (t, x)) J := contMDiffOn_id.prodMk contMDiffOn_const
  have hmetric := hg.comp hcurve (fun t ht => ⟨ht, Set.mem_univ x⟩)
  have hv : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun _ : ℝ => TotalSpace.mk' E (E := TangentSpace I) x X) J :=
    contMDiffOn_const
  have hw : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun _ : ℝ => TotalSpace.mk' E (E := TangentSpace I) x Y) J :=
    contMDiffOn_const
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun _ : ℝ => x) hmetric hv hw
  have hscalar : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun t : ℝ => (g t).inner x X Y) J := by
    intro t ht
    have hpt := happ t ht
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
    exact hpt.2
  exact hscalar.contDiffOn

omit [FiniteDimensional ℝ E] in
private theorem metric_frame_contMDiffOn
    (J : Set ℝ) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    {Idx : Type} (frame : Idx → (x : M) → TangentSpace I x) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u) (i j : Idx) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (g p.1).inner p.2 (frame i p.2) (frame j p.2))
      (J ×ˢ u) := by
  have hmetric := hg.mono (fun p hp => ⟨hp.1, Set.mem_univ p.2⟩ :
    J ×ˢ u ⊆ J ×ˢ Set.univ)
  have hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame i p.2)) (J ×ˢ u) :=
    (hframe.contMDiffOn i).comp contMDiffOn_snd (fun p hp => hp.2)
  have hw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' E p.2 (frame j p.2)) (J ×ˢ u) :=
    (hframe.contMDiffOn j).comp contMDiffOn_snd (fun p hp => hp.2)
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × M => p.2) hmetric hv hw
  intro p hp
  have hpt := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpt
  exact hpt.2

theorem metricFamilySmoothOn_of_contMDiffOn
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ (Set.univ : Set M))) :
    MetricFamilySmoothOn (I := I) (M := M) D g := by
  have hcoeff := metric_coeff_contDiffOn D.carrier g hg
  refine ⟨fun x X Y => (hcoeff x X Y).mono D.regular_subset,
    fun x X Y => (hcoeff x X Y).continuousOn, ?_, ?_⟩
  · apply metricTensorCont_of_chartGram (K := D.carrier) g
    intro x₀ i j
    have hincl : ContinuousOn
        (fun q : {t : ℝ // t ∈ D.carrier} × M => ((q.1 : ℝ), q.2))
        {q : {t : ℝ // t ∈ D.carrier} × M |
          q.2 ∈ (trivializationAt E (TangentSpace I) x₀).baseSet} :=
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    have hgram := (chartGramMatrix_joint_contMDiffOn g D.carrier hg x₀ i j).continuousOn
    have h := hgram.comp hincl (fun q hq => ⟨q.1.2, hq⟩)
    exact h
  · intro Idx _ frame u hframe i j
    exact (metric_frame_contMDiffOn D.carrier g hg frame hframe i j).mono
      (Set.prod_mono D.regular_subset Set.Subset.rfl)

end DifferentialGeometry.Geometry.Curvature
