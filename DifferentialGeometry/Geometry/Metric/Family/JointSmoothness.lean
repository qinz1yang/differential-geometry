import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

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

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] in
theorem chartGramMatrix_joint_contMDiffOn_of_pullback
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (h : ℝ → SmoothRiemannianMetric J N) (Y : N → M) (hY : ContMDiff J I ∞ Y)
    (hinner : ∀ t ∈ A, ∀ x (u v : TangentSpace J x),
      (h t).inner x u v = (g t).inner (Y x) (mfderiv J I Y x u) (mfderiv J I Y x v))
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ) ∞
      (fun p : ℝ × N => chartGramMatrix (I := J) (h p.1) x₀ p.2 i j)
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × N => (p.1, Y p.2)) :=
    contMDiff_fst.prodMk (hY.comp contMDiff_snd)
  have hmetric := hg.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩ :
    Set.MapsTo (fun p : ℝ × N => (p.1, Y p.2))
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet)
      (A ×ˢ (Set.univ : Set M)))
  have hvec (k : Fin (Module.finrank ℝ F)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod J) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × N => TotalSpace.mk' E (E := TangentSpace I)
          (Y p.2) (mfderiv J I Y p.2 (chartBasisVecFiber (I := J) x₀ k p.2)))
        (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
    have hv := (chartBasisVec_contMDiffOn (I := J) x₀ k).comp
      (contMDiffOn_snd : ContMDiffOn (𝓘(ℝ, ℝ).prod J) J ∞
        (Prod.snd : ℝ × N → N) (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet))
      (fun p hp => hp.2)
    exact (hY.contMDiff_tangentMap le_rfl).comp_contMDiffOn hv
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × N => Y p.2)
    hmetric (hvec i) (hvec j)
  intro p hp
  have hs := happ p hp
  rw [Bundle.contMDiffWithinAt_totalSpace] at hs
  have heq : (fun q : ℝ × N => chartGramMatrix (I := J) (h q.1) x₀ q.2 i j)
      =ᶠ[nhdsWithin p (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet)]
      (fun q : ℝ × N => (g q.1).inner (Y q.2)
        (mfderiv J I Y q.2 (chartBasisVecFiber (I := J) x₀ i q.2))
        (mfderiv J I Y q.2 (chartBasisVecFiber (I := J) x₀ j q.2))) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hinner q.1 hq.1 q.2 _ _
  exact hs.2.congr_of_eventuallyEq heq (hinner p.1 hp.1 p.2 _ _)

end DifferentialGeometry.Geometry.Curvature
