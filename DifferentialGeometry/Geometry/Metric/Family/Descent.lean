import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Pullback.Local

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Filter Set DifferentialGeometry.Integral.Measure
  DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ F] [T2Space N] in
private theorem metric_inner_eq_of_local_section
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (hpull : localPullMetric h f hf = g)
    (Y : N → M) {y : N} (hY : ContMDiffAt J I ∞ Y y)
    (hsec : f ∘ Y =ᶠ[𝓝 y] id) (v w : TangentSpace J y) :
    h.inner y v w = g.inner (Y y) (mfderiv J I Y y v) (mfderiv J I Y y w) := by
  have heq : f (Y y) = y := hsec.eq_of_nhds
  have hder : (mfderiv I J f (Y y)).comp (mfderiv J I Y y) =
      ContinuousLinearMap.id ℝ (TangentSpace J y) := by
    rw [← mfderiv_comp y (hf.contMDiff.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp)), hsec.mfderiv_eq, mfderiv_id]
  have hv := congrArg (fun L : TangentSpace J y →L[ℝ] TangentSpace J (f (Y y)) => L v) hder
  have hw := congrArg (fun L : TangentSpace J y →L[ℝ] TangentSpace J (f (Y y)) => L w) hder
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [← hpull, localPullMetric_inner, hv, hw, heq]
  rfl

omit [T2Space N] in
private theorem chartGramMatrix_joint_contMDiffOn_of_surjective_localPullMetric
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ univ))
    (h : ℝ → SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hpull : ∀ t ∈ A, localPullMetric (h t) f hf = g t)
    (x₀ : N) (i j : Fin (Module.finrank ℝ F)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ) ∞
      (fun p : ℝ × N => chartGramMatrix (I := J) (h p.1) x₀ p.2 i j)
      (A ×ˢ (trivializationAt F (TangentSpace J) x₀).baseSet) := by
  intro p hp
  obtain ⟨x, hx⟩ := hsurj p.2
  let Y := (hf x).localInverse
  let V := Y.source ∩ (trivializationAt F (TangentSpace J) x₀).baseSet
  have hY : ContMDiffOn J I ∞ Y V :=
    (hf x).localInverse_contMDiffOn.mono inter_subset_left
  have hpV : p.2 ∈ V := ⟨hx ▸ (hf x).localInverse_mem_source, hp.2⟩
  have hVopen : IsOpen V := Y.open_source.inter
    (trivializationAt F (TangentSpace J) x₀).open_baseSet
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × N => (p.1, Y p.2)) (A ×ˢ V) :=
    contMDiffOn_fst.prodMk (hY.comp contMDiffOn_snd (fun p hp => hp.2))
  have hmetric := hg.comp hmap (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hvec (k : Fin (Module.finrank ℝ F)) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod J) (I.prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × N => TotalSpace.mk' E (E := TangentSpace I)
          (Y p.2) (mfderiv J I Y p.2 (chartBasisVecFiber (I := J) x₀ k p.2)))
        (A ×ˢ V) := by
    have hv := ((chartBasisVec_contMDiffOn (I := J) x₀ k).mono inter_subset_right).comp
      (contMDiffOn_snd : ContMDiffOn (𝓘(ℝ, ℝ).prod J) J ∞
        (Prod.snd : ℝ × N → N) (A ×ˢ V)) (fun p hp => hp.2)
    have ht := hY.contMDiffOn_tangentMapWithin (m := ∞) le_rfl hVopen.uniqueMDiffOn
    have ht' := ht.comp hv (fun p hp => hp.2)
    apply ht'.congr
    intro q hq
    change (⟨Y q.2, mfderiv J I Y q.2
      (chartBasisVecFiber (I := J) x₀ k q.2)⟩ : TangentBundle I M) =
        ⟨Y q.2, mfderivWithin J I Y V q.2
          (chartBasisVecFiber (I := J) x₀ k q.2)⟩
    rw [mfderivWithin_eq_mfderiv (hVopen.uniqueMDiffOn q.2 hq.2)
      (((hY q.2 hq.2).contMDiffAt (hVopen.mem_nhds hq.2)).mdifferentiableAt (by simp))]
  have happ := ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I (M := M)) (E₂ := TangentSpace I (M := M))
    (E₃ := Bundle.Trivial M ℝ) (b := fun p : ℝ × N => Y p.2)
    hmetric (hvec i) (hvec j)
  have heq (q : ℝ × N) (hq : q ∈ A ×ˢ V) :
      chartGramMatrix (I := J) (h q.1) x₀ q.2 i j =
      (g q.1).inner (Y q.2)
        (mfderiv J I Y q.2 (chartBasisVecFiber (I := J) x₀ i q.2))
        (mfderiv J I Y q.2 (chartBasisVecFiber (I := J) x₀ j q.2)) := by
    apply metric_inner_eq_of_local_section (g q.1) (h q.1) f hf (hpull q.1 hq.1) Y
      ((hY q.2 hq.2).contMDiffAt (hVopen.mem_nhds hq.2))
    apply Filter.eventuallyEq_of_mem (Y.open_source.mem_nhds hq.2.1)
    exact (hf x).localInverse_eqOn_right
  have hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ) ∞
      (fun q : ℝ × N => chartGramMatrix (I := J) (h q.1) x₀ q.2 i j) (A ×ˢ V) := by
    intro q hq
    have hs := happ q hq
    rw [Bundle.contMDiffWithinAt_totalSpace] at hs
    exact hs.2.congr (heq) (heq q hq)
  apply (hscalar p ⟨hp.1, hpV⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds ((continuous_snd.tendsto p).eventually
      (hVopen.mem_nhds hpV))] with q hq hqV
  exact ⟨hq.1, hqV⟩

omit [T2Space N] in
theorem metricCLMSection_jointContMDiffOn_of_surjective_localPullMetric
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ univ))
    (h : ℝ → SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (hpull : ∀ t ∈ A, localPullMetric (h t) f hf = g t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y => TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)))
      (A ×ˢ univ) :=
  metricCLMSection_jointContMDiffOn_of_chartGram_on h A
    (chartGramMatrix_joint_contMDiffOn_of_surjective_localPullMetric g A hg h f hf hsurj hpull)

end DifferentialGeometry.Geometry.Curvature
