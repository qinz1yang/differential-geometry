import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.ProductIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Descent
import DifferentialGeometry.Geometry.Metric.Family.Product
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Product
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private theorem Diffeomorph.pullbackMetricCross_conjugate_eq_iff
    (g : SmoothRiemannianMetric I M) (F : M ≃ₘ⟮I, J⟯ N) (Γ : N ≃ₘ⟮J, J⟯ N) :
    Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross g F.symm) Γ =
        Diffeomorph.pullbackMetricCross g F.symm ↔
      Diffeomorph.pullbackMetricCross g ((F.trans Γ).trans F.symm) = g := by
  rw [eq_comm, Diffeomorph.pullbackMetricCross_symm_eq_iff]
  change Diffeomorph.pullbackMetricCross
    (Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross g F.symm) Γ) F = g ↔ _
  rw [Diffeomorph.pullbackMetricCross_trans, Diffeomorph.pullbackMetricCross_trans]

end DifferentialGeometry

open Bundle Set
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [ConnectedSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ V G}
  {U : Type*} [TopologicalSpace U] [ChartedSpace G U] [IsManifold J ∞ U] [T2Space U]

private theorem ricci_flow_prod_real_conjugate_pullback_eq_of_initial_isometry
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U)
    (Γ : U ≃ₘ⟮J, J⟯ U)
    (hinit : Diffeomorph.pullbackMetricCross
        (Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) Γ =
      Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) :
    ∀ t ∈ Ico a b,
      Diffeomorph.pullbackMetricCross
        (Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm) Γ =
      Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm := by
  have hΨ := (Diffeomorph.pullbackMetricCross_conjugate_eq_iff
    ((g a).prod (euclideanMetric (E := ℝ))) F Γ).mp hinit
  have hpersist := ricci_flow_prod_real_pullback_eq_of_initial_isometry
    g hab hdim hscalar hjoint hpde ((F.trans Γ).trans F.symm) hΨ
  intro t ht
  exact (Diffeomorph.pullbackMetricCross_conjugate_eq_iff
    ((g t).prod (euclideanMetric (E := ℝ))) F Γ).mpr (hpersist t ht)


variable {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B]

private theorem metricFiberCompatible_prod_real_flow_of_initial_localPullMetric
    [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U)
    (h₀ : SmoothRiemannianMetric J B) (f : U → B)
    (hf : IsLocalDiffeomorph J J ∞ f) (hcover : IsCoveringMap f)
    (hinit : localPullMetric h₀ f hf =
      Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) :
    ∀ t ∈ Ico a b, metricFiberCompatible
      (Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm) f hf := by
  intro t ht
  apply metricFiberCompatible_of_coveringDeckGroup_invariant _ f hf hcover
  intro γ
  let Γ := coveringDeckGroupDiffeomorph hf γ
  have hcomp : f ∘ (Γ : U → U) = f := by
    funext z
    exact coveringDeckGroup_map γ z
  have hΓ : Diffeomorph.pullbackMetric
      (Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) Γ =
      Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm := by
    rw [← hinit]
    exact pullbackMetric_localPullMetric_of_comp_eq h₀ f hf Γ hcomp
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric] at hΓ ⊢
  exact ricci_flow_prod_real_conjugate_pullback_eq_of_initial_isometry
    g hab hdim hscalar hjoint hpde F Γ hΓ t ht

end

section

open DifferentialGeometry.Geometry.Connection (LeviCivita)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ V G}
  {U : Type*} [TopologicalSpace U] [ChartedSpace G U] [IsManifold J ∞ U] [T2Space U]

private theorem metricCLMSection_jointContMDiffOn_prod_real_pullback
    (g : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun p : ℝ × U => (⟨p.2,
        (Diffeomorph.pullbackMetricCross ((g p.1).prod (euclideanMetric (E := ℝ))) F.symm).inner p.2⟩ :
        TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
          (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set U)) := by
  have he : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) ∞
      (fun p : ℝ × ℝ => (⟨p.2, (euclideanMetric (E := ℝ)).inner p.2⟩ :
        TotalSpace (ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
          (fun x => TangentSpace 𝓘(ℝ, ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set ℝ)) :=
    ((euclideanMetric (E := ℝ)).contMDiff.comp contMDiff_snd).contMDiffOn
  have hp := metricCLMSection_jointContMDiffOn_prod g
    (fun _ => euclideanMetric (E := ℝ)) A hg he
  apply metricCLMSection_jointContMDiffOn_of_chartGram_on
    (fun t => Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm) A
  exact chartGramMatrix_joint_contMDiffOn_of_pullback
    (fun t => (g t).prod (euclideanMetric (E := ℝ))) A hp
    (fun t => Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm)
    F.symm F.symm.contMDiff
    (fun t _ x u v => Diffeomorph.pullbackMetricCross_inner
      ((g t).prod (euclideanMetric (E := ℝ))) F.symm x u v)

variable [I.Boundaryless] [BoundarylessManifold J U]

private theorem hasDerivWithinAt_ricciFlow_prod_real_pullback
    (g : ℝ → SmoothRiemannianMetric I M) {A : Set ℝ} {t : ℝ}
    (hg : ∀ x : M, ∀ u v : TangentSpace I x,
      HasDerivWithinAt (fun s => (g s).inner x u v)
        (-2 * ricciTensor (g t) x u v) A t)
    (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U)
    (x : U) (u v : TangentSpace J x) :
    HasDerivWithinAt
      (fun s => (Diffeomorph.pullbackMetricCross
        ((g s).prod (euclideanMetric (E := ℝ))) F.symm).inner x u v)
      (-2 * ricciTensor (Diffeomorph.pullbackMetricCross
        ((g t).prod (euclideanMetric (E := ℝ))) F.symm) x u v) A t := by
  have he : ∀ y : ℝ, ∀ u v : TangentSpace 𝓘(ℝ, ℝ) y,
      HasDerivWithinAt (fun _ : ℝ => (euclideanMetric (E := ℝ)).inner y u v)
        (-2 * ricciTensor (euclideanMetric (E := ℝ)) y u v) A t := by
    intro y u v
    have hric : ricciTensor (euclideanMetric (E := ℝ)) y u v = 0 := by
      rw [ricciTensor_apply]
      have hz : ricciEndo (euclideanMetric (E := ℝ)) y u v = 0 := by
        apply LinearMap.ext
        intro z
        exact riemannOp_eq_zero_of_finrank_le_one (LeviCivita (euclideanMetric (E := ℝ)))
          (by simp) y z u v
      rw [hz, map_zero]
    rw [hric, mul_zero]
    exact hasDerivWithinAt_const t A ((euclideanMetric (E := ℝ)).inner y u v)
  have hp := hasDerivWithinAt_ricciFlow_prod g (fun _ => euclideanMetric (E := ℝ)) hg he
    (F.symm x) (mfderiv J (I.prod 𝓘(ℝ, ℝ)) F.symm x u)
      (mfderiv J (I.prod 𝓘(ℝ, ℝ)) F.symm x v)
  simpa only [Diffeomorph.pullbackMetricCross_inner,
    DifferentialGeometry.CheegerGromovCompactness.ricciTensor_cross] using hp

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] [ConnectedSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ V G}
  {U : Type*} [TopologicalSpace U] [ChartedSpace G U] [IsManifold J ∞ U] [T2Space U]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B]

omit [ConnectedSpace M] in
theorem exists_ricciFlow_of_prod_real_initial_localPullMetric
    [SimplyConnectedSpace U]
    [J.Boundaryless] [T2Space B]
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (F : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U)
    (h₀ : SmoothRiemannianMetric J B) (f : U → B)
    (hf : IsLocalDiffeomorph J J ∞ f) (hcover : IsCoveringMap f)
    (hsurj : Function.Surjective f)
    (hinit : localPullMetric h₀ f hf =
      Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) :
    ∃ h : ℝ → SmoothRiemannianMetric J B,
      h a = h₀ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) ∞
        (fun p : ℝ × B => (⟨p.2, (h p.1).inner p.2⟩ :
          TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
            (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
        (Ico a b ×ˢ (Set.univ : Set B)) ∧
      (∀ t ∈ Ico a b, ∀ x : B, ∀ v w : TangentSpace J x,
        HasDerivWithinAt (fun s : ℝ => (h s).inner x v w)
          (-2 * ricciTensor (h t) x v w) (Ici a) t) ∧
      ∀ t ∈ Ico a b, localPullMetric (h t) f hf =
        Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm := by
  let _ : LocallyPathConnectedSpace G := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace U := ChartedSpace.locallyPathConnectedSpace G U
  have hsurjM : Function.Surjective (fun x : U => (F.symm x).1) := by
    intro y
    exact ⟨F (y, 0), by simp⟩
  let _ : ConnectedSpace M := hsurjM.connectedSpace
    (continuous_fst.comp F.symm.toHomeomorph.continuous)
  let _ : SigmaCompactSpace U := F.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  apply exists_ricciFlow_of_metricFiberCompatible
    (fun t => Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm)
    hab
    (metricCLMSection_jointContMDiffOn_prod_real_pullback g (Ico a b) hjoint F)
    (fun t ht => hasDerivWithinAt_ricciFlow_prod_real_pullback g (hpde t ht) F)
    h₀ f hf hsurj hinit
  exact metricFiberCompatible_prod_real_flow_of_initial_localPullMetric
    g hab hdim hscalar hjoint hpde F h₀ f hf hcover hinit
end

section CompactComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [CompactSpace N] [T2Space N] [ConnectedSpace N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ V G} [J.Boundaryless]
  {U : Type*} [TopologicalSpace U] [ChartedSpace G U] [IsManifold J ∞ U] [T2Space U]
  [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B] [IsManifold J ∞ B]
  [T2Space B] [CompactSpace B]

omit [ConnectedSpace N] [LocallyPathConnectedSpace U] in
theorem localPullMetric_eq_prod_real_of_initial_of_compact
    {D : RealTimeInterval} (S : SolutionOn (I := J) (M := B) D) (hS : IsSolutionOn S)
    (g : ℝ → SmoothRiemannianMetric I N) {a b : ℝ} (hab : a < b)
    (hreg : Ico a b ⊆ D.regular)
    (hdim : Module.finrank ℝ E = 2)
    (hscalar : ∀ x, metricScalarAt (g a) x ≠ 0)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set N)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : N, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (F : (N × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), J⟯ U)
    (f : U → B) (hf : IsLocalDiffeomorph J J ∞ f)
    (hcover : IsCoveringMap f) (hsurj : Function.Surjective f)
    (hinit : localPullMetric (S.family.metric a) f hf =
      Diffeomorph.pullbackMetricCross ((g a).prod (euclideanMetric (E := ℝ))) F.symm) :
    ∀ t ∈ Ico a b, localPullMetric (S.family.metric t) f hf =
      Diffeomorph.pullbackMetricCross ((g t).prod (euclideanMetric (E := ℝ))) F.symm := by
  obtain ⟨h, hinit', hjoint', hpde', hpull⟩ :=
    exists_ricciFlow_of_prod_real_initial_localPullMetric g hab hdim hscalar hjoint hpde
      F (S.family.metric a) f hf hcover hsurj hinit
  have hSjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) ∞
      (fun p : ℝ × B => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (V →L[ℝ] V →L[ℝ] ℝ)
          (fun x => TangentSpace J x →L[ℝ] TangentSpace J x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set B)) := by
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hreg hp.1))).contMDiffWithinAt
  have hSpde : ∀ t ∈ Ico a b, ∀ x : B, ∀ v w : TangentSpace J x,
      HasDerivWithinAt (fun s => (S.family.metric s).inner x v w)
        (-2 * ricciTensor (S.family.metric t) x v w) (Ici a) t := by
    intro t ht x v w
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
      (metricDerivAt S hS ⟨t, hreg ht⟩ x v w).hasDerivWithinAt (s := Ici a)
  have heq := ricci_flow_forward_unique_of_joint_contMDiffOn
    h S.family.metric hab hjoint' hSjoint hpde' hSpde hinit'
  intro t ht
  rw [← heq t ht]
  exact hpull t ht

end CompactComparison

end DifferentialGeometry.PDE.RicciFlow
