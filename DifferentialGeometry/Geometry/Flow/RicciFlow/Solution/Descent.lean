import DifferentialGeometry.Geometry.Metric.Family.Descent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocalCross
import DifferentialGeometry.Geometry.Metric.Quotient

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

theorem hasDerivWithinAt_ricciFlow_of_surjective_localPullMetric_of_eventuallyEq
    (k : ℝ → SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    {A : Set ℝ} {t : ℝ}
    (hpull : ∀ᶠ s in nhdsWithin t A, localPullMetric (g s) f hf = k s)
    (hpullt : localPullMetric (g t) f hf = k t)
    (hk : ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (k s).inner x v w) (-2 * ricciTensor (k t) x v w) A t)
    (y : N) (v w : TangentSpace J y) :
    HasDerivWithinAt (fun s => (g s).inner y v w)
      (-2 * ricciTensor (g t) y v w) A t := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨x, rfl⟩ := hsurj y
  let L := hf.mfderivToContinuousLinearEquiv (by simp) x
  have hL : (L : TangentSpace I x →L[ℝ] TangentSpace J (f x)) = mfderiv I J f x :=
    hf.mfderivToContinuousLinearEquiv_coe (by simp) x
  have hLv : mfderiv I J f x (L.symm v) = v := by rw [← hL]; exact L.apply_symm_apply v
  have hLw : mfderiv I J f x (L.symm w) = w := by rw [← hL]; exact L.apply_symm_apply w
  have heq (s : ℝ) (hs : localPullMetric (g s) f hf = k s) :
      (g s).inner (f x) v w = (k s).inner x (L.symm v) (L.symm w) := by
    rw [← hs, localPullMetric_inner, hLv, hLw]
  have hric : ricciTensor (g t) (f x) v w =
      ricciTensor (k t) x (L.symm v) (L.symm w) := by
    rw [← hpullt, ricciTensor_localPull, hLv, hLw]
  rw [hric]
  apply (hk x (L.symm v) (L.symm w)).congr_of_eventuallyEq
  · filter_upwards [hpull] with s hs
    exact heq s hs
  · exact heq t hpullt


theorem hasDerivWithinAt_ricciFlow_of_surjective_localPullMetric
    (k : ℝ → SmoothRiemannianMetric I M) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    {A : Set ℝ} {t : ℝ} (ht : t ∈ A)
    (hpull : ∀ s ∈ A, localPullMetric (g s) f hf = k s)
    (hk : ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (k s).inner x v w) (-2 * ricciTensor (k t) x v w) A t)
    (y : N) (v w : TangentSpace J y) :
    HasDerivWithinAt (fun s => (g s).inner y v w)
      (-2 * ricciTensor (g t) y v w) A t := by
  exact hasDerivWithinAt_ricciFlow_of_surjective_localPullMetric_of_eventuallyEq k f hf hsurj g
    (Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => hpull s hs)) (hpull t ht) hk y v w

theorem metric_hasDerivWithinAt_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    {A : Set ℝ} {t : ℝ} (ht : t ∈ A) (htD : t ∈ D.regular)
    (hpull : ∀ s ∈ A, localPullMetric (g s) f hf = S.family.metric s)
    (y : N) (v w : TangentSpace J y) :
    HasDerivWithinAt (fun s => (g s).inner y v w)
      (-2 * ricciTensor (g t) y v w) A t := by
  apply hasDerivWithinAt_ricciFlow_of_surjective_localPullMetric S.family.metric f hf hsurj g ht hpull
  intro x u z
  simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor, SolutionOn.family_metric] using
    (metricDerivAt S hS ⟨t, htD⟩ x u z).hasDerivWithinAt (s := A)

private theorem isSolutionOn_of_joint_metric_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hD : UniqueDiffOn ℝ D.carrier)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod J) (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun p : ℝ × N => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
        (fun y => TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ)))
      (D.carrier ×ˢ univ))
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    IsSolutionOn ({ base := { metric := g } } : SolutionOn (I := J) (M := N) D) := by
  apply isSolutionOn_of_joint_metric D hD g hg
  intro t ht y v w
  exact metric_hasDerivWithinAt_of_surjective_localPullMetric S hS f hf hsurj g
    (D.regular_subset ht) ht hpull y v w

theorem isSolutionOn_of_surjective_localPullMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hsurj : Function.Surjective f)
    (g : ℝ → SmoothRiemannianMetric J N)
    (hD : UniqueDiffOn ℝ D.carrier)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ univ))
    (hpull : ∀ s ∈ D.carrier, localPullMetric (g s) f hf = S.family.metric s) :
    IsSolutionOn ({ base := { metric := g } } : SolutionOn (I := J) (M := N) D) :=
  isSolutionOn_of_joint_metric_of_surjective_localPullMetric S hS f hf hsurj g hD
    (metricCLMSection_jointContMDiffOn_of_surjective_localPullMetric
      S.family.metric D.carrier hg g f hf hsurj hpull) hpull

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N]

theorem isSolutionOn_descendedMetric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hsurj : Function.Surjective f)
    (hD : UniqueDiffOn ℝ D.carrier)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ univ))
    (hcompat : ∀ t, metricFiberCompatible (S.family.metric t) f hf) :
    IsSolutionOn ({ base := { metric := (fun t =>
      descendedMetric (S.family.metric t) f hf hsurj (hcompat t)) } } :
        SolutionOn (I := I) (M := N) D) :=
  isSolutionOn_of_surjective_localPullMetric S hS f hf hsurj _ hD hg
    (fun t _ => localPullMetric_descendedMetric (S.family.metric t) f hf hsurj (hcompat t))


theorem exists_isSolutionOn_of_metricFiberCompatible
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hsurj : Function.Surjective f)
    (hD : UniqueDiffOn ℝ D.carrier)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (D.carrier ×ˢ univ))
    (hcompat : ∀ t ∈ D.carrier, metricFiberCompatible (S.family.metric t) f hf) :
    ∃ T : SolutionOn (I := I) (M := N) D, IsSolutionOn T ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × N => (⟨p.2, (T.family.metric p.1).inner p.2⟩ :
          TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))
        (D.carrier ×ˢ univ) ∧
      ∀ t ∈ D.carrier, localPullMetric (T.family.metric t) f hf = S.family.metric t := by
  classical
  let h₀ := descendedMetric (S.family.metric D.initial) f hf hsurj
    (hcompat D.initial D.initial_mem)
  let g := fun t : ℝ => if ht : t ∈ D.carrier then
    descendedMetric (S.family.metric t) f hf hsurj (hcompat t ht) else h₀
  have hpull (t : ℝ) (ht : t ∈ D.carrier) :
      localPullMetric (g t) f hf = S.family.metric t := by
    simp only [g, dif_pos ht]
    exact localPullMetric_descendedMetric (S.family.metric t) f hf hsurj (hcompat t ht)
  refine ⟨{ base := { metric := g } }, ?_, ?_, hpull⟩
  · exact isSolutionOn_of_surjective_localPullMetric S hS f hf hsurj g hD hg hpull
  · exact metricCLMSection_jointContMDiffOn_of_surjective_localPullMetric
      S.family.metric D.carrier hg g f hf hsurj hpull

theorem exists_ricciFlow_of_metricFiberCompatible
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a b ×ˢ (Set.univ : Set M)))
    (hpde : ∀ t ∈ Ico a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : ℝ => (g s).inner x v w)
        (-2 * ricciTensor (g t) x v w) (Ici a) t)
    (h₀ : SmoothRiemannianMetric I N) (f : M → N)
    (hf : IsLocalDiffeomorph I I ∞ f) (hsurj : Function.Surjective f)
    (hinit : localPullMetric h₀ f hf = g a)
    (hcompat : ∀ t ∈ Ico a b, metricFiberCompatible (g t) f hf) :
    ∃ h : ℝ → SmoothRiemannianMetric I N,
      h a = h₀ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × N => (⟨p.2, (h p.1).inner p.2⟩ :
          TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
            (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
        (Ico a b ×ˢ (Set.univ : Set N)) ∧
      (∀ t ∈ Ico a b, ∀ x : N, ∀ v w : TangentSpace I x,
        HasDerivWithinAt (fun s : ℝ => (h s).inner x v w)
          (-2 * ricciTensor (h t) x v w) (Ici a) t) ∧
      ∀ t ∈ Ico a b, localPullMetric (h t) f hf = g t := by
  classical
  let h := fun t : ℝ => if ht : t ∈ Ico a b then
    descendedMetric (g t) f hf hsurj (hcompat t ht) else h₀
  have hpull (t : ℝ) (ht : t ∈ Ico a b) : localPullMetric (h t) f hf = g t := by
    simp only [h, dif_pos ht]
    exact localPullMetric_descendedMetric (g t) f hf hsurj (hcompat t ht)
  refine ⟨h, ?_, ?_, ?_, hpull⟩
  · exact localPullMetric_injective_of_surjective f hf hsurj
      ((hpull a ⟨le_rfl, hab⟩).trans hinit.symm)
  · exact metricCLMSection_jointContMDiffOn_of_surjective_localPullMetric
      g (Ico a b) hjoint h f hf hsurj hpull
  · intro t ht x v w
    apply hasDerivWithinAt_ricciFlow_of_surjective_localPullMetric_of_eventuallyEq
      g f hf hsurj h ?_ (hpull t ht) (hpde t ht) x v w
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hslt
    exact hpull s ⟨hs, hslt⟩

end DifferentialGeometry.PDE.RicciFlow
