import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PositiveSystem
import DifferentialGeometry.Geometry.Connection.ParallelTransport.SubbundleInvariance

open Bundle CovariantDerivative Set
open scoped Manifold ContDiff Topology InnerProductSpace

private theorem exists_Ioo_mem_subset_of_isOpen_ordConnected
    {J : Set ℝ} (hopen : IsOpen J) (hJ : J.OrdConnected)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    ∃ a b, s ∈ Ioo a b ∧ t ∈ Ioo a b ∧ Ioo a b ⊆ J := by
  have hmin : min s t ∈ J := by
    rcases le_total s t with h | h
    · simpa only [min_eq_left h] using hs
    · simpa only [min_eq_right h] using ht
  have hmax : max s t ∈ J := by
    rcases le_total s t with h | h
    · simpa only [max_eq_right h] using ht
    · simpa only [max_eq_left h] using hs
  obtain ⟨δ, hδ, hδJ⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmin)
  obtain ⟨ε, hε, hεJ⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmax)
  let a := min s t - δ / 2
  let b := max s t + ε / 2
  have ha : a ∈ J := hδJ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos]
    · dsimp only [a]; linarith
    · dsimp only [a]; linarith)
  have hb : b ∈ J := hεJ (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg]
    · dsimp only [b]; linarith
    · dsimp only [b]; linarith)
  refine ⟨a, b, ⟨?_, ?_⟩, ⟨?_, ?_⟩, Ioo_subset_Icc_self.trans (hJ.out ha hb)⟩
  all_goals dsimp only [a, b]; linarith [min_le_left s t, min_le_right s t,
    le_max_left s t, le_max_right s t]

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem kernel_rigidity_on_open_interval
    {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    (hcovsmooth : ∀ t ∈ J, ContMDiffCovariantDerivative (cov t) ∞)
    (hcov : ∀ t ∈ J, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hJopen : IsOpen J) (hJ : J.OrdConnected)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ J, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t ∈ J, ∀ x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hevolution : ∀ t ∈ J, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t) :
    let k := Module.finrank ℝ F - q
    (∀ p ∈ J ×ˢ (Set.univ : Set M),
      ∃ (U : Set (ℝ × M)) (w : Fin k → (p : ℝ × M) → V p.2),
        IsOpen U ∧ p ∈ U ∧ U ⊆ J ×ˢ (Set.univ : Set M) ∧
        (∀ z ∈ U, LinearIndependent ℝ (w · z)) ∧
        (∀ z ∈ U,
          Submodule.span ℝ (Set.range (w · z)) = (A z.1 z.2).ker) ∧
        ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I)
          ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
          (fun z ↦ TotalSpace.mk' F z (w i z) : ℝ × M →
            TotalSpace F ((ContMDiffMap.snd :
              C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U) ∧
      (∀ t ∈ J,
        IsCovariantlyInvariantSubmoduleFamily (cov t)
          (fun x ↦ (A t x).ker)) ∧
      (∀ t ∈ J, ∀ x v, A t x v = 0 →
        inner ℝ (reaction t x (A t x) v) v = 0) ∧
      (∀ t ∈ J, ∀ x v, A t x v = 0 →
        deriv (fun s ↦ A s x) t v = reaction t x (A t x) v) ∧
      ∀ t ∈ J,
        ∀ (w : (p : ℝ × M) → V p.2) {U : Set (ℝ × M)},
          IsOpen U → ∀ {x}, (t, x) ∈ U →
          ContMDiffOn (𝓘(ℝ, ℝ).prod I)
            ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
            (fun p ↦ TotalSpace.mk' F p (w p) : ℝ × M →
              TotalSpace F ((ContMDiffMap.snd :
                C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯) *ᵖ V)) U →
          (∀ p ∈ U, A p.1 p.2 (w p) = 0) →
          A t x (deriv (fun s ↦ w (s, x)) t) =
              -reaction t x (A t x) (w (t, x)) ∧
            deriv (fun s ↦ A s x) t (w (t, x)) =
              reaction t x (A t x) (w (t, x)) := by
  classical
  by_cases hJempty : J = ∅
  · subst J
    simp
  obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.mpr hJempty
  let cov' : ℝ → CovariantDerivative I F V :=
    fun t => if t ∈ J then cov t else cov t₀
  let _ : ∀ t, ContMDiffCovariantDerivative (cov' t) ∞ := by
    intro t
    dsimp only [cov']
    split_ifs with ht
    · exact hcovsmooth t ht
    · exact hcovsmooth t₀ ht₀
  have hcov' : ∀ t, (cov' t).IsMetricCompatible := by
    intro t
    dsimp only [cov']
    split_ifs with ht
    · exact hcov t ht
    · exact hcov t₀ ht₀
  have heq : ∀ t ∈ J, cov' t = cov t := fun t ht => ite_eq_left ht
  have hAspace := contMDiffOnSpacetimeEndomorphism_of_contMDiffOn_hom_bundle
    (I := I) (F := F) (V := V) (n := ∞) (A := fun t x => A t x) hA
  have hAsymm : ∀ t ∈ J, ∀ x,
      ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric :=
    fun t ht x => (hApos t ht x).isSymmetric
  let reaction' : ℝ → (x : M) → (V x →L[ℝ] V x) → V x →L[ℝ] V x :=
    fun t x => if t ∈ J then reaction t x else fun _ => 0
  have hnull : ∀ t x, satisfiesNullEigenvectorCondition (reaction' t x) := by
    intro t x
    by_cases ht : t ∈ J
    · simpa only [reaction', ite_eq_left ht] using hreactionNull t ht x
    · intro B hB v hv
      simp only [reaction', ite_eq_right ht, zero_apply, inner_zero_left, le_refl]
  have hevol : ∀ t ∈ J, ∀ x,
      deriv (fun s ↦ A s x) t =
        rawBundleEndomorphismConnLap (I := I) (g t) (cov' t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov' t) (cov' t) (fun y ↦ A t y) x (X t x) +
          reaction' t x (A t x) := by
    intro t ht x
    simpa only [reaction', ite_eq_left ht, heq t ht] using (hevolution t ht x).deriv
  have hrig (a b : ℝ) (hsub : Ioo a b ⊆ J) :=
    kernel_rigidity_of_constant_range_rank g cov' hcov' A
      (hAspace.mono (Set.prod_mono hsub Set.Subset.rfl)) q
      (fun u hu => hrange u (hsub hu)) (fun u hu => hAsymm u (hsub hu))
      (fun u hu => hApos u (hsub hu)) X reaction' hnull
      (fun u hu x => (hevolution u (hsub hu) x).differentiableAt) (fun u hu => hevol u (hsub hu))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, b, ht, _, hsub⟩ :=
      exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ hp.1 hp.1
    obtain ⟨U, w, hU, hpU, hUW, hw⟩  := (hrig a b hsub).1 p ⟨ht, hp.2⟩
    exact ⟨U, w, hU, hpU, hUW.trans (Set.prod_mono hsub Set.Subset.rfl), hw⟩
  · intro t ht
    obtain ⟨a, b, hat, _, hsub⟩ :=
      exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ ht ht
    simpa only [heq t ht] using (hrig a b hsub).2.1 t hat
  · intro t ht
    obtain ⟨a, b, hat, _, hsub⟩ :=
      exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ ht ht
    simpa only [reaction', ite_eq_left ht] using (hrig a b hsub).2.2.1 t hat
  · intro t ht
    obtain ⟨a, b, hat, _, hsub⟩ :=
      exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ ht ht
    simpa only [reaction', ite_eq_left ht] using (hrig a b hsub).2.2.2.1 t hat
  · intro t ht
    obtain ⟨a, b, hat, _, hsub⟩ :=
      exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ ht ht
    simpa only [reaction', ite_eq_left ht] using (hrig a b hsub).2.2.2.2 t hat

theorem exists_smooth_parallel_kernel_on_open_interval
    {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    (hcovsmooth : ∀ t ∈ J, ContMDiffCovariantDerivative (cov t) ∞)
    (hcov : ∀ t ∈ J, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hJopen : IsOpen J) (hJ : J.OrdConnected)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ J, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t ∈ J, ∀ x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hevolution : ∀ t ∈ J, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t) :
    ∀ t ∈ J, ∃ K : ContMDiffVectorSubbundle (I := I) (F := F) (V := V) (n := ∞),
      K.rank = Module.finrank ℝ F - q ∧
      (∀ x, K.fiber x = (A t x).ker) ∧
      (∀ x, (K.fiber x)ᗮ = (A t x).range) ∧
      IsCovariantlyInvariantSubmoduleFamily (cov t) K.fiber ∧
      (cov t).IsParallelSet {p : TotalSpace F V | p.2 ∈ K.fiber p.1} := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hrig := kernel_rigidity_on_open_interval g cov hcovsmooth hcov A hJopen hJ
    hA q hrange hApos X reaction hreactionNull hevolution
  intro t ht
  let _ := hcovsmooth t ht
  have hker (x : M) : Module.finrank ℝ (A t x).ker = Module.finrank ℝ F - q := by
    have hd := VectorBundle.finrank_eq ℝ F V x
    have hr := hrange t ht x
    have hsum := (A t x).toLinearMap.finrank_range_add_finrank_ker
    omega
  obtain ⟨K, hKrank, hK⟩ := ContMDiffVectorSubbundle.exists_smooth_kernel
    (fun x => A t x) (A t).contMDiff (Module.finrank ℝ F - q) hker
  have hparallel : IsCovariantlyInvariantSubmoduleFamily (cov t) K.fiber := by
    have heq : K.fiber = fun x => (A t x).ker := funext hK
    rw [heq]
    exact hrig.2.1 t ht
  refine ⟨K, hKrank, hK, ?_, hparallel,
    K.isParallelSet_of_covariantly_invariant (cov t) hparallel inferInstance⟩
  intro x
  rw [hK x, ← (hApos t ht x).isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]

theorem kernel_time_constant_on_open_interval
    {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    (hcovsmooth : ∀ t ∈ J, ContMDiffCovariantDerivative (cov t) ∞)
    (hcov : ∀ t ∈ J, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hJopen : IsOpen J) (hJ : J.OrdConnected)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ J, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t ∈ J, ∀ x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hreactionAnn : ∀ t ∈ J, ∀ x v, A t x v = 0 →
      reaction t x (A t x) v = 0)
    (hevolution : ∀ t ∈ J, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t)
    {x : M} {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (A s x).ker = (A t x).ker ∧ (A s x).range = (A t x).range := by
  classical
  let t₀ := s
  have ht₀ : t₀ ∈ J := hs
  let cov' : ℝ → CovariantDerivative I F V :=
    fun t => if t ∈ J then cov t else cov t₀
  let _ : ∀ t, ContMDiffCovariantDerivative (cov' t) ∞ := by
    intro t
    dsimp only [cov']
    split_ifs with ht
    · exact hcovsmooth t ht
    · exact hcovsmooth t₀ ht₀
  have hcov' : ∀ t, (cov' t).IsMetricCompatible := by
    intro t
    dsimp only [cov']
    split_ifs with ht
    · exact hcov t ht
    · exact hcov t₀ ht₀
  have heq : ∀ t ∈ J, cov' t = cov t := fun t ht => ite_eq_left ht
  have hAspace := contMDiffOnSpacetimeEndomorphism_of_contMDiffOn_hom_bundle
    (I := I) (F := F) (V := V) (n := ∞) (A := fun t x => A t x) hA
  have hAsymm : ∀ t ∈ J, ∀ x,
      ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric :=
    fun t ht x => (hApos t ht x).isSymmetric
  let reaction' : ℝ → (x : M) → (V x →L[ℝ] V x) → V x →L[ℝ] V x :=
    fun t x => if t ∈ J then reaction t x else fun _ => 0
  have hnull : ∀ t x, satisfiesNullEigenvectorCondition (reaction' t x) := by
    intro t x
    by_cases ht : t ∈ J
    · simpa only [reaction', ite_eq_left ht] using hreactionNull t ht x
    · intro B hB v hv
      simp only [reaction', ite_eq_right ht, zero_apply, inner_zero_left, le_refl]
  have hevol : ∀ t ∈ J, ∀ x,
      deriv (fun s ↦ A s x) t =
        rawBundleEndomorphismConnLap (I := I) (g t) (cov' t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov' t) (cov' t) (fun y ↦ A t y) x (X t x) +
          reaction' t x (A t x) := by
    intro t ht x
    simpa only [reaction', ite_eq_left ht, heq t ht] using (hevolution t ht x).deriv
  have hA_time (y : M) : ContDiffOn ℝ 1 (fun t ↦ A t y) J := by
    let _ : FiniteDimensional ℝ (V y) := VectorBundle.finiteDimensional ℝ F V y
    let c : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; I, M⟯ := ContMDiffMap.snd
    let _ : TopologicalSpace (TotalSpace F (fun p : ℝ × M => V p.2)) := by
      change TopologicalSpace (TotalSpace F (c *ᵖ V)); infer_instance
    let _ : FiberBundle F (fun p : ℝ × M => V p.2) := by
      change FiberBundle F (c *ᵖ V); infer_instance
    let _ : VectorBundle ℝ F (fun p : ℝ × M => V p.2) := by
      change VectorBundle ℝ F (c *ᵖ V); infer_instance
    let _ : ContMDiffVectorBundle ∞ F (fun p : ℝ × M => V p.2)
        (𝓘(ℝ, ℝ).prod I) := by
      change ContMDiffVectorBundle ∞ F (c *ᵖ V) (𝓘(ℝ, ℝ).prod I); infer_instance
    apply contDiffOn_clm_apply.mpr
    intro v
    obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at
      (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) y v
    have hwsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' F p (w p.2) :
          ℝ × M → TotalSpace F (c *ᵖ V)) (J ×ˢ (Set.univ : Set M)) := by
      intro p hp
      let e₀ := trivializationAt F V p.2
      let e := e₀.pullback c
      let _ : MemTrivializationAtlas e := ⟨⟨e₀, inferInstance, rfl⟩⟩
      have hpe : p ∈ e.baseSet := mem_baseSet_trivializationAt F V p.2
      apply (e.contMDiffWithinAt_section _ hpe).mpr
      have hwcoord := (e₀.contMDiffAt_section_iff
        (mem_baseSet_trivializationAt F V p.2)).mp (w.contMDiff p.2)
      convert (hwcoord.comp p contMDiffAt_snd).contMDiffWithinAt using 1
      funext y
      rfl
    have hAsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
        ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p (A p.1 p.2))
        (J ×ˢ (Set.univ : Set M)) := hAspace
    have happ := hAsmooth.clm_bundle_apply hwsmooth
    have htime := contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section
      (I := I) (F := F) (V := V)
      (w := fun p => A p.1 p.2 (w p.2))
      (hJopen.prod isOpen_univ) happ
      (x := y) (fun t (ht : t ∈ J) => ⟨ht, mem_univ y⟩)
    simpa only [hw] using htime.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨a, b, has, hbt, hsub⟩ :=
    exists_Ioo_mem_subset_of_isOpen_ordConnected hJopen hJ hs ht
  exact kernel_time_constant_of_constant_range_rank g cov' hcov' A
    (hAspace.mono (Set.prod_mono hsub Set.Subset.rfl))
    (fun y => (hA_time y).mono hsub) q (fun u hu => hrange u (hsub hu))
    (fun u hu => hAsymm u (hsub hu)) (fun u hu => hApos u (hsub hu))
    X reaction' hnull (fun u hu x v hv => by
      simpa only [reaction', ite_eq_left (hsub hu)] using hreactionAnn u (hsub hu) x v hv)
    (fun u hu x => (hevolution u (hsub hu) x).differentiableAt) (fun u hu => hevol u (hsub hu)) has hbt

end PositiveSystem

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u₁ v₁

variable {E : Type u₁} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type v₁} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
theorem reaction_kernel_annihilation_of_isPositive_on_open_interval
    {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    (hcovsmooth : ∀ t ∈ J, ContMDiffCovariantDerivative (cov t) ∞)
    (hcov : ∀ t ∈ J, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hJopen : IsOpen J) (hJ : J.OrdConnected)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ J, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t ∈ J, ∀ x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hreactionPos : ∀ t ∈ J, ∀ x,
      (reaction t x (A t x)).IsPositive)
    (hevolution : ∀ t ∈ J, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t) :
    ∀ t ∈ J, ∀ x v, A t x v = 0 → reaction t x (A t x) v = 0 := by
  have hrig := kernel_rigidity_on_open_interval g cov hcovsmooth hcov A hJopen hJ hA q hrange
    hApos X reaction hreactionNull hevolution
  intro t ht x v hv
  apply continuousLinearMap_kernel_annihilation_of_isPositive
    (A := A t x) (B := reaction t x (A t x)) (hreactionPos t ht x)
  · intro w hw
    exact hrig.2.2.1 t ht x w (LinearMap.mem_ker.mp hw)
  · exact LinearMap.mem_ker.mpr hv

theorem reaction_kernel_annihilation_of_commuting_on_open_interval
    {J : Set ℝ}
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    (hcovsmooth : ∀ t ∈ J, ContMDiffCovariantDerivative (cov t) ∞)
    (hcov : ∀ t ∈ J, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hJopen : IsOpen J) (hJ : J.OrdConnected)
    (hA : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (J ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ J, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (reaction : ℝ → (x : M) →
      (V x →L[ℝ] V x) → V x →L[ℝ] V x)
    (hreactionNull : ∀ t ∈ J, ∀ x,
      satisfiesNullEigenvectorCondition (reaction t x))
    (hreactionSymm : ∀ t ∈ J, ∀ x,
      ((reaction t x (A t x) : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).IsSymmetric)
    (hreactionComm : ∀ t ∈ J, ∀ x,
      ((reaction t x (A t x) : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).comp
          ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x) =
        ((A t x : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x).comp
          ((reaction t x (A t x) : V x →L[ℝ] V x) : V x →ₗ[ℝ] V x))
    (hevolution : ∀ t ∈ J, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          reaction t x (A t x)) t) :
    ∀ t ∈ J, ∀ x v, A t x v = 0 → reaction t x (A t x) v = 0 := by
  have hrig := kernel_rigidity_on_open_interval g cov hcovsmooth hcov A hJopen hJ hA q hrange
    hApos X reaction hreactionNull hevolution
  intro t ht x v hv
  apply linearMap_kernel_annihilation_of_commuting
    (A := (A t x : V x →L[ℝ] V x).toLinearMap)
    (B := (reaction t x (A t x) : V x →L[ℝ] V x).toLinearMap)
    (hreactionSymm t ht x) (hreactionComm t ht x)
  · intro w hw
    exact hrig.2.2.1 t ht x w (LinearMap.mem_ker.mp hw)
  · exact LinearMap.mem_ker.mpr hv

end PositiveSystem
