import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.PositiveSystem
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionRegularity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureReactionPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity
import DifferentialGeometry.Bundle.HomNorm
import DifferentialGeometry.Geometry.Metric.BundleContinuity
import DifferentialGeometry.Analysis.Spectral.BundleLowerKyFan

set_option autoImplicit false

noncomputable section

open Bundle Set CovariantDerivative
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator

private theorem reaction_null
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] :
    PositiveSystem.satisfiesNullEigenvectorCondition
      (fun A : V →L[ℝ] V =>
        (curvatureOperatorReactionEndomorphism3 A.toLinearMap).toContinuousLinearMap) := by
  intro A hA v _
  exact (curvatureOperatorReactionEndomorphism3_isPositive hA.toLinearMap).inner_nonneg_left v

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

local notation "Q" => fun (x : M) (B : V x →L[ℝ] V x) =>
  (@LinearMap.toContinuousLinearMap ℝ _ (V x) _ _ _ _ _ (V x) _ _ _ _ _ _ _
    (VectorBundle.finiteDimensional ℝ F V x))
    (@curvatureOperatorReactionEndomorphism3 (V x) _ _
      (VectorBundle.finiteDimensional ℝ F V x) (ContinuousLinearMap.toLinearMap B))

omit [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem spacetime_endomorphism_contDiffOn_time
    {a b : ℝ}
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hA : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (x : M) : ContDiffOn ℝ 1 (fun t ↦ A t x) (Ioo a b) := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
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
    (I := I) (F := F) (V := V) (n := (⊤ : ℕ∞)) x v
  have hwsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' F p (w p.2) :
        ℝ × M → TotalSpace F (c *ᵖ V)) (Ioo a b ×ˢ (Set.univ : Set M)) := by
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
      (Ioo a b ×ˢ (Set.univ : Set M)) := hA
  have happ := hAsmooth.clm_bundle_apply hwsmooth
  have htime := contDiffOn_fixed_spatial_of_contMDiffOn_pullback_section
    (I := I) (F := F) (V := V)
    (w := fun p => A p.1 p.2 (w p.2))
    (isOpen_Ioo.prod isOpen_univ) happ
    (x := x) (fun t (ht : t ∈ Ioo a b) => ⟨ht, mem_univ x⟩)
  simpa only [hw] using htime.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)

theorem curvatureOperator_kernel_parallel_and_reaction_annihilated_of_constant_rank
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    {a b : ℝ}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t) :
    (∀ t ∈ Ioo a b,
      IsCovariantlyInvariantSubmoduleFamily (cov t)
        (fun x ↦ (A t x).ker)) ∧
      (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
        Q x (A t x) v = 0) ∧
      (∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
        deriv (fun s ↦ A s x) t v = 0) := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hrigidity := PositiveSystem.kernel_rigidity_of_constant_range_rank
    g cov hcov A hAspace q hrange (fun t ht x => (hApos t ht x).toLinearMap.isSymmetric)
    hApos X (fun _ _ B =>
      (curvatureOperatorReactionEndomorphism3 B.toLinearMap).toContinuousLinearMap)
    (fun _ _ => reaction_null) (fun t ht x => (hevolution t ht x).differentiableAt)
    (fun t ht x => (hevolution t ht x).deriv)
  have hann : ∀ t ∈ Ioo a b, ∀ x v, A t x v = 0 →
      Q x (A t x) v = 0 := by
    intro t ht x v hv
    exact ((curvatureOperatorReactionEndomorphism3_isPositive
      (hApos t ht x).toLinearMap).inner_apply_self_eq_zero_iff v).mp
        (hrigidity.2.2.1 t ht x v hv)
  refine ⟨hrigidity.2.1, hann, ?_⟩
  intro t ht x v hv
  exact (hrigidity.2.2.2.1 t ht x v hv).trans (hann t ht x v hv)


theorem curvatureOperator_kernel_and_range_eq_of_constant_rank
    (g : ℝ → SmoothRiemannianMetric I M)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    {a b : ℝ}
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo a b ×ˢ (Set.univ : Set M)))
    (q : ℕ) (hrange : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (A t x).range = q)
    (hApos : ∀ t ∈ Ioo a b, ∀ x, (A t x).IsPositive)
    (X : ℝ → (x : M) → TangentSpace I x)
    (hevolution : ∀ t ∈ Ioo a b, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (g t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t)
    {x : M} {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    (A s x).ker = (A t x).ker ∧ (A s x).range = (A t x).range := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hrigidity := curvatureOperator_kernel_parallel_and_reaction_annihilated_of_constant_rank
    g cov hcov A hAspace q hrange hApos X hevolution
  exact PositiveSystem.kernel_time_constant_of_constant_range_rank
    g cov hcov A hAspace (spacetime_endomorphism_contDiffOn_time A hAspace) q hrange
    (fun t ht x => (hApos t ht x).toLinearMap.isSymmetric) hApos X
    (fun _ _ B => (curvatureOperatorReactionEndomorphism3 B.toLinearMap).toContinuousLinearMap)
    (fun _ _ => reaction_null) hrigidity.2.1
    (fun t ht x => (hevolution t ht x).differentiableAt)
    (fun t ht x => (hevolution t ht x).deriv) hs ht


theorem curvatureOperator_finrank_range_le_at_later_time
    [I.Boundaryless] [ConnectedSpace M]
    [NeZero (Module.finrank ℝ E)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hAsymm : ∀ t x, (A t x).IsSymmetric)
    (hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (x : M) → TangentSpace I x)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ t ∈ Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (hevolution : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  have hbound : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {K : Set M}, IsCompact K →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ K, ‖A q z‖ ≤ R := by
    intro s t hs hst ht K hK
    obtain ⟨R, -, hR⟩ := (isCompact_Icc.prod hK).exists_hom_bundle_opNorm_bound
      (hAcont.mono fun p hp => ⟨⟨hs.trans hp.1.1, hp.1.2.trans ht⟩, mem_univ p.2⟩)
    exact ⟨R, fun q hq z hz => hR (q, z) ⟨hq, hz⟩⟩
  have hdim : ∀ x, Module.finrank ℝ (V x) = Module.finrank ℝ F :=
    fun x => VectorBundle.finrank_eq ℝ F V x
  have hlip (R : ℝ) := curvatureOperatorReactionEndomorphism3_exists_uniform_lipschitzOn_closedBall
    V (Module.finrank ℝ F) hdim (2 * R)
  apply PositiveSystem.finrank_range_le_at_later_time_of_metricFamilySmoothOn
    G cov hcov hT A hAsymm hApos
    (fun k hk => hAcont.lowerKyFanSum_bundle (fun p => hAsymm p.1 p.2) hk)
    hbound X (fun _ _ B =>
      (curvatureOperatorReactionEndomorphism3 B.toLinearMap).toContinuousLinearMap)
    (fun _ _ => reaction_null) ?_ hG hreg hX hGconn
    (fun t ht x => (hevolution t ht x).differentiableAt)
    (fun t ht x => (hevolution t ht x).deriv) hs hst ht x y
  intro s t hs hst ht K hK R
  obtain ⟨L, hL⟩ := hlip R
  refine ⟨L, fun q hq z hz => (hL z).mono ?_⟩
  intro B hB
  exact mem_closedBall_zero_iff.mpr hB.2


theorem curvatureOperator_rank_spatially_constant_and_locally_constant_from_left
    [I.Boundaryless] [ConnectedSpace M]
    [NeZero (Module.finrank ℝ E)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hAsymm : ∀ t x, (A t x).IsSymmetric)
    (hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (x : M) → TangentSpace I x)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ t ∈ Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (hevolution : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range = Module.finrank ℝ (A t y).range) ∧
      (∀ x, MonotoneOn (fun t ↦ Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).range = Module.finrank ℝ (A t x).range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    (rank := fun t x => Module.finrank ℝ (A t x).range) hT
  · intro t ht x
    exact (hevolution t ht x).differentiableAt.continuousAt.eventually_finrank_range_ge
      |>.filter_mono inf_le_left
  · intro s t hs hst ht x y
    exact curvatureOperator_finrank_range_le_at_later_time G cov hcov hT A hAsymm hApos
      hAcont X hG hreg hX hGconn hevolution hs hst ht x y


theorem curvatureOperator_reaction_annihilates_kernel_at_positive_time
    [I.Boundaryless] [ConnectedSpace M]
    [NeZero (Module.finrank ℝ E)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hAsymm : ∀ t x, (A t x).IsSymmetric)
    (hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (x : M) → TangentSpace I x)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ t ∈ Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (hevolution : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) (v : V x) (hv : A t x v = 0) :
    Q x (A t x) v = 0 := by
  let _ : ∀ x, FiniteDimensional ℝ (V x) :=
    fun x => VectorBundle.finiteDimensional ℝ F V x
  have hrank := curvatureOperator_rank_spatially_constant_and_locally_constant_from_left
    G cov hcov hT A hAsymm hApos hAcont X hG hreg hX hGconn hevolution
  obtain ⟨ε, hε, hrankε⟩ := hrank.2.2.1 t ht x
  have hεsub : Ioo (t - ε) t ⊆ Ioo 0 T := by
    intro s hs
    exact ⟨by linarith [hε.2, hs.1], hs.2.trans_le ht.2⟩
  have hεT : Ioo (t - ε) t ⊆ Ioc 0 T :=
    fun _ hs => ⟨(hεsub hs).1, (hεsub hs).2.le⟩
  have hspace := hAspace.mono (Set.prod_mono hεsub Set.Subset.rfl)
  let q := Module.finrank ℝ (A t x).range
  have hrange : ∀ s ∈ Ioo (t - ε) t, ∀ y,
      Module.finrank ℝ (A s y).range = q := by
    intro s hs y
    exact (hrank.1 s (hεT hs) y x).trans (hrankε s ⟨hs.1, hs.2.le⟩)
  have hpos : ∀ s ∈ Ioo (t - ε) t, ∀ y, (A s y).IsPositive :=
    fun s hs y => hApos s ⟨(hεT hs).1.le, (hεT hs).2⟩ y
  have hevol := fun s (hs : s ∈ Ioo (t - ε) t) y => hevolution s (hεT hs) y
  have hrigidity := curvatureOperator_kernel_parallel_and_reaction_annihilated_of_constant_rank
    G.metric cov hcov A hspace q hrange hpos X hevol
  let r := t - ε / 2
  have hr : r ∈ Ioo (t - ε) t := by
    dsimp only [r]
    constructor <;> linarith [hε.1]
  let K := (A r x).ker
  have hK : ∀ s ∈ Ioo (t - ε) t, (A s x).ker = K := by
    intro s hs
    exact (curvatureOperator_kernel_and_range_eq_of_constant_rank
      G.metric cov hcov A hspace q hrange hpos X hevol hs hr).1
  have hfin : Module.finrank ℝ K = Module.finrank ℝ (A t x).ker := by
    have hsumr := (A r x).toLinearMap.finrank_range_add_finrank_ker
    have hsumt := (A t x).toLinearMap.finrank_range_add_finrank_ker
    have hrankr := hrankε r ⟨hr.1, hr.2.le⟩
    dsimp only [K]
    omega
  have hcont := (hevolution t ht x).differentiableAt.continuousAt
  have hQcont : ContinuousAt (fun s => Q x (A s x)) t :=
    curvatureOperatorReactionEndomorphism3_contDiff.continuous.continuousAt.comp hcont
  exact continuousLinearMap_kernel_annihilation_of_constant_on_left
    (show t - ε < t by linarith [hε.1]) hcont hQcont hK hfin
    (fun s hs w hw => hrigidity.2.1 s hs x w (LinearMap.mem_ker.mp hw)) v
    (LinearMap.mem_ker.mpr hv)


theorem curvatureOperator_finrank_range_trichotomy_at_positive_time
    [I.Boundaryless] [ConnectedSpace M]
    [NeZero (Module.finrank ℝ E)]
    (hF : Module.finrank ℝ F = 3)
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ t, ContMDiffCovariantDerivative (cov t) ∞]
    (hcov : ∀ t, (cov t).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun x : M ↦ V x →L[ℝ] V x)⟯)
    (hAsymm : ∀ t x, (A t x).IsSymmetric)
    (hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hAspace : ContMDiffOnSpacetimeEndomorphism
      (I := I) (F := F) (V := V) (n := ∞)
      (fun t x ↦ A t x) (Ioo 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (x : M) → TangentSpace I x)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconn : ∀ t ∈ Icc 0 T,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (hevolution : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivAt (fun s ↦ A s x)
        (rawBundleEndomorphismConnLap (I := I) (G.metric t) (cov t)
            (fun y ↦ A t y) x +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov t) (cov t) (fun y ↦ A t y) x (X t x) +
          Q x (A t x)) t)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : M) :
    Module.finrank ℝ (A t x).range = 0 ∨
      Module.finrank ℝ (A t x).range = 1 ∨
        Module.finrank ℝ (A t x).range = 3 := by
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  have hdim : Module.finrank ℝ (V x) = 3 :=
    (VectorBundle.finrank_eq ℝ F V x).trans hF
  apply curvatureOperatorEndomorphism_finrank_range_trichotomy
    hdim (A t x).toLinearMap (hApos t ⟨ht.1.le, ht.2⟩ x).toLinearMap
  intro v hv
  exact curvatureOperator_reaction_annihilates_kernel_at_positive_time
    G cov hcov hT A hAsymm hApos hAcont hAspace X hG hreg hX hGconn
    hevolution ht x v hv

end DifferentialGeometry.Analysis.Parabolic
