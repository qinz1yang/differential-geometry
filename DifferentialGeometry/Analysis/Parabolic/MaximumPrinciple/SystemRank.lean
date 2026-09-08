import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.RankSpreading
import DifferentialGeometry.Analysis.Spectral.BundleLowerKyFan
import DifferentialGeometry.Analysis.TimeInterval
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity
import DifferentialGeometry.Bundle.HomNorm
import DifferentialGeometry.Geometry.Metric.BundleContinuity

set_option autoImplicit false

noncomputable section

open Bundle Set CovariantDerivative Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem lowerKyFanSum_continuousOn_of_endomorphism_continuous
    [IsContinuousRiemannianBundle F V]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    {T : ℝ}
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M))) :
    ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M =>
        (hAsymm p.1 p.2).lowerKyFanSum k)
        (Icc 0 T ×ˢ (Set.univ : Set M)) := by
  let _ := fiberFinite
  intro k hk
  exact hAcont.lowerKyFanSum_bundle (fun p => hAsymm p.1 p.2) hk

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V I] [IsContMDiffRiemannianBundle I ∞ F V] in
private theorem endomorphism_norm_bound_on_compact_time_interval
    [IsContinuousRiemannianBundle F V]
    {T : ℝ}
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M))) :
    ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {K : Set M}, IsCompact K →
        ∃ R, ∀ q ∈ Icc s t, ∀ z ∈ K, ‖A q z‖ ≤ R := by
  intro s t hs hst ht K hK
  obtain ⟨R, -, hR⟩ := (isCompact_Icc.prod hK).exists_hom_bundle_opNorm_bound
    (hAcont.mono fun p hp =>
      ⟨⟨hs.trans hp.1.1, hp.1.2.trans ht⟩, Set.mem_univ p.2⟩)
  exact ⟨R, fun q hq z hz => hR (q, z) ⟨hq, hz⟩⟩

theorem finrank_range_spatially_constant_and_locally_constant_of_continuous_endomorphism
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Icc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range =
        Module.finrank ℝ (A t y).range) ∧
      (∀ x, MonotoneOn
        (fun t ↦ Module.finrank ℝ (A t x).range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).range =
            Module.finrank ℝ (A t x).range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z ↦ VectorBundle.finiteDimensional ℝ F V z
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  exact finrank_range_spatially_constant_and_locally_constant_of_metricFamilySmoothOn
    G cov hcov hT A hAsymm hApos
    (lowerKyFanSum_continuousOn_of_endomorphism_continuous A hAsymm hAcont)
    (endomorphism_norm_bound_on_compact_time_interval A hAcont)
    X reaction hreactionNull hreactionLip hG hreg hX hGconnClosed
    (fun q hq z => (hevolution q hq z).differentiableAt)
    (fun q hq z => (hevolution q hq z).deriv)

theorem rank_finite_interval_partition_of_continuous_endomorphism
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc 0 T, ∀ z, (A q z).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T →
      ∀ {Kset : Set M}, IsCompact Kset → ∀ R,
        ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset,
          LipschitzOnWith Klip (reaction q z)
            {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Icc 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M =>
      (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M))
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Icc 0 T,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hevolution : ∀ q ∈ Ioc 0 T, ∀ z,
      HasDerivAt (fun r ↦ A r z)
        (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ T) :
    ∃ Q : Finset ℕ,
      Icc a b = ⋃ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q} ∧
      (Q : Set ℕ).PairwiseDisjoint
        (fun q => {t | t ∈ Icc a b ∧ ∀ x,
          Module.finrank ℝ (A t x).range = q}) ∧
      ∀ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ Icc a b ∧ ∀ x,
            Module.finrank ℝ (A t x).range = q} = Icc a u ∧
              (∀ x, Module.finrank ℝ (A a x).range = q) ∨
            {t | t ∈ Icc a b ∧ ∀ x,
              Module.finrank ℝ (A t x).range = q} = Ioc l u ∧
              ¬ ∀ x, Module.finrank ℝ (A a x).range = q) := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z ↦ VectorBundle.finiteDimensional ℝ F V z
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).range ≤
        Module.finrank ℝ (A t y).range := by
    intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_metricFamilySmoothOn
      G cov hcov hT A hAsymm hApos
      (lowerKyFanSum_continuousOn_of_endomorphism_continuous A hAsymm hAcont)
      (endomorphism_norm_bound_on_compact_time_interval A hAcont)
      X reaction hreactionNull hreactionLip hG hreg hX hGconnClosed
      (fun q hq z => (hevolution q hq z).differentiableAt)
      (fun q hq z => (hevolution q hq z).deriv) hs hst ht x y
  exact rank_finite_interval_partition_of_spreading
    hT (fun t ht x =>
      (ContinuousAt.eventually_finrank_range_ge (hevolution t ht x).continuousAt).filter_mono inf_le_left)
    hspread ha hab hb

theorem finrank_range_le_at_later_time_of_continuous_endomorphism_on_Ioo
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hcovsmooth : ∀ q ∈ Ico 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ico 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) : ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ico 0 T, ∀ z, satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t < T → ∀ {Kset : Set M}, IsCompact Kset → ∀ R, ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset, LipschitzOnWith Klip (reaction q z) {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Ico 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Ico 0 T, G.connection q = LeviCivita (I := I) (G.metric q))
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z, HasDerivAt (fun r ↦ A r z) (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q) (fun w ↦ A q w) z + HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) + reaction q z (A q z)) q)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t < T) (x y : M) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  classical
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  let _ : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := ∞)
  have hT : 0 < T := (hs.trans_lt hst).trans ht
  have hzero : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have htpos : 0 < t := hs.trans_lt hst
  have hsub : Icc 0 t ⊆ Ico 0 T := fun q hq => ⟨hq.1, hq.2.trans_lt ht⟩
  let A' : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯ :=
    fun q => if q ∈ Ico 0 T then A q else 0
  have hAeq : ∀ q ∈ Ico 0 T, A' q = A q := by
    intro q hq
    exact if_pos hq
  have hAsymm' : ∀ q z, ((A' q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric := by
    intro q z
    by_cases hq : q ∈ Ico 0 T
    · rw [hAeq q hq]
      exact (hApos q hq z).toLinearMap.isSymmetric
    · simp only [A', if_neg hq]
      change (0 : V z →ₗ[ℝ] V z).IsSymmetric
      exact LinearMap.IsSymmetric.zero
  have hApos' : ∀ q ∈ Icc 0 t, ∀ z, (A' q z).IsPositive := by
    intro q hq z
    rw [hAeq q (hsub hq)]
    exact hApos q (hsub hq) z
  have hAcont' : ContinuousOn (fun p : ℝ × M =>
      TotalSpace.mk' (F →L[ℝ] F) p.2 (A' p.1 p.2) :
        ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))
      (Icc 0 t ×ˢ (Set.univ : Set M)) := by
    apply (hAcont.mono (fun p hp => ⟨hsub hp.1, hp.2⟩)).congr
    intro p hp
    exact congrArg (fun B : Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯ =>
      (TotalSpace.mk' (F →L[ℝ] F) p.2 (B p.2) :
        TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x))) (hAeq p.1 (hsub hp.1))
  let cov' : ℝ → CovariantDerivative I F V :=
    fun q => if q ∈ Ico 0 T then cov q else cov 0
  let _ : ∀ q, ContMDiffCovariantDerivative (cov' q) ∞ := by
    intro q
    dsimp only [cov']
    split_ifs with hq
    · exact hcovsmooth q hq
    · exact hcovsmooth 0 hzero
  have hcov' : ∀ q, (cov' q).IsMetricCompatible := by
    intro q
    dsimp only [cov']
    split_ifs with hq
    · exact hcov q hq
    · exact hcov 0 hzero
  let reaction' : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z :=
    fun q z => if q ∈ Ico 0 T then reaction q z else fun _ => 0
  have hnull : ∀ q z, satisfiesNullEigenvectorCondition (reaction' q z) := by
    intro q z
    by_cases hq : q ∈ Ico 0 T
    · simpa only [reaction', if_pos hq] using hreactionNull q hq z
    · intro B hB v hv
      simp only [reaction', if_neg hq, zero_apply, inner_zero_left, le_refl]
  have hlip : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ t → ∀ {K : Set M},
      IsCompact K → ∀ R, ∃ Klip : NNReal, ∀ q ∈ Ioc a b, ∀ z ∈ K,
        LipschitzOnWith Klip (reaction' q z)
          {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R} := by
    intro a b ha hab hb K hK R
    obtain ⟨Klip, hKlip⟩ := hreactionLip ha hab (hb.trans_lt ht) hK R
    refine ⟨Klip, ?_⟩
    intro q hq z hz
    have hqT : q ∈ Ico 0 T := ⟨(ha.trans_lt hq.1).le, hq.2.trans_lt (hb.trans_lt ht)⟩
    simpa only [reaction', if_pos hqT] using hKlip q hq z hz
  have hevol : ∀ q ∈ Ioc 0 t, ∀ z,
      HasDerivAt (fun r ↦ A' r z)
        (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov' q)
            (fun w ↦ A' q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov' q) (cov' q) (fun w ↦ A' q w) z (X q z) +
          reaction' q z (A' q z)) q := by
    intro q hq z
    have hqT : q ∈ Ioo 0 T := ⟨hq.1, hq.2.trans_lt ht⟩
    have hqT' : q ∈ Ico 0 T := ⟨hqT.1.le, hqT.2⟩
    have hev : (fun r => A' r z) =ᶠ[𝓝 q] (fun r => A r z) := by
      filter_upwards [isOpen_Ioo.mem_nhds hqT] with r hr
      rw [hAeq r ⟨hr.1.le, hr.2⟩]
    simpa only [hAeq q hqT', cov', reaction', if_pos hqT'] using
      (hevolution q hqT z).congr_of_eventuallyEq hev
  have hbound : ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ t → ∀ {K : Set M},
      IsCompact K → ∃ R, ∀ q ∈ Icc a b, ∀ z ∈ K, ‖A' q z‖ ≤ R := by
    intro a b ha hab hb K hK
    obtain ⟨R, -, hR⟩ := (isCompact_Icc.prod hK).exists_hom_bundle_opNorm_bound
      (hAcont'.mono fun p hp => ⟨⟨ha.trans hp.1.1, hp.1.2.trans hb⟩, mem_univ p.2⟩)
    exact ⟨R, fun q hq z hz => hR (q, z) ⟨hq, hz⟩⟩
  have hmain := finrank_range_le_at_later_time_of_metricFamilySmoothOn
    G cov' hcov' htpos A' hAsymm' hApos'
    (fun k hk => hAcont'.lowerKyFanSum_bundle (fun p => hAsymm' p.1 p.2) hk)
    hbound X reaction' hnull hlip hG (hsub.trans hreg)
    (hX.mono fun p hp => ⟨hsub hp.1, hp.2⟩)
    (fun q hq => hGconnClosed q (hsub hq))
    (fun q hq z => (hevol q hq z).differentiableAt)
    (fun q hq z => (hevol q hq z).deriv) hs hst le_rfl x y
  rw [hAeq s ⟨hs, hst.trans ht⟩, hAeq t ⟨htpos.le, ht⟩] at hmain
  exact hmain

theorem finrank_range_spatially_constant_and_locally_constant_on_Ioo
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ} (hT : 0 < T)
    (hcovsmooth : ∀ q ∈ Ico 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ico 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) : ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ico 0 T, ∀ z, satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t < T → ∀ {Kset : Set M}, IsCompact Kset → ∀ R, ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset, LipschitzOnWith Klip (reaction q z) {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Ico 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Ico 0 T, G.connection q = LeviCivita (I := I) (G.metric q))
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z, HasDerivAt (fun r ↦ A r z) (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q) (fun w ↦ A q w) z + HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) + reaction q z (A q z)) q)
 :
    (∀ t ∈ Ioo 0 T, ∀ x y,
      Module.finrank ℝ (A t x).range = Module.finrank ℝ (A t y).range) ∧
    (∀ x, MonotoneOn (fun t => Module.finrank ℝ (A t x).range) (Ioo 0 T)) ∧
    (∀ t ∈ Ioo 0 T, ∀ x,
      ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
        Module.finrank ℝ (A s x).range = Module.finrank ℝ (A t x).range) ∧
    ∃ δ ∈ Ioo 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x,
      Module.finrank ℝ (A t x).range = q := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t < T → ∀ x y,
      Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
    intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_continuous_endomorphism_on_Ioo
      G cov hcovsmooth hcov A hApos hAcont X reaction hreactionNull hreactionLip
      hG hreg hX hGconnClosed hevolution hs hst ht x y
  have hrank {u : ℝ} (hu : u ∈ Ioo 0 T) :=
    rank_spatially_constant_and_locally_constant_from_left_of_spreading
      (rank := fun t x => Module.finrank ℝ (A t x).range) hu.1
      (fun t ht x =>
        (ContinuousAt.eventually_finrank_range_ge
          (hevolution t ⟨ht.1, ht.2.trans_lt hu.2⟩ x).continuousAt).filter_mono inf_le_left)
      (fun hs hst ht x y => hspread hs hst (ht.trans_lt hu.2) x y)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht x y
    exact (hrank ht).1 t ⟨ht.1, le_rfl⟩ x y
  · intro x s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    · exact hspread hs.1.le hst ht.2 x x
  · intro t ht x
    exact (hrank ht).2.2.1 t ⟨ht.1, le_rfl⟩ x
  · have hh : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
    obtain ⟨δ, hδ, q, hq⟩ := (hrank hh).2.2.2
    exact ⟨δ, ⟨hδ.1, hδ.2.trans_lt hh.2⟩, q, hq⟩

theorem rank_finite_interval_partition_on_Ioo
    [I.Boundaryless] [ConnectedSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    {T : ℝ}
    (hcovsmooth : ∀ q ∈ Ico 0 T, ContMDiffCovariantDerivative (cov q) ∞)
    (hcov : ∀ q ∈ Ico 0 T, (cov q).IsMetricCompatible)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hApos : ∀ q ∈ Ico 0 T, ∀ z, (A q z).IsPositive)
    (hAcont : ContinuousOn (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] F) p.2 (A p.1 p.2) : ℝ × M → TotalSpace (F →L[ℝ] F) (fun x => V x →L[ℝ] V x)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) → (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q ∈ Ico 0 T, ∀ z, satisfiesNullEigenvectorCondition (reaction q z))
    (hreactionLip : ∀ {s t : ℝ}, 0 ≤ s → s < t → t < T → ∀ {Kset : Set M}, IsCompact Kset → ∀ R, ∃ Klip : NNReal, ∀ q ∈ Ioc s t, ∀ z ∈ Kset, LipschitzOnWith Klip (reaction q z) {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (hreg : Ico 0 T ⊆ D.regular)
    (hX : ContinuousOn (fun p : ℝ × M => (TotalSpace.mk' E p.2 (X p.1 p.2) : TangentBundle I M)) (Ico 0 T ×ˢ (Set.univ : Set M)))
    (hGconnClosed : ∀ q ∈ Ico 0 T, G.connection q = LeviCivita (I := I) (G.metric q))
    (hevolution : ∀ q ∈ Ioo 0 T, ∀ z, HasDerivAt (fun r ↦ A r z) (rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q) (fun w ↦ A q w) z + HomConnectionGen.homBundleCovariantDerivativeGen I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) + reaction q z (A q z)) q)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    ∃ Q : Finset ℕ,
      Icc a b = ⋃ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q} ∧
      (Q : Set ℕ).PairwiseDisjoint
        (fun q => {t | t ∈ Icc a b ∧ ∀ x,
          Module.finrank ℝ (A t x).range = q}) ∧
      ∀ q ∈ Q, {t | t ∈ Icc a b ∧ ∀ x,
        Module.finrank ℝ (A t x).range = q}.Nonempty ∧
        ∃ l u : ℝ, a ≤ l ∧ l ≤ u ∧ u ≤ b ∧
          ({t | t ∈ Icc a b ∧ ∀ x,
            Module.finrank ℝ (A t x).range = q} = Icc a u ∧
              (∀ x, Module.finrank ℝ (A a x).range = q) ∨
            {t | t ∈ Icc a b ∧ ∀ x,
              Module.finrank ℝ (A t x).range = q} = Ioc l u ∧
              ¬ ∀ x, Module.finrank ℝ (A a x).range = q) := by
  let _ : ∀ z, FiniteDimensional ℝ (V z) :=
    fun z => VectorBundle.finiteDimensional ℝ F V z
  have hbpos : 0 < b := ha.trans_le hab
  apply rank_finite_interval_partition_of_spreading
    (rank := fun t x => Module.finrank ℝ (A t x).range) hbpos
  · intro t ht x
    exact (ContinuousAt.eventually_finrank_range_ge
      (hevolution t ⟨ht.1, ht.2.trans_lt hb⟩ x).continuousAt).filter_mono inf_le_left
  · intro s t hs hst ht x y
    exact finrank_range_le_at_later_time_of_continuous_endomorphism_on_Ioo
      G cov hcovsmooth hcov A hApos hAcont X reaction hreactionNull hreactionLip
      hG hreg hX hGconnClosed hevolution hs hst (ht.trans_lt hb) x y
  · exact ha
  · exact hab
  · exact le_rfl

end PositiveSystem
