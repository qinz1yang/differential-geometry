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

end PositiveSystem
