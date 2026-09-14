import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingFrontier

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff

structure CompleteBoundedCurvatureShortTimeExistenceOnAncient (T : ℝ) : Prop where
  shortTime : ∀ s ∈ Iio T, ∀ (N : Type) [TopologicalSpace N]
      [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
      [IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N]
      [T2Space N] [SigmaCompactSpace N],
    ∀ h₀ : SmoothRiemannianMetric 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N,
    RiemannianMetricComplete h₀ →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : N, normSq0S h₀ y 4 (metricRm04At h₀ y) ≤ C) →
    ∃ (d : ℝ) (hsd : s < d),
      ∃ Q : CompleteBoundedCurvatureSolutionOn
        (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (M := N)
        (D := RealTimeInterval.closedOpen s d hsd),
        Q.solution.base.metric s = h₀ ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico s d, ∀ y : N,
          normSq0S (Q.solution.base.metric t) y 4
            (metricRm04At (Q.solution.base.metric t) y) ≤ C

structure CompleteBoundedCurvatureUniquenessOnAncient {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] (T : ℝ) : Prop where
  unique : ∀ u v, (huv : u < v) → v < T →
    ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
      (D := RealTimeInterval.closed u v huv.le),
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
      normSq0S (S₁.solution.base.metric t) x 4
        (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
      normSq0S (S₂.solution.base.metric t) x 4
        (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
    S₁.solution.base.metric u = S₂.solution.base.metric u →
    ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t

section AncientInputs

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

theorem curvatureOperatorImageAt_finrank_eq_one_on_ancient_of_completeBoundedCurvatureInputs
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hst : CompleteBoundedCurvatureShortTimeExistenceOnAncient T)
    (huq : CompleteBoundedCurvatureUniquenessOnAncient (I := I) (M := M) T)
    {s : ℝ} (hs : s < T) (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∀ t < T, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1 := by
  obtain ⟨q, -, hq⟩ :=
    exists_curvatureOperatorImageAt_finrank_eq_on_ancient_of_complete_existence_and_uniqueness
      (S := S) (hS := hS) (hreg := hreg) (hcomplete := hcomplete) (hbound := hbound)
      (hexists := hst.shortTime) (hclosedUnique := huq.unique)
  intro t ht x
  exact (hq t ht x).trans ((hq s hs x₀).symm.trans hrank)

theorem exists_global_product_of_rankOne_on_ancient_of_completeBoundedCurvatureInputs
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hst : CompleteBoundedCurvatureShortTimeExistenceOnAncient T)
    (huq : CompleteBoundedCurvatureUniquenessOnAncient (I := I) (M := M) T)
    {s : ℝ} (hs : s < T) (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ Iio T, RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              (∀ t ∈ Iio T, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Iio T, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                HasDerivWithinAt (fun a => (h a).inner y u v)
                  (-2 * ricciTensor (h t) y u v) (Iio T) t) ∧
              (∀ {a b t : ℝ} (ht : t ∈ Ioo a b), Ioo a b ⊆ Iio T →
                IsSolutionOn ({ base := { metric := h } } :
                  SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                    (M := N) (RealTimeInterval.openInterval a b t ht))) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.ancient T)) ∧
              (∀ t ∈ Iio T, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Iio T, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v :=
  exists_positive_surface_global_product_of_curvatureOperator_rank_one_of_complete_ancient_existence_and_uniqueness
    (S := S) (hS := hS) (hreg := hreg) (hcomplete := hcomplete) (hbound := hbound)
    (hexists := hst.shortTime) (hclosedUnique := huq.unique) (hs := hs) (x₀ := x₀)
    (hrank := hrank)

end AncientInputs

section AncientPointedFlow

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {D : RealTimeInterval}
  (F : PointedFlowData.{0, 0, 0} (I := I) D)

local instance ancientPointedFlowTopology : TopologicalSpace F.M := F.topology
local instance ancientPointedFlowCharted : ChartedSpace H F.M := F.charted
local instance ancientPointedFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientPointedFlowC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientPointedFlowT2 : T2Space F.M := F.t2
local instance ancientPointedFlowT2TangentBundle : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
local instance ancientPointedFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_global_product_of_pastTailRankOne_of_completeBoundedCurvatureInputs
    [SimplyConnectedSpace F.M]
    (hreg : Iio (0 : ℝ) ⊆ D.regular)
    (hcomplete : ∀ t < 0, RiemannianMetricComplete (F.S.family.metric t))
    (hbound : ∀ u v, u < v → v < 0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : F.M,
        normSq0S (F.S.family.metric t) x 4
          (metricRm04At (F.S.family.metric t) x) ≤ C)
    (hst : CompleteBoundedCurvatureShortTimeExistenceOnAncient (0 : ℝ))
    (huq : CompleteBoundedCurvatureUniquenessOnAncient (I := I) (M := F.M) (0 : ℝ))
    (htail : ∃ t₁ : ℝ, t₁ < 0 ∧ ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1) :
    ∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold
          𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F' : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) F.M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ Iio (0 : ℝ), RiemannianMetricComplete
                (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              (∀ t ∈ Iio (0 : ℝ), Diffeomorph.pullbackMetricCross
                (F.S.family.metric t) F' =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Iio (0 : ℝ), ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                HasDerivWithinAt (fun a => (h a).inner y u v)
                  (-2 * ricciTensor (h t) y u v) (Iio (0 : ℝ)) t) ∧
              (∀ {a b t : ℝ} (ht : t ∈ Ioo a b), Ioo a b ⊆ Iio (0 : ℝ) →
                IsSolutionOn ({ base := { metric := h } } :
                  SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                    (M := N) (RealTimeInterval.openInterval a b t ht))) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.ancient (0 : ℝ))) ∧
              (∀ t ∈ Iio (0 : ℝ), ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Iio (0 : ℝ), ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v := by
  obtain ⟨t₁, ht₁, htail'⟩ := htail
  exact exists_positive_surface_global_product_of_curvatureOperator_rank_one_of_complete_ancient_existence_and_uniqueness
    (S := F.S) (hS := F.isSolution) (hreg := hreg) (hcomplete := hcomplete)
    (hbound := hbound) (hexists := hst.shortTime) (hclosedUnique := huq.unique)
    (hs := ht₁) (x₀ := F.basepoint) (hrank := htail' t₁ le_rfl F.basepoint)

end AncientPointedFlow

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance rankOneSplittingTopology : TopologicalSpace F.M := F.topology
local instance rankOneSplittingCharted : ChartedSpace H F.M := F.charted
local instance rankOneSplittingSmooth : IsManifold I ∞ F.M := F.smooth
local instance rankOneSplittingC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance rankOneSplittingT2 : T2Space F.M := F.t2
local instance rankOneSplittingSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance rankOneSplittingInhabited : Inhabited F.M := ⟨F.basepoint⟩
local instance rankOneSplittingLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
local instance rankOneSplittingSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

theorem one_le_curvatureOperatorImageAt_finrank_on_negativeTime_of_rankOneOnPastTail
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    {t₁ : ℝ}
    (htail : ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1) :
    ∀ t : ℝ, t < 0 → ∀ x : F.M,
      1 ≤ Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) := by
  intro t ht x
  rcases lt_or_ge t₁ t with hlt | hle
  · have hreg : Set.Icc t₁ t ⊆ ancientTimeInterval.regular := by
      intro r hr
      simp only [ancientTimeInterval_regular, Set.mem_Iio]
      exact lt_of_le_of_lt hr.2 ht
    have hmono := curvatureOperatorImageAt_finrank_le_at_later_time (S := F.S)
      F.isSolution hdim hlt hreg
      (fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F
        hcurvature r (le_of_lt (lt_of_le_of_lt hr.2 ht)))
      F.basepoint x
    rw [htail t₁ le_rfl F.basepoint] at hmono
    exact hmono
  · rw [htail t hle x]

theorem curvatureOperatorImageAt_finrank_ne_two_on_negativeTime
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t) :
    ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) ≠ 2 := by
  intro t ht x hq
  have hreg : Set.Icc (t - 1) t ⊆ ancientTimeInterval.regular := by
    intro r hr
    simp only [ancientTimeInterval_regular, Set.mem_Iio]
    exact lt_of_le_of_lt hr.2 ht
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time (S := F.S)
    F.isSolution hdim (s := t - 1) (t := t) (by linarith) hreg
    (fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F
      hcurvature r (le_of_lt (lt_of_le_of_lt hr.2 ht))) x
  rcases htri with h0 | h1 | h3
  · rw [h0] at hq
    exact absurd hq (by decide)
  · rw [h1] at hq
    exact absurd hq (by decide)
  · rw [h3] at hq
    exact absurd hq (by decide)

theorem curvatureOperatorImageAt_finrank_eq_one_on_negativeTime_of_rankThreeFree
    (hconnected : ConnectedSpace F.M)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (htail : ∃ t₁ : ℝ, t₁ < 0 ∧ ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1)
    (hneThree : ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) ≠ 3) :
    ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1 := by
  obtain ⟨t₁, -, htail'⟩ := htail
  intro t ht x
  have hpos := one_le_curvatureOperatorImageAt_finrank_on_negativeTime_of_rankOneOnPastTail
    F hconnected hdim hcurvature htail' t ht x
  have hreg : Set.Icc (t - 1) t ⊆ ancientTimeInterval.regular := by
    intro r hr
    simp only [ancientTimeInterval_regular, Set.mem_Iio]
    exact lt_of_le_of_lt hr.2 ht
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time (S := F.S)
    F.isSolution hdim (s := t - 1) (t := t) (by linarith) hreg
    (fun r hr => nullPlane_curvatureOperatorImageAt_finrank_cone_membership F
      hcurvature r (le_of_lt (lt_of_le_of_lt hr.2 ht))) x
  rcases htri with h0 | h1 | h3
  · rw [h0] at hpos
    exact absurd hpos (by decide)
  · exact h1
  · exact absurd h3 (hneThree t ht x)

abbrev RankOneNegativeTimeForwardPersistence : Prop :=
  Module.finrank ℝ E = 3 →
    (∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t) →
    (∃ t₁ : ℝ, t₁ < 0 ∧ ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1) →
    ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1

omit [I.Boundaryless] in
theorem rankOneNegativeTimeForwardPersistence_of_rankOneOnNegativeTime
    (h : ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1) :
    RankOneNegativeTimeForwardPersistence (I := I) F :=
  fun _ _ _ => h

omit [I.Boundaryless] in
theorem curvatureOperatorImageAt_finrank_eq_one_on_negativeTime_of_rankThreeInput
    (hpersist : RankOneNegativeTimeForwardPersistence (I := I) F)
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (htail : ∃ t₁ : ℝ, t₁ < 0 ∧ ∀ t : ℝ, t ≤ t₁ → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1) :
    ∀ t : ℝ, t < 0 → ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.family.metric t) x
        ⟨metricRm04At (F.S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (F.S.family.metric t) x⟩) = 1 :=
  hpersist hdim hcurvature htail

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
