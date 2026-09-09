import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

theorem exists_curvatureOperatorImageAt_finrank_eq_on_ancient_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ s ∈ Iio T, ∀ (N : Type) [TopologicalSpace N]
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
              (metricRm04At (Q.solution.base.metric t) y) ≤ C)
    (hclosedUnique : ∀ u v, (huv : u < v) → v < T →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closed u v huv.le),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    : ∃ q ∈ ({0, 1, 3} : Set ℕ), ∀ t < T, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hR : ∀ t < T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro t ht x
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun r hr => D.regular_subset (hreg (hr.trans_lt ht)))
      (fun r hr => hreg (hr.trans ht))
      (fun r hr => hcomplete r (hr.trans_lt ht)) hdim x
  have hinterval (a b : ℝ) (hb : b < T) :
      ∃ q ∈ ({0, 1, 3} : Set ℕ), ∀ t ∈ Ioo a b, ∀ x : M,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
    apply exists_curvatureOperatorImageAt_finrank_eq_on_interval_of_complete_existence_and_uniqueness
      S hS (fun t ht => hreg (ht.2.trans hb))
      (fun t ht => hR t (ht.2.trans hb)) (fun t ht => hcomplete t (ht.2.trans hb))
      (fun u v _ huv hvb => hbound u v huv (hvb.trans hb))
      (fun t ht => hexists t (ht.2.trans hb))
      (fun u v _ huv hvb => hclosedUnique u v huv (hvb.trans hb))
  let s : ℝ := T - 1
  have hs : s < T := by dsimp [s]; linarith
  let x₀ : M := Classical.choice inferInstance
  obtain ⟨b₀, hsb₀, hb₀⟩ := exists_between hs
  obtain ⟨q, hq, hbase⟩ := hinterval (s - 1) b₀ hb₀
  have hsbase : s ∈ Ioo (s - 1) b₀ := ⟨by linarith, hsb₀⟩
  refine ⟨q, hq, ?_⟩
  intro t ht x
  obtain ⟨b, hmaxb, hb⟩ := exists_between (max_lt hs ht)
  let a : ℝ := min s t - 1
  have has : a < s := by dsimp [a]; linarith [min_le_left s t]
  have hat : a < t := by dsimp [a]; linarith [min_le_right s t]
  have hsb : s < b := (le_max_left s t).trans_lt hmaxb
  have htb : t < b := (le_max_right s t).trans_lt hmaxb
  obtain ⟨r, _, hr⟩ := hinterval a b hb
  exact (hr t ⟨hat, htb⟩ x).trans ((hr s ⟨has, hsb⟩ x₀).symm.trans (hbase s hsbase x₀))

end DifferentialGeometry.PDE.RicciFlow
