import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankOnePersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.FlatPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.TimeRestriction

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

theorem exists_curvatureOperatorImageAt_finrank_eq_on_interval_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ s ∈ Ioo a b, ∀ (N : Type) [TopologicalSpace N]
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
    (hclosedUnique : ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closed u v huv.le),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t) :
    ∃ r ∈ ({0, 1, 3} : Set ℕ), ∀ t ∈ Ioo a b, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = r := by
  classical
  have hunique : ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen u v huv),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Ico u v, S₁.solution.base.metric t = S₂.solution.base.metric t := by
    intro u v hau huv hvb S₁ S₂ hB₁ hB₂ hi
    obtain ⟨C₁, hC₁, hB₁⟩ := hB₁
    obtain ⟨C₂, hC₂, hB₂⟩ := hB₂
    apply metric_eq_on_closedOpen_of_complete_forward_uniqueness_on_closed huv S₁ S₂
      (fun c hc => ⟨C₁, hC₁, fun t ht => hB₁ t ⟨ht.1, ht.2.trans_lt hc.2⟩⟩)
      (fun c hc => ⟨C₂, hC₂, fun t ht => hB₂ t ⟨ht.1, ht.2.trans_lt hc.2⟩⟩)
      (fun c huc hcv => hclosedUnique u c hau huc (hcv.trans hvb)) hi
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  let q (t : ℝ) (x : M) : ℕ := Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
    ⟨metricRm04At (S.family.metric t) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  have hspatial (t : ℝ) (ht : t ∈ Ioo a b) (x y : M) : q t x = q t y := by
    obtain ⟨u, hau, hut⟩ := exists_between ht.1
    have hsub : Icc u t ⊆ Ioo a b := fun z hz =>
      ⟨hau.trans_le hz.1, hz.2.trans_lt ht.2⟩
    exact curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hut
      (hsub.trans hreg) (fun z hz => hR z (hsub hz)) x y
  have htri (t : ℝ) (ht : t ∈ Ioo a b) (x : M) : q t x = 0 ∨ q t x = 1 ∨ q t x = 3 := by
    obtain ⟨u, hau, hut⟩ := exists_between ht.1
    have hsub : Icc u t ⊆ Ioo a b := fun z hz =>
      ⟨hau.trans_le hz.1, hz.2.trans_lt ht.2⟩
    exact curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim hut
      (hsub.trans hreg) (fun z hz => hR z (hsub hz)) x
  by_cases hzero : ∃ t ∈ Ioo a b, ∃ x : M, q t x = 0
  · obtain ⟨s, hs, x₀, hz⟩ := hzero
    have hflat := stationary_flat_of_curvatureOperatorImageAt_finrank_eq_zero_of_complete_forward_uniqueness
      S hS hdim hs hreg hR hcomplete hbound hunique x₀ hz
    refine ⟨0, by simp, ?_⟩
    intro t ht x
    rw [(hflat t ht).1]
    exact (hspatial s hs x x₀).trans hz
  · by_cases hone : ∃ t ∈ Ioo a b, ∃ x : M, q t x = 1
    · obtain ⟨s, hs, x₀, ho⟩ := hone
      exact ⟨1, by simp,
        curvatureOperatorImageAt_finrank_eq_one_on_interval_of_complete_existence_and_uniqueness
          S hS hs hreg hR hcomplete hbound hexists hclosedUnique x₀ ho⟩
    · refine ⟨3, by simp, ?_⟩
      intro t ht x
      rcases htri t ht x with hz | ho | hthree
      · exact (hzero ⟨t, ht, x, hz⟩).elim
      · exact (hone ⟨t, ht, x, ho⟩).elim
      · exact hthree

end DifferentialGeometry.PDE.RicciFlow
