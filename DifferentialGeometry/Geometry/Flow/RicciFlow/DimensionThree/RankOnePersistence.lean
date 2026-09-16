import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductQuotient
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductCompactness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.UniversalCover
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy
import DifferentialGeometry.Geometry.Curvature.SurfaceProductBounds
import DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.FlatPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.TimeRestriction
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

section

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

private theorem exists_complete_surface_product_at_rank_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.family.metric s))
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x₀ : M)
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
            ∃ (h₀ : SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) M ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              RiemannianMetricComplete h₀ ∧
              Diffeomorph.pullbackMetricCross (S.family.metric s) F =
                h₀.prod (euclideanMetric (E := ℝ)) := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  obtain ⟨r, har, hrs⟩ := exists_between hs.1
  have hsub : Icc r s ⊆ Ioo a b := fun q hq =>
    ⟨har.trans_le hq.1, hq.2.trans_lt hs.2⟩
  have hall x : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x
      ⟨metricRm04At (S.family.metric s) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x⟩) = 1 :=
    (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrs
      (hsub.trans hreg) (fun q hq => hR q (hsub hq)) x x₀).trans hrank
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod⟩ :=
    exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
      S hS hreg (J := {s}) (Set.ordConnected_singleton)
      (fun _ ht => (Set.mem_singleton_iff.mp ht) ▸ hs) (Set.mem_singleton s)
      hcomplete hR (fun t ht => (Set.mem_singleton_iff.mp ht) ▸ hall)
  exact ⟨N, htop, hcs, hmanifold, ht2, hσ, h s, F, hconn, hsimply,
    hcomp s (Set.mem_singleton s) hcomplete, hprod s (Set.mem_singleton s)⟩

theorem exists_right_interval_curvatureOperatorImageAt_finrank_eq_one_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ (N : Type) [TopologicalSpace N]
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
    (hunique : ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen u v huv),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Ico u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∃ c ∈ Ioo s b, ∀ t ∈ Ico s c, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1 := by
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, h₀, F, -, -, hc₀, hprod⟩ :=
    exists_complete_surface_product_at_rank_one S hS hs hreg (hcomplete s hs) hR x₀ hrank
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  obtain ⟨r, hsr, hrb⟩ := exists_between hs.2
  obtain ⟨B₀, hB₀, hb₀⟩ := hbound s r hs.1 hsr hrb
  have hb₀' : ∀ y : N, normSq0S h₀ y 4 (metricRm04At h₀ y) ≤ B₀ :=
    normSq0S_metricRm04At_le_of_pullbackMetricCross_eq_prod_real
      (S.family.metric s) h₀ F hprod (hb₀ s ⟨le_rfl, hsr.le⟩)
  obtain ⟨d, hsd, Q, hQ₀, BQ, hBQ, hQbound⟩ :=
    hexists N h₀ hc₀ ⟨B₀, hB₀, hb₀'⟩
  obtain ⟨c, hsc, hc⟩ := exists_between (lt_min hs.2 hsd)
  have hcb : c < b := hc.trans_le (min_le_left _ _)
  have hcd : c < d := hc.trans_le (min_le_right _ _)
  let D' := RealTimeInterval.closedOpen s c hsc
  have hsub : Ico s c ⊆ Ioo a b := fun t ht =>
    ⟨hs.1.trans_le ht.1, ht.2.trans hcb⟩
  let S' : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D') := {
    solution := S.timeRestrict D'
    isSolution := isSolutionOn_timeRestrict hS
      (fun t ht => D.regular_subset (hreg (hsub ht)))
      (fun t ht => hreg (hsub ⟨ht.1.le, ht.2⟩))
    complete := fun t ht => hcomplete t (hsub ht)
    curvatureBound := by
      intro t ht
      obtain ⟨C, hC, hCb⟩ := hbound s c hs.1 hsc hcb
      exact ⟨C, hC, hCb t ⟨ht.1, ht.2.le⟩⟩ }
  let Q' : SolutionOn
      (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (M := N) D' :=
    Q.solution.timeRestrict D'
  have hQ' : IsSolutionOn Q' := isSolutionOn_timeRestrict Q.isSolution
    (fun t ht => ⟨ht.1, ht.2.trans hcd⟩)
    (fun t ht => ⟨ht.1, ht.2.trans hcd⟩)
  let L : SolutionOn (I := 𝓘(ℝ, ℝ)) (M := ℝ) D' :=
    SolutionOn.const (euclideanMetric (E := ℝ)) D'
  have hL : IsSolutionOn L := isSolutionOn_const_euclidean_real D'
  let P : CompleteBoundedCurvatureSolutionOn
      (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      (M := N × ℝ) (D := D') := {
    solution := Q'.prod L
    isSolution := isSolutionOn_prod Q' hQ' L hL
    complete := by
      intro t ht
      exact RiemannianMetricComplete.prod (Q.complete t ⟨ht.1, ht.2.trans hcd⟩)
        euclideanMetric_complete
    curvatureBound := by
      intro t ht
      refine ⟨BQ, hBQ, fun x => ?_⟩
      change normSq0S ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) x 4
        (metricRm04At ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) x) ≤ BQ
      rw [normSq0S_metricRm04At_productReal]
      exact hQbound t ⟨ht.1, ht.2.trans hcd⟩ x.1 }
  let U := P.pullback F.symm
  have hU₀ : U.solution.base.metric s = S'.solution.base.metric s := by
    change Diffeomorph.pullbackMetricCross
      ((Q.solution.base.metric s).prod (euclideanMetric (E := ℝ))) F.symm = S.family.metric s
    rw [hQ₀]
    exact Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hprod
  have hUbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico s c, ∀ x : M,
      normSq0S (U.solution.base.metric t) x 4
        (metricRm04At (U.solution.base.metric t) x) ≤ C := by
    refine ⟨BQ, hBQ, fun t ht x => ?_⟩
    change normSq0S
      (Diffeomorph.pullbackMetricCross
        ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) F.symm) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross
        ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) F.symm) x) ≤ BQ
    rw [CheegerGromovCompactness.riemannNormSq_cross, normSq0S_metricRm04At_productReal]
    exact hQbound t ⟨ht.1, ht.2.trans hcd⟩ (F.symm x).1
  have hSbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico s c, ∀ x : M,
      normSq0S (S'.solution.base.metric t) x 4
        (metricRm04At (S'.solution.base.metric t) x) ≤ C := by
    obtain ⟨C, hC, hCb⟩ := hbound s c hs.1 hsc hcb
    exact ⟨C, hC, fun t ht => hCb t ⟨ht.1, ht.2.le⟩⟩
  have heq := hunique s c hs.1 hsc hcb S' U hSbound hUbound hU₀.symm
  refine ⟨c, ⟨hsc, hcb⟩, fun t ht x => ?_⟩
  have heq' : S.family.metric t = Diffeomorph.pullbackMetricCross
      ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) F.symm := heq t ht
  have hupper : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ 1 := by
    rw [heq']
    exact DifferentialGeometry.Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_pullback_prod_real_le_one
      (Q.solution.base.metric t) F.symm
      (by simp [DifferentialGeometry.Topology.Morse.MorseModel]) x
  apply Nat.le_antisymm hupper
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  rcases ht.1.eq_or_lt with he | hst
  · subst t
    obtain ⟨r, har, hrs⟩ := exists_between hs.1
    have hsub₀ : Icc r s ⊆ Ioo a b := fun q hq =>
      ⟨har.trans_le hq.1, hq.2.trans_lt hs.2⟩
    have heq₀ := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrs
      (hsub₀.trans hreg) (fun q hq => hR q (hsub₀ hq)) x x₀
    rw [heq₀, hrank]
  · have hsub₁ : Icc s t ⊆ Ioo a b := fun q hq =>
      ⟨hs.1.trans_le hq.1, hq.2.trans_lt (ht.2.trans hcb)⟩
    have hle := curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hst
      (hsub₁.trans hreg) (fun q hq => hR q (hsub₁ hq)) x₀ x
    rw [hrank] at hle
    exact hle

private theorem rank_le_on_interval_of_closed_and_right_extension
    {a b s : ℝ} (q : ℝ → ℕ) (hs : s ∈ Ioo a b)
    (hclosed : ∀ v ∈ Ioo s b, IsClosed ({t | q t ≤ 1} ∩ Icc s v))
    (hzero : ∀ t ∈ Ioo a b, q t = 0 → ∀ u ∈ Ioo a b, q u = 0)
    (hforward : ∀ t ∈ Ioo a b, q t = 1 →
      ∃ c ∈ Ioo t b, ∀ u ∈ Ico t c, q u ≤ 1)
    (hmono : MonotoneOn q (Ioo a b))
    (hrank : q s = 1) : ∀ t ∈ Ioo a b, q t = 1 := by
  have hright (v : ℝ) (hv : v ∈ Ioo s b) : q v ≤ 1 := by
    apply (hclosed v hv).mem_of_ge_of_forall_exists_gt (s := {t | q t ≤ 1})
      (by simp [hrank]) hv.1.le
    rintro t ⟨htq, hst, htv⟩
    change q t ≤ 1 at htq
    have ht : t ∈ Ioo a b := ⟨hs.1.trans_le hst, htv.trans hv.2⟩
    have hq : q t = 1 := by
      have : 1 ≤ q t := by simpa [hrank] using hmono hs ht hst
      omega
    obtain ⟨c, ⟨htc, hcb⟩, hc⟩ := hforward t ht hq
    obtain ⟨u, htu, hu⟩ := exists_between (lt_min htc htv)
    exact ⟨u, hc u ⟨htu.le, (lt_min_iff.mp hu).1⟩,
      htu, (lt_min_iff.mp hu).2.le⟩
  intro t ht
  rcases le_total t s with hts | hst
  · have hle : q t ≤ 1 := by simpa [hrank] using hmono ht hs hts
    have hne : q t ≠ 0 := by
      intro hz
      have := hzero t ht hz s hs
      omega
    omega
  · rcases eq_or_lt_of_le hst with rfl | hst
    · exact hrank
    · have hle := hright t ⟨hst, ht.2⟩
      have hge : 1 ≤ q t := by simpa [hrank] using hmono hs ht hst.le
      omega

theorem curvatureOperatorImageAt_finrank_eq_one_on_interval_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
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
      ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∀ t ∈ Ioo a b, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1 := by
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
  let q : ℝ → ℕ := fun t => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x₀
    ⟨metricRm04At (S.family.metric t) x₀,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x₀⟩)
  have hclosed (v : ℝ) (hv : v ∈ Ioo s b) :
      IsClosed ({t | q t ≤ 1} ∩ Icc s v) := by
    apply isClosed_curvatureOperatorImageAt_finrank_le_on_Icc S hS hdim x₀ 1
    intro t ht
    exact D.regular_subset (hreg ⟨hs.1.trans_le ht.1, ht.2.trans_lt hv.2⟩)
  have hzero (t : ℝ) (ht : t ∈ Ioo a b) (hz : q t = 0) :
      ∀ u ∈ Ioo a b, q u = 0 := by
    have hflat := stationary_flat_of_curvatureOperatorImageAt_finrank_eq_zero_of_complete_forward_uniqueness
      S hS hdim ht hreg hR hcomplete hbound hunique x₀ hz
    intro u hu
    dsimp only [q]
    rw [(hflat u hu).1]
    exact hz
  have hforward (t : ℝ) (ht : t ∈ Ioo a b) (hq : q t = 1) :
      ∃ c ∈ Ioo t b, ∀ u ∈ Ico t c, q u ≤ 1 := by
    obtain ⟨c, hc, hlocal⟩ :=
      exists_right_interval_curvatureOperatorImageAt_finrank_eq_one_of_complete_existence_and_uniqueness
        S hS ht hreg hR hcomplete hbound (hexists t ht) hunique x₀ hq
    exact ⟨c, hc, fun u hu => (hlocal u hu x₀).le⟩
  have hmono : MonotoneOn q (Ioo a b) := by
    intro u hu v hv huv
    rcases huv.eq_or_lt with rfl | huv
    · exact le_rfl
    · have hsub : Icc u v ⊆ Ioo a b := fun t ht =>
        ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
      exact curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim huv
        (hsub.trans hreg) (fun t ht => hR t (hsub ht)) x₀ x₀
  have hall := rank_le_on_interval_of_closed_and_right_extension q hs
    hclosed hzero hforward hmono hrank
  intro t ht x
  obtain ⟨r, har, hrt⟩ := exists_between ht.1
  have hsub : Icc r t ⊆ Ioo a b := fun u hu =>
    ⟨har.trans_le hu.1, hu.2.trans_lt ht.2⟩
  exact (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrt
    (hsub.trans hreg) (fun u hu => hR u (hsub hu)) x x₀).trans (hall t ht)

theorem exists_positive_surface_global_product_of_curvatureOperator_rank_one_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
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
      ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (x₀ : M)
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
              (∀ t ∈ Ioo a b, RiemannianMetricComplete (h t)) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.openInterval a b s hs)) ∧
              (∀ t ∈ Ioo a b, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Ioo a b, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Ioo a b, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v := by
  have hranks := curvatureOperatorImageAt_finrank_eq_one_on_interval_of_complete_existence_and_uniqueness
    S hS hs hreg hR hcomplete hbound hexists hclosedUnique x₀ hrank
  obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod,
      hderiv, hsolution, hscalar, hsectional⟩ :=
    exists_positive_surface_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
      S hS hreg (J := Ioo a b) (Set.ordConnected_Ioo) (Subset.refl _) hs
      (hcomplete s hs) hR hranks
  exact ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply,
    fun t ht => hcomp t ht (hcomplete t ht), hsolution hs (Subset.refl _),
    hprod, hscalar, hsectional⟩

end

section CompactProduct

open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
  [SemilocallySimplyConnectedSpace M] [Inhabited M]
variable {N : Type} [TopologicalSpace N]
  [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

omit [CompactSpace M] [SigmaCompactSpace N] [ConnectedSpace N] in
private theorem scalar_pos_of_surface_product
    (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
    (F : Diffeomorph
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      I (N × ℝ) (UniversalCover M) ∞)
    (hprod : Diffeomorph.pullbackMetricCross (liftedMetric g) F =
      h.prod (euclideanMetric (E := ℝ)))
    (hscalar : ∀ y, 0 < metricScalarAt h y) : ∀ x, 0 < metricScalarAt g x := by
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  intro x
  let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
  let p := F.symm x'
  have hf := congrArg
    (fun q : SmoothRiemannianMetric
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ)) (N × ℝ) =>
      metricScalarAt q p) hprod
  rw [DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross, metricScalarAt_productMetric,
    metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp),
    add_zero, metricScalarAt_lifted] at hf
  have hx : proj (F p) = x := by dsimp [p]; rw [F.apply_symm_apply]; rfl
  rw [hx] at hf
  rw [hf]
  exact hscalar p.1

private theorem exists_right_interval_curvatureOperatorImageAt_finrank_le_one_of_surface_product
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (h : SmoothRiemannianMetric 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
    (hcomplete : RiemannianMetricComplete h)
    (F : Diffeomorph
      ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
      I (N × ℝ) (UniversalCover M) ∞)
    (hprod : Diffeomorph.pullbackMetricCross (liftedMetric (S.family.metric s)) F =
      h.prod (euclideanMetric (E := ℝ)))
    (hscalar : ∀ y, 0 < metricScalarAt h y) :
    ∃ c ∈ Ioo s b, ∀ t ∈ Ico s c, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ 1 := by
  let _ : CompactSpace N := compactSpace_of_compact_of_base_scalar_pos_of_pullback_eq_prod
    (S.family.metric s) h hcomplete F hprod
    (scalar_pos_of_surface_product (S.family.metric s) h F hprod hscalar)
  let _ : NeZero (Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2)) :=
    ⟨by simp [DifferentialGeometry.Topology.Morse.MorseModel]⟩
  obtain ⟨d, hsd, Q, hQ₀, -, hjoint, hpde⟩ :=
    exists_completeBoundedCurvatureSolutionOn_from_time_of_compact h s
  obtain ⟨c, hsc, hc⟩ := exists_between (lt_min hs.2 hsd)
  have hcb : c < b := hc.trans_le (min_le_left _ _)
  have hcd : c < d := hc.trans_le (min_le_right _ _)
  have hsub : Ico s c ⊆ Ioo a b := fun t ht =>
    ⟨hs.1.trans_le ht.1, ht.2.trans hcb⟩
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : SigmaCompactSpace (UniversalCover M) :=
    F.symm.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  have hinit : localPullMetric (S.family.metric s) proj (UniversalCover.proj_localDiffeo (I := I)) =
      Diffeomorph.pullbackMetricCross
        ((Q.solution.base.metric s).prod (euclideanMetric (E := ℝ))) F.symm := by
    rw [hQ₀, ← liftedMetric_eq_localPullMetric]
    exact (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hprod).symm
  have heq := localPullMetric_eq_prod_real_of_initial_of_compact S hS Q.solution.base.metric
    hsc (hsub.trans hreg) (by simp [DifferentialGeometry.Topology.Morse.MorseModel])
    (fun y => by rw [hQ₀]; exact ne_of_gt (hscalar y))
    (hjoint.mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans hcd⟩, hp.2⟩))
    (fun t ht => hpde t ⟨ht.1, ht.2.trans hcd⟩)
    F proj (UniversalCover.proj_localDiffeo (I := I)) UniversalCover.proj_isCoveringMap (by
      let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
      intro x
      exact ⟨⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩, rfl⟩) hinit
  refine ⟨c, ⟨hsc, hcb⟩, ?_⟩
  intro t ht x
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
  have heq' : liftedMetric (S.family.metric t) =
      Diffeomorph.pullbackMetricCross
        ((Q.solution.base.metric t).prod (euclideanMetric (E := ℝ))) F.symm := by simpa only [← liftedMetric_eq_localPullMetric] using heq t ht
  have hupper := Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_pullback_prod_real_le_one
    (Q.solution.base.metric t) F.symm (by simp [DifferentialGeometry.Topology.Morse.MorseModel]) x'
  rw [← heq'] at hupper
  exact (curvatureOperatorImageAt_finrank_liftedMetric (S.family.metric t) x'
    (by simp [DifferentialGeometry.Topology.Morse.MorseModel])).symm.le.trans hupper

end CompactProduct

section Compact

open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]

private theorem has_surface_product_of_rank_one
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting (S.family.metric s) := by
  obtain ⟨r, har, hrs⟩ := exists_between hs.1
  have hsub : Icc r s ⊆ Ioo a b := fun q hq =>
    ⟨har.trans_le hq.1, hq.2.trans_lt hs.2⟩
  rcases DimensionThree.flow_time_slice_global_trichotomy_at_later_time S hS hrs
    (hsub.trans hreg) (fun t ht => hR t (hsub ht))
    (RiemannianMetricComplete.of_compact (S.family.metric s)) with
    ⟨hzero, -⟩ | ⟨-, hsplit⟩ | ⟨hthree, -⟩
  · have hbot : curvatureOperatorImageAt (S.family.metric s) x₀
        ⟨metricRm04At (S.family.metric s) x₀,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩ = ⊥ := by
      change (curvatureOperatorEndomorphismAt (S.family.metric s) x₀
        ⟨metricRm04At (S.family.metric s) x₀,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩).range = ⊥
      have hz : curvatureOperatorEndomorphismAt (S.family.metric s) x₀
          ⟨metricRm04At (S.family.metric s) x₀,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩ = 0 := hzero x₀
      rw [hz]
      exact LinearMap.range_zero
    rw [hbot, finrank_bot] at hrank
    omega
  · exact hsplit
  · have h3 : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
        ⟨metricRm04At (S.family.metric s) x₀,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 3 := hthree x₀
    omega

theorem exists_right_interval_curvatureOperatorImageAt_finrank_le_one_of_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∃ c ∈ Ioo s b, ∀ t ∈ Ico s c, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ≤ 1 := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨L, P, -, -, -, hscalar⟩ := has_surface_product_of_rank_one S hS hs hreg hR x₀ hrank
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : ConnectedSpace P.N := P.connectedN
  exact exists_right_interval_curvatureOperatorImageAt_finrank_le_one_of_surface_product
    S hS hs hreg P.metricN P.completeN P.F
    (by simpa only [flatModelMetric] using P.pullbackMetric_eq_prod (S.family.metric s)) hscalar

theorem curvatureOperatorImageAt_finrank_eq_one_on_interval_of_compact
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∀ t ∈ Ioo a b, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1 := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  let q : ℝ → ℕ := fun t => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x₀
    ⟨metricRm04At (S.family.metric t) x₀,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x₀⟩)
  have hclosed (v : ℝ) (hv : v ∈ Ioo s b) :
      IsClosed ({t | q t ≤ 1} ∩ Icc s v) := by
    apply isClosed_curvatureOperatorImageAt_finrank_le_on_Icc S hS hdim x₀ 1
    intro t ht
    exact D.regular_subset (hreg ⟨hs.1.trans_le ht.1, ht.2.trans_lt hv.2⟩)
  have hzero (t : ℝ) (ht : t ∈ Ioo a b) (hz : q t = 0) :
      ∀ u ∈ Ioo a b, q u = 0 := by
    have hflat := stationary_flat_of_curvatureOperatorImageAt_finrank_eq_zero_of_compact
      S hS hdim ht hreg hR x₀ hz
    intro u hu
    dsimp only [q]
    rw [(hflat u hu).1]
    exact hz
  have hforward' (t : ℝ) (ht : t ∈ Ioo a b) (hq : q t = 1) :
      ∃ c ∈ Ioo t b, ∀ u ∈ Ico t c, q u ≤ 1 := by
    obtain ⟨c, hc, hlocal⟩ :=
      exists_right_interval_curvatureOperatorImageAt_finrank_le_one_of_compact
        S hS ht hreg hR x₀ hq
    exact ⟨c, hc, fun u hu => hlocal u hu x₀⟩
  have hmono : MonotoneOn q (Ioo a b) := by
    intro u hu v hv huv
    rcases huv.eq_or_lt with rfl | huv
    · exact le_rfl
    · have hsub : Icc u v ⊆ Ioo a b := fun t ht =>
        ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
      exact curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim huv
        (hsub.trans hreg) (fun t ht => hR t (hsub ht)) x₀ x₀
  have hall := rank_le_on_interval_of_closed_and_right_extension q hs
    hclosed hzero hforward' hmono hrank
  intro t ht x
  obtain ⟨r, har, hrt⟩ := exists_between ht.1
  have hsub : Icc r t ⊆ Ioo a b := fun u hu =>
    ⟨har.trans_le hu.1, hu.2.trans_lt ht.2⟩
  exact (curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim hrt
    (hsub.trans hreg) (fun u hu => hR u (hsub hu)) x x₀).trans (hall t ht)

end Compact

section

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

theorem exists_right_interval_common_parallel_unit_section_of_complete_existence_and_uniqueness
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b s : ℝ} (hs : s ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ (N : Type) [TopologicalSpace N]
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
    (hunique : ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen u v huv),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico u v, ∀ x : M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Ico u v, S₁.solution.base.metric t = S₂.solution.base.metric t)
    (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∃ c ∈ Ioo s b, ∃ X : Cₛ^∞⟮I; DifferentialGeometry.Topology.Morse.MorseModel 3,
        TangentSpace I⟯,
      (∀ t ∈ Icc s c, ∀ x : M,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) ∧
      (∀ t ∈ Icc s c, ∀ x, X x ∈ curvatureOperatorImageAnnihilatorAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) ∧
      (∀ t ∈ Icc s c, ∀ x, (S.family.metric t).inner x (X x) (X x) = 1) ∧
      (∀ t ∈ Icc s c, ∀ x, ∀ v : TangentSpace I x,
        (DifferentialGeometry.Geometry.Connection.LeviCivita (S.family.metric t)) X x v = 0) ∧
      ∀ t ∈ Icc s c, ∀ x, ∀ v : TangentSpace I x,
        (S.family.metric t).inner x (X x) v = (S.family.metric s).inner x (X x) v := by
  obtain ⟨d, hd, hq⟩ :=
    exists_right_interval_curvatureOperatorImageAt_finrank_eq_one_of_complete_existence_and_uniqueness
      S hS hs hreg hR hcomplete hbound hexists hunique x₀ hrank
  obtain ⟨c, hsc, hcd⟩ := exists_between hd.1
  have hcb : c < b := hcd.trans hd.2
  have hq' : ∀ t ∈ Icc s c, ∀ x : M,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1 :=
    fun t ht => hq t ⟨ht.1, ht.2.trans_lt hcd⟩
  have hsub : Icc s c ⊆ Ioo a b :=
    fun t ht => ⟨hs.1.trans_le ht.1, ht.2.trans_lt hcb⟩
  obtain ⟨X, hmem, hunit, hparallel, hdual⟩ :=
    exists_global_parallel_unit_section_on_interval_of_curvatureOperatorImage_rank_eq_one
      S hS (by simp [DifferentialGeometry.Topology.Morse.MorseModel]) hreg
      ordConnected_Icc hsub (left_mem_Icc.mpr hsc.le) hR hq'
  exact ⟨c, ⟨hsc, hcb⟩, X, hq', hmem, hunit, hparallel, hdual⟩

end

end DifferentialGeometry.PDE.RicciFlow
