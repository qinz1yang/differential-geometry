import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.RankPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Rank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureTrichotomy

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]


theorem whole_flow_trichotomy_exclusive_of_complete_existence_and_uniqueness
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ s ∈ Ioo a b, ∀ (N : Type)
        [TopologicalSpace N]
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
    (hclosedUnique :
      let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
      let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
      ∀ u v, a < u → (huv : u < v) → v < b →
      ∀ S₁ S₂ : CompleteBoundedCurvatureSolutionOn
        (I := I) (M := UniversalCover M)
        (D := RealTimeInterval.closed u v huv.le),
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : UniversalCover M,
        normSq0S (S₁.solution.base.metric t) x 4
          (metricRm04At (S₁.solution.base.metric t) x) ≤ C) →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : UniversalCover M,
        normSq0S (S₂.solution.base.metric t) x 4
          (metricRm04At (S₂.solution.base.metric t) x) ≤ C) →
      S₁.solution.base.metric u = S₂.solution.base.metric u →
      ∀ t ∈ Icc u v, S₁.solution.base.metric t = S₂.solution.base.metric t) :
    let flat := ((∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, S.family.metric s = S.family.metric t) ∧
      ∀ t ∈ Ioo a b, ∀ x u v w,
        riemannOp (Geometry.Connection.LeviCivita (S.family.metric t))
          x u v w = 0)
    let product := (∃ (N : Type) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric
                𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
              (F : Diffeomorph
                ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                  𝓘(ℝ, ℝ)) I (N × ℝ) (UniversalCover M) ∞),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ Ioo a b, RiemannianMetricComplete (h t)) ∧
              (∀ (s : ℝ) (hs : s ∈ Ioo a b), IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.openInterval a b s hs))) ∧
              (∀ t ∈ Ioo a b, Diffeomorph.pullbackMetricCross
                (liftedMetric (S.family.metric t)) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Ioo a b, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Ioo a b, ∀ y u v,
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v)
    let positive := ∀ t ∈ Ioo a b, ∀ x : M, ∀ beta : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        beta ≠ 0 → 0 < (twoFormMetricData (S.family.metric t) x).inner
          (curvatureOperatorEndomorphismAt (S.family.metric t) x
            ⟨metricRm04At (S.family.metric t) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ beta) beta
    (flat ∨ product ∨ positive) ∧
      ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  intro flat product positive
  let q := fun t (x : M) => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  have hflatRank (hf : flat) : ∀ t ∈ Ioo a b, ∀ x, q t x = 0 := by
    intro t ht
    exact curvatureOperatorImageAt_finrank_eq_zero_of_riemannOp_eq_zero
      (S.family.metric t) (hf.2 t ht)
  have hproductRank (hp : product) : ∀ t ∈ Ioo a b, ∀ x, q t x = 1 := by
    obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, -, -, -, -, hprod, hscalar, -⟩ := hp
    let _ := htop
    let _ := hcs
    let _ := hman
    let _ := ht2
    let _ := hσ
    intro t ht x
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
    have hprod' := Diffeomorph.pullbackMetricCross_symm_eq_iff.mp (hprod t ht)
    have hr := Geometry.Curvature.DimensionThree.curvatureOperatorImageAt_finrank_pullback_prod_real_eq_one_of_scalar_ne_zero
      (h t) F.symm (by simp [Topology.Morse.MorseModel]) x' (ne_of_gt (hscalar t ht _))
    rw [hprod'] at hr
    exact (curvatureOperatorImageAt_finrank_liftedMetric (S.family.metric t) x'
      (by simp [Topology.Morse.MorseModel])).symm.trans hr
  have hpositiveRank (hp : positive) : ∀ t ∈ Ioo a b, ∀ x, q t x = 3 := by
    intro t ht x
    have hr := curvatureOperatorImageAt_finrank_eq_of_pos (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ (hp t ht x)
    simpa [q, Topology.Morse.MorseModel] using hr
  have hexclusive : ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
    obtain ⟨s, hs⟩ := exists_between hab
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hf, hp⟩
      have h0 := hflatRank hf s hs default
      have h1 := hproductRank hp s hs default
      omega
    · rintro ⟨hf, hp⟩
      have h0 := hflatRank hf s hs default
      have h3 := hpositiveRank hp s hs default
      omega
    · rintro ⟨hf, hp⟩
      have h1 := hproductRank hf s hs default
      have h3 := hpositiveRank hp s hs default
      omega
  refine ⟨?_, hexclusive⟩
  let U : SolutionOn (I := I) (M := UniversalCover M) D := S.universalCover
  have hU : IsSolutionOn U := hS.universalCover S
  have hUreg : Ioo a b ⊆ D.regular := hreg
  have hUR : ∀ t ∈ Ioo a b, ∀ x : UniversalCover M,
      (⟨metricRm04At (U.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := UniversalCover M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := UniversalCover M) := by
    intro t ht x
    change metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (S.family.metric t)) x ∈ _
    exact (metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
      (S.family.metric t) x).2 (hR t ht (proj x))
  have hUcomplete : ∀ t ∈ Ioo a b, RiemannianMetricComplete (U.family.metric t) := by
    intro t ht
    exact S.universalCover_complete t (hcomplete t ht)
  have hUbound : ∀ u v, a < u → u < v → v < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : UniversalCover M,
        normSq0S (U.family.metric t) x 4 (metricRm04At (U.family.metric t) x) ≤ C := by
    intro u v hau huv hvb
    obtain ⟨C, hC, hB⟩ := hbound u v hau huv hvb
    exact ⟨C, hC, fun t ht x => by
      change normSq0S (liftedMetric (S.family.metric t)) x 4
        (metricRm04At (liftedMetric (S.family.metric t)) x) ≤ C
      rw [normSq0S_metricRm04At_liftedMetric]
      exact hB t ht (proj x)⟩
  have hrank := exists_curvatureOperatorImageAt_finrank_eq_on_interval_of_complete_existence_and_uniqueness
    U hU hUreg hUR hUcomplete hUbound hexists hclosedUnique
  rcases hrank with ⟨r, hrset, hrank⟩
  have hbaseRank : ∀ t ∈ Ioo a b, ∀ x : M, q t x = r := by
    intro t ht x
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
    exact (curvatureOperatorImageAt_finrank_liftedMetric
      (S.family.metric t) x' (by simp [DifferentialGeometry.Topology.Morse.MorseModel])).symm.trans
        (hrank t ht x')
  rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hrset) with rfl | rfl | rfl
  · left
    exact ⟨fun s hs t ht => metric_eq_on_of_curvatureOperatorImageAt_finrank_eq_zero
      S hS hreg hbaseRank hs ht,
      fun t ht => Geometry.Curvature.riemannOp_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
        (S.family.metric t) (hbaseRank t ht)⟩
  · obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod,
      -, hsol, hscalar, hsectional⟩ := exists_positive_surface_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
      U hU hUreg Set.ordConnected_Ioo (Subset.rfl)
      (exists_between hab).choose_spec (hUcomplete _ (exists_between hab).choose_spec) hUR hrank
    right; left
    exact ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply, (fun t ht => hcomp t ht (hUcomplete t ht)),
      (fun _ hs => hsol hs (Subset.rfl)), hprod, hscalar, hsectional⟩
  · right; right
    intro t ht x beta hbeta
    obtain ⟨u, hau, hut⟩ := exists_between ht.1
    have hsub : Icc u t ⊆ Ioo a b := fun v hv =>
      ⟨hau.trans_le hv.1, hv.2.trans_lt ht.2⟩
    rcases DimensionThree.flow_time_slice_global_trichotomy_at_later_time
      S hS hut (hsub.trans hreg) (fun v hv => hR v (hsub hv)) (hcomplete t ht) with
      ⟨hz, -⟩ | ⟨ho, -⟩ | ⟨-, hp⟩
    · have hzero : curvatureOperatorEndomorphismAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ = 0 := hz x
      have hz' : q t x = 0 := by
        change Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x _) = 0
        have hb : curvatureOperatorImageAt (S.family.metric t) x
            ⟨metricRm04At (S.family.metric t) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ = ⊥ := by
          change (curvatureOperatorEndomorphismAt (S.family.metric t) x _).range = ⊥
          rw [hzero]
          exact LinearMap.range_zero
        rw [hb]
        exact finrank_bot ℝ _
      have h3 := hbaseRank t ht x
      omega
    · have h1 : q t x = 1 := ho x
      have h3 := hbaseRank t ht x
      omega
    · exact hp x beta hbeta

end DifferentialGeometry.PDE.RicciFlow
