import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankPersistence
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


theorem ancient_flow_trichotomy_exclusive_of_complete_existence_and_uniqueness
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t ∈ Iio T, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    (hexists : ∀ s ∈ Iio T, ∀ (N : Type)
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
      ∀ u v, (huv : u < v) → v < T →
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
    let flat := ((∀ s ∈ Iio T, ∀ t ∈ Iio T, S.family.metric s = S.family.metric t) ∧
      ∀ t ∈ Iio T, ∀ x u v w,
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
              (∀ t ∈ Iio T, RiemannianMetricComplete (h t)) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.ancient T)) ∧
              (∀ t ∈ Iio T, Diffeomorph.pullbackMetricCross
                (liftedMetric (S.family.metric t)) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Iio T, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Iio T, ∀ y u v,
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v)
    let positive := ∀ t ∈ Iio T, ∀ x : M, ∀ beta : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        beta ≠ 0 → 0 < (twoFormMetricData (S.family.metric t) x).inner
          (curvatureOperatorEndomorphismAt (S.family.metric t) x
            ⟨metricRm04At (S.family.metric t) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ beta) beta
    (flat ∨ product ∨ positive) ∧
      ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  intro flat product positive
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hR : ∀ t ∈ Iio T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro t ht x
    change t < T at ht
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun r hr => D.regular_subset (hreg (hr.trans_lt ht)))
      (fun r hr => hreg (hr.trans ht))
      (fun r hr => hcomplete r (hr.trans_lt ht)) hdim x
  let q := fun t (x : M) => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  have hflatRank (hf : flat) : ∀ t ∈ Iio T, ∀ x, q t x = 0 := by
    intro t ht
    exact curvatureOperatorImageAt_finrank_eq_zero_of_riemannOp_eq_zero
      (S.family.metric t) (hf.2 t ht)
  have hproductRank (hp : product) : ∀ t ∈ Iio T, ∀ x, q t x = 1 := by
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
  have hpositiveRank (hp : positive) : ∀ t ∈ Iio T, ∀ x, q t x = 3 := by
    intro t ht x
    have hr := curvatureOperatorImageAt_finrank_eq_of_pos (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ (hp t ht x)
    simpa [q, Topology.Morse.MorseModel] using hr
  have hexclusive : ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
    let s := T - 1
    have hs : s ∈ Iio T := by change s < T; dsimp [s]; linarith
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
  have hUreg : Iio T ⊆ D.regular := hreg
  have hUR : ∀ t ∈ Iio T, ∀ x : UniversalCover M,
      (⟨metricRm04At (U.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := UniversalCover M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := UniversalCover M) := by
    intro t ht x
    change metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (S.family.metric t)) x ∈ _
    exact (metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
      (S.family.metric t) x).2 (hR t ht (proj x))
  have hUcomplete : ∀ t ∈ Iio T, RiemannianMetricComplete (U.family.metric t) := by
    intro t ht
    exact S.universalCover_complete t (hcomplete t ht)
  have hUbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : UniversalCover M,
        normSq0S (U.family.metric t) x 4 (metricRm04At (U.family.metric t) x) ≤ C := by
    intro u v huv hvb
    obtain ⟨C, hC, hB⟩ := hbound u v huv hvb
    exact ⟨C, hC, fun t ht x => by
      change normSq0S (liftedMetric (S.family.metric t)) x 4
        (metricRm04At (liftedMetric (S.family.metric t)) x) ≤ C
      rw [normSq0S_metricRm04At_liftedMetric]
      exact hB t ht (proj x)⟩
  have hrank := exists_curvatureOperatorImageAt_finrank_eq_on_ancient_of_complete_existence_and_uniqueness
    U hU hUreg hUcomplete hUbound hexists hclosedUnique
  rcases hrank with ⟨r, hrset, hrank⟩
  have hbaseRank : ∀ t ∈ Iio T, ∀ x : M, q t x = r := by
    intro t ht x
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    let x' : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
    exact (curvatureOperatorImageAt_finrank_liftedMetric
      (S.family.metric t) x' (by simp [DifferentialGeometry.Topology.Morse.MorseModel])).symm.trans
        (hrank t ht x')
  rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hrset) with rfl | rfl | rfl
  · left
    refine ⟨?_, fun t ht =>
      Geometry.Curvature.riemannOp_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
        (S.family.metric t) (hbaseRank t ht)⟩
    intro s hs t ht
    change s < T at hs
    change t < T at ht
    obtain ⟨b, hmaxb, hb⟩ := exists_between (max_lt hs ht)
    let a := min s t - 1
    have has : a < s := by dsimp [a]; linarith [min_le_left s t]
    have hat : a < t := by dsimp [a]; linarith [min_le_right s t]
    have hsb : s < b := (le_max_left s t).trans_lt hmaxb
    have htb : t < b := (le_max_right s t).trans_lt hmaxb
    exact metric_eq_on_of_curvatureOperatorImageAt_finrank_eq_zero S hS
      (fun r hr => hreg (hr.2.trans hb))
      (fun r hr => hbaseRank r (hr.2.trans hb)) ⟨has, hsb⟩ ⟨hat, htb⟩
  · have hs : T - 1 ∈ Iio T := by simp
    obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod,
        -, hsol, hscalar, hsectional⟩ :=
      exists_positive_surface_global_product_of_curvatureOperatorImage_rank_eq_one
        U hU isOpen_Iio hUreg (J := Iio T) Set.ordConnected_Iio (Subset.refl _) hs
        (hUcomplete _ hs) hUR hrank
    let _ := htop
    let _ := hcs
    let _ := hman
    let _ := ht2
    let _ := hσ
    have hancient : IsSolutionOn ({ base := { metric := h } } :
        SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
          (M := N) (RealTimeInterval.ancient T)) := by
      apply isSolutionOn_ancient_of_open_interval_restrictions
      intro a b t ht hsub
      exact hsol ht hsub
    right; left
    exact ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply,
      (fun t ht => hcomp t ht (hUcomplete t ht)), hancient, hprod, hscalar, hsectional⟩
  · right; right
    intro t ht x beta hbeta
    change t < T at ht
    let u := t - 1
    have hut : u < t := by dsimp [u]; linarith
    have hsub : Icc u t ⊆ Iio T := fun v hv => hv.2.trans_lt ht
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

omit [SigmaCompactSpace M] in
theorem ancient_flow_trichotomy_exclusive_of_compact
    [CompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hreg : Iio T ⊆ D.regular) :
    let flat := ((∀ s ∈ Iio T, ∀ t ∈ Iio T, S.family.metric s = S.family.metric t) ∧
      ∀ t ∈ Iio T, ∀ x u v w,
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
              CompactSpace N ∧ ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ Iio T, RiemannianMetricComplete (h t)) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                  (M := N) (RealTimeInterval.ancient T)) ∧
              (∀ t ∈ Iio T, Diffeomorph.pullbackMetricCross
                (liftedMetric (S.family.metric t)) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Iio T, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ Iio T, ∀ y u v,
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v)
    let positive := ∀ t ∈ Iio T, ∀ x : M, ∀ beta : TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ,
        beta ≠ 0 → 0 < (twoFormMetricData (S.family.metric t) x).inner
          (curvatureOperatorEndomorphismAt (S.family.metric t) x
            ⟨metricRm04At (S.family.metric t) x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ beta) beta
    (flat ∨ product ∨ positive) ∧
      ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  intro flat product positive
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hcomplete : ∀ t ∈ Iio T, RiemannianMetricComplete (S.family.metric t) :=
    fun t _ => RiemannianMetricComplete.of_compact (S.family.metric t)
  have hR : ∀ t ∈ Iio T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro t ht x
    change t < T at ht
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun r hr => D.regular_subset (hreg (hr.trans_lt ht)))
      (fun r hr => hreg (hr.trans ht))
      (fun r hr => hcomplete r (hr.trans_lt ht)) hdim x
  let q := fun t (x : M) => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  have hflatRank (hf : flat) : ∀ t ∈ Iio T, ∀ x, q t x = 0 := by
    intro t ht
    exact curvatureOperatorImageAt_finrank_eq_zero_of_riemannOp_eq_zero
      (S.family.metric t) (hf.2 t ht)
  have hproductRank (hp : product) : ∀ t ∈ Iio T, ∀ x, q t x = 1 := by
    obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, -, -, -, -, -, hprod, hscalar, -⟩ := hp
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
  have hpositiveRank (hp : positive) : ∀ t ∈ Iio T, ∀ x, q t x = 3 := by
    intro t ht x
    have hr := curvatureOperatorImageAt_finrank_eq_of_pos (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ (hp t ht x)
    simpa [q, Topology.Morse.MorseModel] using hr
  have hexclusive : ¬(flat ∧ product) ∧ ¬(flat ∧ positive) ∧ ¬(product ∧ positive) := by
    let s := T - 1
    have hs : s ∈ Iio T := by change s < T; dsimp [s]; linarith
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
  have hUreg : Iio T ⊆ D.regular := hreg
  have hUR : ∀ t ∈ Iio T, ∀ x : UniversalCover M,
      (⟨metricRm04At (U.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := UniversalCover M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := UniversalCover M) := by
    intro t ht x
    change metricAlgebraicCurvatureTensorAt (I := I) (liftedMetric (S.family.metric t)) x ∈ _
    exact (metricAlgebraicCurvatureTensorAt_lifted_mem_curvatureOperatorNonnegativeCone_iff
      (S.family.metric t) x).2 (hR t ht (proj x))
  have hUcomplete : ∀ t ∈ Iio T, RiemannianMetricComplete (U.family.metric t) := by
    intro t ht
    exact S.universalCover_complete t (hcomplete t ht)
  obtain ⟨r, hrset, hbaseRank'⟩ :=
    exists_curvatureOperatorImageAt_finrank_eq_on_ancient_of_compact S hS hreg
  have hbaseRank : ∀ t ∈ Iio T, ∀ x : M, q t x = r := hbaseRank'
  have hrank : ∀ t ∈ Iio T, ∀ x : UniversalCover M,
      Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric t) x
        ⟨metricRm04At (U.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.family.metric t) x⟩) = r := by
    intro t ht x
    exact (curvatureOperatorImageAt_finrank_liftedMetric (S.family.metric t) x hdim).trans
      (hbaseRank t ht (proj x))
  rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hrset) with rfl | rfl | rfl
  · left
    refine ⟨?_, fun t ht =>
      Geometry.Curvature.riemannOp_eq_zero_of_curvatureOperatorImageAt_finrank_eq_zero
        (S.family.metric t) (hbaseRank t ht)⟩
    intro s hs t ht
    change s < T at hs
    change t < T at ht
    obtain ⟨b, hmaxb, hb⟩ := exists_between (max_lt hs ht)
    let a := min s t - 1
    have has : a < s := by dsimp [a]; linarith [min_le_left s t]
    have hat : a < t := by dsimp [a]; linarith [min_le_right s t]
    have hsb : s < b := (le_max_left s t).trans_lt hmaxb
    have htb : t < b := (le_max_right s t).trans_lt hmaxb
    exact metric_eq_on_of_curvatureOperatorImageAt_finrank_eq_zero S hS
      (fun r hr => hreg (hr.2.trans hb))
      (fun r hr => hbaseRank r (hr.2.trans hb)) ⟨has, hsb⟩ ⟨hat, htb⟩
  · have hs : T - 1 ∈ Iio T := by simp
    obtain ⟨N, htop, hcs, hman, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod,
        -, hsol, hscalar, hsectional⟩ :=
      exists_positive_surface_global_product_of_curvatureOperatorImage_rank_eq_one
        U hU isOpen_Iio hUreg (J := Iio T) Set.ordConnected_Iio (Subset.refl _) hs
        (hUcomplete _ hs) hUR hrank
    let _ := htop
    let _ := hcs
    let _ := hman
    let _ := ht2
    let _ := hσ
    let _ : ConnectedSpace N := hconn
    have hcompact : CompactSpace N :=
      compactSpace_of_compact_of_base_scalar_pos_of_pullback_eq_prod
        (S.family.metric (T - 1)) (h (T - 1)) (hcomp _ hs (hUcomplete _ hs)) F
        (hprod _ hs) (fun x =>
          Geometry.Curvature.DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
            hdim (S.family.metric (T - 1)) x (hR _ hs x) (hbaseRank _ hs x))
    have hancient : IsSolutionOn ({ base := { metric := h } } :
        SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
          (M := N) (RealTimeInterval.ancient T)) := by
      apply isSolutionOn_ancient_of_open_interval_restrictions
      intro a b t ht hsub
      exact hsol ht hsub
    right; left
    exact ⟨N, htop, hcs, hman, ht2, hσ, h, F, hcompact, hconn, hsimply,
      (fun t ht => hcomp t ht (hUcomplete t ht)), hancient, hprod, hscalar, hsectional⟩
  · right; right
    intro t ht x beta hbeta
    change t < T at ht
    let u := t - 1
    have hut : u < t := by dsimp [u]; linarith
    have hsub : Icc u t ⊆ Iio T := fun v hv => hv.2.trans_lt ht
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
