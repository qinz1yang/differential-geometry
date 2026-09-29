import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Morse.EuclideanModel
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ProductFactor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.LocalProduct
import DifferentialGeometry.Geometry.Curvature.LocalProduct
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe uH uM

variable {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

theorem exists_positive_surface_global_product_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {U : Set ℝ} (hU : IsOpen U) (hreg : U ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hg : RiemannianMetricComplete (I := I) (S.family.metric t₀))
    (hR : ∀ t ∈ U, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
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
              (∀ t ∈ J, RiemannianMetricComplete (I := I) (S.family.metric t) →
                RiemannianMetricComplete
                  (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              (∀ t ∈ J, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ J, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                HasDerivWithinAt (fun a => (h a).inner y u v)
                  (-2 * ricciTensor (h t) y u v) J t) ∧
              (∀ {a b t : ℝ} (ht : t ∈ Ioo a b), Ioo a b ⊆ J →
                IsSolutionOn ({ base := { metric := h } } :
                  SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                    (M := N) (RealTimeInterval.openInterval a b t ht))) ∧
              (∀ t ∈ J, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ J, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v := by
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, h, F, hconn, hsimply, hcomp, hprod⟩ :=
    exists_global_product_of_curvatureOperatorImage_rank_eq_one
      S hS hU hreg hJ hJsub ht₀ hg hR hrank
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  have hlocal t (ht : t ∈ J) :
      localPullMetric (S.family.metric t) F F.isLocalDiffeomorph =
        (h t).prod (euclideanMetric (E := ℝ)) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    exact hprod t ht
  have hdim₃ : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hdim₂ : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hpositive t (ht : t ∈ J) (y : N) : 0 < metricScalarAt (h t) y := by
    have hn := metricScalarAt_localPull (S.family.metric t) F F.isLocalDiffeomorph (y, 0)
    rw [hlocal t ht, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hn
    rw [hn]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim₃ (S.family.metric t) _ (hR t (hJsub ht) _) (hrank t ht _)
  refine ⟨N, htop, hcs, hmanifold, ht2, hσ, h, F, hconn, hsimply,
    hcomp, hprod, ?_, ?_, hpositive, ?_⟩
  · intro t ht y u v
    exact metric_hasDerivWithinAt_fst_of_local_product S hS F F.isLocalDiffeomorph h
      (fun _ => euclideanMetric (E := ℝ)) ht (hreg (hJsub ht)) hlocal y 0 u v
  · intro a b t ht hsub
    exact isSolutionOn_fst_of_local_product S hS h (fun _ => euclideanMetric (E := ℝ))
      F F.isLocalDiffeomorph 0 ht (hsub.trans (hJsub.trans hreg))
      (fun r hr => hlocal r (hsub hr))
  · intro t ht y u v huv
    exact Geometry.Riemannian.sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
      (h t) hdim₂ y (hpositive t ht y) u v huv

theorem exists_positive_surface_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
    [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {α β : ℝ} (hreg : Ioo α β ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ Ioo α β)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hg : RiemannianMetricComplete (I := I) (S.family.metric t₀))
    (hR : ∀ t ∈ Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
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
              (∀ t ∈ J, RiemannianMetricComplete (I := I) (S.family.metric t) →
                RiemannianMetricComplete
                  (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (h t)) ∧
              (∀ t ∈ J, Diffeomorph.pullbackMetricCross (S.family.metric t) F =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ J, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                HasDerivWithinAt (fun a => (h a).inner y u v)
                  (-2 * ricciTensor (h t) y u v) J t) ∧
              (∀ {a b t : ℝ} (ht : t ∈ Ioo a b), Ioo a b ⊆ J →
                IsSolutionOn ({ base := { metric := h } } :
                  SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
                    (M := N) (RealTimeInterval.openInterval a b t ht))) ∧
              (∀ t ∈ J, ∀ y : N, 0 < metricScalarAt (h t) y) ∧
              ∀ t ∈ J, ∀ (y : N)
                  (u v : TangentSpace
                    𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y),
                LinearIndependent ℝ ![u, v] →
                  0 < Geometry.Riemannian.sectionalCurvature (h t) y u v := by
  exact exists_positive_surface_global_product_of_curvatureOperatorImage_rank_eq_one
    S hS isOpen_Ioo hreg hJ hJsub ht₀ hg hR hrank

private theorem closed_past_product_morse
    [SimplyConnectedSpace M]
    {T t₀ : ℝ} (ht₀ : t₀ ≤ T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed T t₀ ht₀))
    (hS : IsSolutionOn S)
    (hg : ∀ t ≤ T, RiemannianMetricComplete (S.family.metric t))
    (hrank : ∀ t ≤ T, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N),
      let _ := hcs
      ∃ hmanifold : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (G : SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (M := N)
                (RealTimeInterval.infiniteClosed T t₀ ht₀))
              (Phi : (N × ℝ) ≃ₘ⟮(𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ), I⟯ M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧ IsSolutionOn G ∧
              (∀ t ≤ T, RiemannianMetricComplete (G.family.metric t)) ∧
              (∀ t ≤ T, ∀ y : N, 0 < G.scalar t y) ∧
              ∀ t ≤ T, Diffeomorph.pullbackMetricCross (S.family.metric t) Phi =
                (G.family.metric t).prod (euclideanMetric (E := ℝ)) := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hcone (t : ℝ) (ht : t ≤ T) (x : M) :
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
    curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun _ hs => hs.trans ht) (fun _ hs => hs.trans_le ht)
      (fun s hs => hg s (hs.trans ht)) hdim x
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, h, Phi, hconn, hsimply, -, hprod⟩ :=
    exists_global_product_of_curvatureOperatorImage_rank_eq_one S hS
      isOpen_Iio (Subset.refl (Iio T)) ordConnected_Iio (Subset.refl (Iio T))
      (show T - 1 ∈ Iio T by simp only [mem_Iio]; linarith)
      (hg (T - 1) (by linarith))
      (fun t ht => hcone t ht.le) (fun t ht => hrank t ht.le)
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  let P := S.pullback Phi
  have hP : IsSolutionOn P := hS.pullback S Phi
  let G : SolutionOn (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) (M := N)
      (RealTimeInterval.infiniteClosed T t₀ ht₀) :=
    { base := { metric := fun t => (P.family.metric t).sliceFst (0 : ℝ) } }
  have hnegative (t : ℝ) (ht : t < T) :
      P.family.metric t = ((P.family.metric t).sliceFst (0 : ℝ)).prod
        (euclideanMetric (E := ℝ)) := by
    have hp : P.family.metric t = (h t).prod (euclideanMetric (E := ℝ)) := hprod t ht
    have hs : (P.family.metric t).sliceFst (0 : ℝ) = h t := by
      rw [hp]
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [SmoothRiemannianMetric.sliceFst_inner]
      have hz : (euclideanMetric (E := ℝ)).inner (0 : ℝ) 0 0 = 0 := by
        change inner ℝ (0 : ℝ) 0 = 0
        exact inner_zero_left _
      exact (SmoothRiemannianMetric.prod_inner (h t) (euclideanMetric (E := ℝ))
          (x, (0 : ℝ)) (v, 0) (w, 0)).trans
          ((congrArg (fun z : ℝ => (h t).inner x v w + z) hz).trans (add_zero _))
    rw [hs]
    exact hp
  have hclosed (t : ℝ) (ht : t ≤ T) :
      P.family.metric t = ((P.family.metric t).sliceFst (0 : ℝ)).prod
        (euclideanMetric (E := ℝ)) := by
    rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hnegative t hlt
    · exact hP.smoothMetric.eq_sliceFst_prod_at_terminal_of_lt
        (Subset.refl (Iic t)) (euclideanMetric (E := ℝ)) 0 hnegative
  refine ⟨N, htop, hcs, hmanifold, ht2, hσ, G, Phi, hconn, hsimply,
    isSolutionOn_sliceFst_of_prod_euclidean P hP hclosed, ?_, ?_, hclosed⟩
  · intro t ht
    exact RiemannianMetricComplete.sliceFst _ 0
      (Geometry.Metric.riemannianMetricComplete_pullbackMetricCross (hg t ht) Phi)
  · intro t ht y
    have hp := SolutionOn.pullback_scalar S Phi t (y, 0)
    change metricScalarAt (P.family.metric t) (y, 0) = _ at hp
    rw [hclosed t ht, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hp
    change 0 < metricScalarAt ((P.family.metric t).sliceFst (0 : ℝ)) y
    rw [hp]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim _ _ (hcone t ht _) (hrank t ht _)


end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow
open Set Geometry.Curvature Topology.Morse
open scoped _root_.Manifold ContDiff
universe uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_positive_surface_global_product_on_closed_past_of_curvatureOperatorImage_rank_eq_one [SimplyConnectedSpace M]
    {T t₀ : ℝ} (ht₀ : t₀ ≤ T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.infiniteClosed T t₀ ht₀))
    (hS : IsSolutionOn S) (hdim : Module.finrank ℝ E = 3)
    (hg : ∀ t ≤ T, RiemannianMetricComplete (S.family.metric t))
    (hrank : ∀ t ≤ T, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.family.metric t) x)) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N),
      let _ := hcs
      ∃ hmanifold : IsManifold (𝓡 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (G : SolutionOn (I := 𝓡 2) (M := N)
                (RealTimeInterval.infiniteClosed T t₀ ht₀))
              (Phi : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧ IsSolutionOn G ∧
              (∀ t ≤ T, RiemannianMetricComplete (G.family.metric t)) ∧
              (∀ t ≤ T, ∀ y : N, 0 < G.scalar t y) ∧
              ∀ t ≤ T, Diffeomorph.pullbackMetricCross (S.family.metric t) Phi =
                (G.family.metric t).prod (euclideanMetric (E := ℝ)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e : E ≃L[ℝ] MorseModel 3 :=
    (Module.finBasisOfFinrankEq ℝ E hdim).equivFun.toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv e
  let Psi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) (RealTimeInterval.infiniteClosed T t₀ ht₀) :=
    S.pullback Psi.symm
  have hU : IsSolutionOn U := hS.pullback S Psi.symm
  have hcomp (t : ℝ) (ht : t ≤ T) : RiemannianMetricComplete (U.family.metric t) :=
    Geometry.Metric.riemannianMetricComplete_pullbackMetricCross (hg t ht) Psi.symm
  have hr (t : ℝ) (ht : t ≤ T) (x : M) :
      Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (U.family.metric t) x)) = 1 := by
    have hdimJ : Module.finrank ℝ (MorseModel 3) = 3 := by simp [MorseModel]
    refine (metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      (U.family.metric t) x hdimJ).symm.trans ?_
    change DimensionThree.metricCurvatureOperatorRankAt
      (Diffeomorph.pullbackMetricCross (S.family.metric t) Psi.symm) x hdimJ = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      DimensionThree.metricCurvatureOperatorRankAt_localPull _ _ _ _ hdimJ hdim]
    exact (metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      (S.family.metric t) (Psi.symm x) hdim).trans (hrank t ht _)
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, G, Phi, hconn, hsimply, hG, hc, hs, hp⟩ :=
    closed_past_product_morse
      ht₀ U hU hcomp hr
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  let _ := morseModelEuclideanModelChartedSpace 2 N
  let _ := isManifold_morseModelEuclideanModel (n := 2) (M := N)
  let A := morseModelEuclideanModelDiffeomorph (n := 2) (M := N)
  let B := A.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let G' := G.pullback A
  refine ⟨N, htop, inferInstance, inferInstance, ht2, hσ, G',
    B.trans (Phi.trans Psi.symm), hconn, hsimply, hG.pullback G A, ?_, ?_, ?_⟩
  · intro t ht
    exact Geometry.Metric.riemannianMetricComplete_pullbackMetricCross (hc t ht) A
  · intro t ht y
    change 0 < (G.pullback A).scalar t y
    rw [SolutionOn.pullback_scalar]
    exact hs t ht _
  · intro t ht
    rw [← Diffeomorph.pullbackMetricCross_trans,
      ← Diffeomorph.pullbackMetricCross_trans]
    change Diffeomorph.pullbackMetricCross
      (Diffeomorph.pullbackMetricCross (U.family.metric t) Phi) B = _
    rw [hp t ht, Diffeomorph.pullbackMetricCross_prodCongr,
      Diffeomorph.pullbackMetricCross_refl]
    rfl

end DifferentialGeometry.PDE.RicciFlow
