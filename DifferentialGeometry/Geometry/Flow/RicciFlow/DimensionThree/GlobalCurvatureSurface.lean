import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.LocalProduct
import DifferentialGeometry.Geometry.Curvature.LocalProduct
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

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
    exists_global_product_on_interval_of_curvatureOperatorImage_rank_eq_one
      S hS hreg hJ hJsub ht₀ hg hR hrank
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
    rw [hlocal t ht, metricScalarAt_prod,
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

end DifferentialGeometry.PDE.RicciFlow
