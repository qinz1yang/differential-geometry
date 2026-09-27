import DifferentialGeometry.Topology.Manifold.SmallDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientRankPersistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Morse
open scoped _root_.Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [SimplyConnectedSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_positive_surface_product_of_rank_one_of_complete_ancient
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ u v, u < v → v < T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C)
    {s : ℝ} (hs : s < T) (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric s) x₀
      ⟨metricRm04At (S.family.metric s) x₀,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric s) x₀⟩) = 1) :
    ∃ (N : Type) (_ : TopologicalSpace N) (hcs : ChartedSpace (MorseModel 2) N),
      let _ := hcs
      ∃ hman : IsManifold 𝓘(ℝ, MorseModel 2) ∞ N,
        let _ := hman
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hσ : SigmaCompactSpace N,
            let _ := hσ
            ∃ (h : ℝ → SmoothRiemannianMetric 𝓘(ℝ, MorseModel 2) N)
              (Phi : (N × ℝ) ≃ₘ⟮(𝓘(ℝ, MorseModel 2)).prod 𝓘(ℝ, ℝ), I⟯ M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t < T, RiemannianMetricComplete (h t)) ∧
              IsSolutionOn ({ base := { metric := h } } :
                SolutionOn (I := 𝓘(ℝ, MorseModel 2)) (M := N) (RealTimeInterval.ancient T)) ∧
              (∀ t < T, Diffeomorph.pullbackMetricCross (S.family.metric t) Phi =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t < T, ∀ y : N, 0 < metricScalarAt (h t) y) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] MorseModel 3 := ContinuousLinearEquiv.ofFinrankEq (by
    simpa only [MorseModel, Module.finrank_fin_fun] using hdim)
  obtain ⟨P, htopP, hcsP, hmanP, ⟨e⟩⟩ :=
    DifferentialGeometry.Manifold.exists_small_diffeomorph (M := M) (I := I) L
  let _ := htopP
  let _ := hcsP
  let _ := hmanP
  let _ : T2Space P := e.toHomeomorph.isEmbedding.t2Space
  let _ : SigmaCompactSpace P := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let _ : SimplyConnectedSpace P := e.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let U := S.pullback e
  have hU : IsSolutionOn U := hS.pullback S e
  have hUc (t : ℝ) (ht : t < T) : RiemannianMetricComplete (U.family.metric t) :=
    RiemannianMetricComplete.pullbackCross (S.family.metric t) e (hcomplete t ht)
  have hUb (u v : ℝ) (huv : u < v) (hv : v < T) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : P,
        normSq0S (U.family.metric t) x 4 (metricRm04At (U.family.metric t) x) ≤ C := by
    obtain ⟨C, hC, hb⟩ := hbound u v huv hv
    refine ⟨C, hC, ?_⟩
    intro t ht x
    change normSq0S (Diffeomorph.pullbackMetricCross (S.family.metric t) e) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.family.metric t) e) x) ≤ C
    rw [DifferentialGeometry.CheegerGromovCompactness.riemannNormSq_cross]
    exact hb t ht (e x)
  have hrU : Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric s) (e.symm x₀)
      ⟨metricRm04At (U.family.metric s) (e.symm x₀),
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (U.family.metric s) (e.symm x₀)⟩) = 1 := by
    have hdimP : Module.finrank ℝ
        (TangentSpace 𝓘(ℝ, MorseModel 3) (e.symm x₀)) = 3 := by
      change Module.finrank ℝ (MorseModel 3) = 3
      simp [MorseModel]
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      _ _ hdimP]
    change DimensionThree.metricCurvatureOperatorRankAt
      (Diffeomorph.pullbackMetricCross (S.family.metric s) e) (e.symm x₀) hdimP = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      DimensionThree.metricCurvatureOperatorRankAt_localPull _ _ _ _ hdimP hdim,
      metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
    rw [e.apply_symm_apply]
    exact hrank
  obtain ⟨N, htop, hcs, hman, ht2, hσ, h, Phi, hconn, hsimply, hc, hp, _, _, hsol, hpos, _⟩ :=
    exists_positive_surface_global_product_of_curvatureOperator_rank_one_of_complete_ancient
      U hU hreg hUc hUb hs (e.symm x₀) hrU
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hσ
  refine ⟨N, htop, hcs, hman, ht2, hσ, h, Phi.trans e, hconn, hsimply, hc, hsol, ?_, hpos⟩
  intro t ht
  rw [← Diffeomorph.pullbackMetricCross_trans]
  exact hp t ht

end DifferentialGeometry.PDE.RicciFlow
