import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.AffinePullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalRankOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.ProductSlice
import DifferentialGeometry.Geometry.Metric.CompletenessPullback
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Topology.Manifold.SmallDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

section Model

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M] [SimplyConnectedSpace M]

private theorem metric_inner_eq_affine_ricci_model
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b σ : ℝ} (hab : a < b)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete_terminal : RiemannianMetricComplete (S.base.metric b))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (x₀ : M) (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x₀
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x₀)) = 1)
    (hterminal : ∀ x : M, S.scalar b x = σ) :
    ∀ t ∈ Icc a b, ∀ x : M, ∀ v w : TangentSpace I x,
      (S.family.metric t).inner x v w =
        (S.family.metric b).inner x v w +
          2 * (b - t) * ricciTensor (S.family.metric b) x v w := by
  have hdim : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hσ : 0 < σ := by
    have hp := DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim (S.family.metric b) x₀ (hR b hb x₀) hrank
    change 0 < S.scalar b x₀ at hp
    simpa only [hterminal x₀] using hp
  have hcomplete (t : ℝ) (ht : t ∈ Ioc a b) :
      RiemannianMetricComplete (S.base.metric t) := by
    obtain ⟨K, _, hK⟩ := hbound
    exact complete_of_curvature_bound S hS hcar hreg hK ⟨ht.1.le, ht.2⟩ hb
      hcomplete_terminal
  have hmid : (a+b)/2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hr := curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one S hS hdim
    hcar hreg hR (fun t ht => hcomplete t ⟨ht.1,ht.2.le⟩) hbound x₀ hrank
  obtain ⟨N, htop, hcs, hman, ht2, hSigma, h, Phi, hconn, hsimply, hp⟩ :=
    exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one S hS hcar hreg
      hmid (hcomplete _ ⟨hmid.1,hmid.2.le⟩)
      (fun t ht => hR t (Ioo_subset_Icc_self ht))
      (fun t ht => hr t ⟨ht.1,ht.2.le⟩)
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hSigma
  let _ : ConnectedSpace N := hconn
  let P := S.pullback Phi
  have hP : IsSolutionOn P := hS.pullback S Phi
  let k := fun t => (P.family.metric t).sliceFst (0 : ℝ)
  have hprod (t : ℝ) (ht : t ∈ Icc a b) :
      P.family.metric t = (k t).prod (euclideanMetric (E := ℝ)) := by
    have hpt : P.family.metric t = (h t).prod (euclideanMetric (E := ℝ)) := hp t ht
    have hs : k t = h t := by
      apply SmoothRiemannianMetric.ext_inner
      intro y v w
      dsimp only [k]
      erw [SmoothRiemannianMetric.sliceFst_inner, hpt, SmoothRiemannianMetric.prod_inner]
      change (h t).inner y v w + inner ℝ (0 : ℝ) 0 = (h t).inner y v w
      rw [inner_zero_left, add_zero]
    rw [hs]
    exact hpt
  have hscalar (y : N) : P.scalar b (y,0) = σ := by
    change (S.pullback Phi).scalar b (y,0) = σ
    rw [SolutionOn.pullback_scalar]
    exact hterminal _
  have hfactor (y : N) : metricScalarAt (k b) y = σ := by
    have hh := hscalar y
    change metricScalarAt (P.family.metric b) (y,0) = σ at hh
    rw [hprod b hb, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hh
    exact hh
  have hc : RiemannianMetricComplete (k b) :=
    RiemannianMetricComplete.sliceFst (P.family.metric b) (0 : ℝ)
      (RiemannianMetricComplete.pullbackCross (S.family.metric b) Phi
        (hcomplete b ⟨hab,le_rfl⟩))
  have hdim₂ : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hRic : BonnetMyers.RicciBoundedBelow (k b)
      (((Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2) : ℝ)-1)*(σ/2)) := by
    intro y v
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two (k b) hdim₂,
      hfactor, hdim₂]
    norm_num
  let _ : NeZero (Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 2)) :=
    ⟨by rw [hdim₂]; norm_num⟩
  let _ : CompactSpace N := BonnetMyers.bonnet_myers_compactSpace_of_complete_metric
    (k b) hc (by omega) (half_pos hσ) hRic
  apply metric_inner_eq_affine_ricci_of_pullback S.family.metric Phi
  exact product_flow_metric_inner_eq_affine_ricci_of_terminal_scalar_constant P hP hdim₂
    hab hσ.le hcar hreg hprod hscalar

end Model

open DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [SimplyConnectedSpace M]

theorem metric_inner_eq_affine_ricci_of_terminal_rank_one_and_scalar_constant_of_simplyConnected
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b σ : ℝ} (hab : a < b)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (x₀ : M) (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b) x₀
      (metricAlgebraicCurvatureTensorAt (S.family.metric b) x₀)) = 1)
    (hterminal : ∀ x : M, S.scalar b x = σ) :
    ∀ t ∈ Icc a b, ∀ x : M, ∀ v w : TangentSpace I x,
      (S.family.metric t).inner x v w =
        (S.family.metric b).inner x v w +
          2 * (b - t) * ricciTensor (S.family.metric b) x v w := by
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
  have hRU : ∀ t ∈ Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (U.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    intro t ht x
    exact (metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff
      (S.family.metric t) e x).mpr (hR t ht (e x))
  have hcU : RiemannianMetricComplete (U.base.metric b) :=
    RiemannianMetricComplete.pullbackCross (S.family.metric b) e hcomplete
  have hbU : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ K := by
    obtain ⟨K, hK, hbound⟩ := hbound
    refine ⟨K, hK, ?_⟩
    intro t ht x
    change normSq0S (Diffeomorph.pullbackMetricCross (S.family.metric t) e) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.family.metric t) e) x) ≤ K
    rw [DifferentialGeometry.CheegerGromovCompactness.riemannNormSq_cross]
    exact hbound t ht (e x)
  have hrU : Module.finrank ℝ (curvatureOperatorImageAt (U.family.metric b) (e.symm x₀)
      (metricAlgebraicCurvatureTensorAt (U.family.metric b) (e.symm x₀))) = 1 := by
    have hdimP : Module.finrank ℝ
        (TangentSpace 𝓘(ℝ, MorseModel 3) (e.symm x₀)) = 3 := by
      change Module.finrank ℝ (MorseModel 3) = 3
      simp [MorseModel]
    unfold metricAlgebraicCurvatureTensorAt
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ _ hdimP]
    change DimensionThree.metricCurvatureOperatorRankAt
      (Diffeomorph.pullbackMetricCross (S.family.metric b) e) (e.symm x₀) hdimP = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    have hdimN : Module.finrank ℝ (TangentSpace I (e (e.symm x₀))) = 3 := hdim
    have hnat := DimensionThree.metricCurvatureOperatorRankAt_localPull
      (S.family.metric b) e e.isLocalDiffeomorph (e.symm x₀) hdimP hdimN
    apply hnat.trans
    apply (metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      (S.family.metric b) (e (e.symm x₀)) hdimN).trans
    change Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric b)
      (e (e.symm x₀)) (metricAlgebraicCurvatureTensorAt (S.family.metric b) (e (e.symm x₀)))) = 1
    rw [e.apply_symm_apply]
    exact hrank
  have htU (x : P) : U.scalar b x = σ := by
    change (S.pullback e).scalar b x = σ
    rw [SolutionOn.pullback_scalar]
    exact hterminal (e x)
  apply metric_inner_eq_affine_ricci_of_pullback S.family.metric e
  exact metric_inner_eq_affine_ricci_model U hU hab
    hcar hreg hRU hcU hbU (e.symm x₀) hrU htU

end DifferentialGeometry.PDE.RicciFlow
