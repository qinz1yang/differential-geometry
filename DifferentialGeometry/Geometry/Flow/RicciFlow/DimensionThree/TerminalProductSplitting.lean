import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.TerminalRankOne
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator
import DifferentialGeometry.Geometry.Metric.Product.Completeness

set_option autoImplicit false
noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

universe uE uH uM
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [SimplyConnectedSpace M]

theorem exists_surface_product_on_closed_interval_of_terminal_rank_one
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {a b : ℝ} (hab : a < b)
    (hcar : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ t ∈ Icc a b, ∀ x,
      metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hcomplete : RiemannianMetricComplete (S.base.metric b))
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (x₀ : M) (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric b) x₀
      (metricAlgebraicCurvatureTensorAt (S.base.metric b) x₀)) = 1) :
    ∃ (N : Type uM) (_ : TopologicalSpace N)
      (hcs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N),
      let _ := hcs
      ∃ hmanifold : IsManifold (𝓡 2) ∞ N,
        let _ := hmanifold
        ∃ ht2 : T2Space N,
          let _ := ht2
          ∃ hSigma : SigmaCompactSpace N,
            let _ := hSigma
            ∃ (h : ℝ → SmoothRiemannianMetric (𝓡 2) N)
              (Phi : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), I⟯ M),
              ConnectedSpace N ∧ SimplyConnectedSpace N ∧
              (∀ t ∈ Icc a b, Diffeomorph.pullbackMetricCross (S.base.metric t) Phi =
                (h t).prod (euclideanMetric (E := ℝ))) ∧
              (∀ t ∈ Icc a b, RiemannianMetricComplete (h t)) ∧
              ∀ t ∈ Ioc a b, ∀ y : N, 0 < metricScalarAt (h t) y := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hb : b ∈ Icc a b := ⟨hab.le,le_rfl⟩
  have hcomp (t : ℝ) (ht : t ∈ Icc a b) : RiemannianMetricComplete (S.base.metric t) := by
    obtain ⟨K,_,hK⟩ := hbound
    exact complete_of_curvature_bound S hS hcar hreg hK ht hb hcomplete
  have hr := curvatureOperatorImageAt_finrank_eq_one_of_terminal_rank_one S hS hdim
    hcar hreg hR (fun t ht => hcomp t ⟨ht.1.le,ht.2.le⟩) hbound x₀ hrank
  let e : E ≃L[ℝ] MorseModel 3 :=
    (Module.finBasisOfFinrankEq ℝ E hdim).equivFun.toContinuousLinearEquiv
  let J := I.transContinuousLinearEquiv e
  let Psi := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Psi.symm
  have hU : IsSolutionOn U := hS.pullback S Psi.symm
  have hcompU (t : ℝ) (ht : t ∈ Icc a b) : RiemannianMetricComplete (U.base.metric t) :=
    Geometry.Metric.riemannianMetricComplete_pullbackMetricCross (hcomp t ht) Psi.symm
  have hRU (t : ℝ) (ht : t ∈ Ioo a b) (x : M) :
      metricAlgebraicCurvatureTensorAt (U.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    exact (metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff
      (S.family.metric t) Psi.symm x).mpr (hR t ⟨ht.1.le,ht.2.le⟩ _)
  have hrU (t : ℝ) (ht : t ∈ Ioo a b) (x : M) :
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
      (S.family.metric t) (Psi.symm x) hdim).trans (hr t ⟨ht.1,ht.2.le⟩ _)
  have hmid : (a+b)/2 ∈ Ioo a b := ⟨by linarith,by linarith⟩
  obtain ⟨N,htop,hcs,hman,ht2,hSigma,h,F,hconn,hsimply,hprod⟩ :=
    exists_global_product_on_Icc_of_curvatureOperatorImage_rank_eq_one U hU hcar hreg
      hmid (hcompU _ ⟨hmid.1.le,hmid.2.le⟩) hRU hrU
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hSigma
  let _ := morseModelEuclideanModelChartedSpace 2 N
  let _ := isManifold_morseModelEuclideanModel (n := 2) (M := N)
  let A := morseModelEuclideanModelDiffeomorph (n := 2) (M := N)
  let B := A.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let Phi := B.trans (F.trans Psi.symm)
  let k := fun t => Diffeomorph.pullbackMetricCross (h t) A
  have hk (t : ℝ) (ht : t ∈ Icc a b) :
      Diffeomorph.pullbackMetricCross (S.base.metric t) Phi = (k t).prod (euclideanMetric (E := ℝ)) := by
    rw [← Diffeomorph.pullbackMetricCross_trans,← Diffeomorph.pullbackMetricCross_trans]
    change Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross (U.base.metric t) F) B = _
    have hp : Diffeomorph.pullbackMetricCross (U.base.metric t) F = (h t).prod (euclideanMetric (E := ℝ)) := hprod t ht
    rw [hp,Diffeomorph.pullbackMetricCross_prodCongr,Diffeomorph.pullbackMetricCross_refl]
  refine ⟨N,htop,inferInstance,inferInstance,ht2,hSigma,k,Phi,hconn,hsimply,hk,?_,?_⟩
  · intro t ht
    have hh := Geometry.Metric.riemannianMetricComplete_pullbackMetricCross (hcomp t ht) Phi
    rw [hk t ht] at hh
    exact RiemannianMetricComplete.fst_of_prod hh (0 : ℝ)
  · intro t ht y
    have hh := metricScalarAt_localPull (S.base.metric t) Phi Phi.isLocalDiffeomorph (y,0)
    rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric,hk t ⟨ht.1.le,ht.2⟩,
      metricScalarAt_productMetric,metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1),add_zero] at hh
    rw [hh]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim _ _ (hR t ⟨ht.1.le,ht.2⟩ _) (hr t ht _)

end DifferentialGeometry.PDE.RicciFlow
