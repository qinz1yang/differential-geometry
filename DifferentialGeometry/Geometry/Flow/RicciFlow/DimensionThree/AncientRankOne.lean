import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CylinderPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientCurvatureRank
import DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence

noncomputable section

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem rank_le_one_on_closed_past [SimplyConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T a : ℝ} (ha : a < T)
    (hcarrier : Iic T ⊆ D.carrier) (hregular : Iio T ⊆ D.regular)
    (hcomplete : ∀ t ≤ T, RiemannianMetricComplete (S.base.metric t))
    (hbound : ∀ u v : ℝ, u < v → v ≤ T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ C)
    (hpast : ∀ t ≤ a, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 1) :
    ∀ t ≤ T, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≤ 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let D₀ := RealTimeInterval.infiniteClosed a a le_rfl
  let U := S.timeRestrict D₀
  have hU : IsSolutionOn U := isSolutionOn_timeRestrict hS
    (fun r hr => hcarrier (hr.trans ha.le)) (fun r hr => hregular (hr.trans ha))
  obtain ⟨N, htop, hcs, hmanifold, ht2, hσ, G, Phi, hconn, _, _, _, _, hp⟩ :=
    exists_positive_surface_global_product_on_closed_past_of_curvatureOperatorImage_rank_eq_one
      (show a ≤ a from le_rfl) U hU hdim
      (fun t ht => hcomplete t (ht.trans ha.le)) hpast
  let _ := htop
  let _ := hcs
  let _ := hmanifold
  let _ := ht2
  let _ := hσ
  let _ := hconn
  let V := S.pullback Phi
  have hV : IsSolutionOn V := hS.pullback S Phi
  have hdim3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by
    rw [Module.finrank_prod]; simp
  have hcomp (r : ℝ) (hr : r ≤ T) : RiemannianMetricComplete (V.base.metric r) :=
    riemannianMetricComplete_pullbackMetricCross (hcomplete r hr) Phi
  have hRic (r : ℝ) (hr : r ≤ T) (x : N × ℝ) (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ)) x) :
      0 ≤ ricciTensor (V.base.metric r) x v v :=
    ricciTensor_nonnegative_of_curvatureOperator_nonnegative _ x
      (curvatureOperator_nonnegative_of_complete_ancient V hV
        (fun q hq => hcarrier (hq.trans hr)) (fun q hq => hregular (hq.trans_le hr))
        (fun q hq => hcomp q (hq.trans hr)) hdim3 x) v
  have hinit : V.base.metric a = cylinderMetric (G.base.metric a) := by
    change Diffeomorph.pullbackMetricCross (S.base.metric a) Phi = _
    rw [show Diffeomorph.pullbackMetricCross (S.base.metric a) Phi =
      (G.base.metric a).prod (euclideanMetric (E := ℝ)) from hp a le_rfl]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [SmoothRiemannianMetric.prod_inner, cylinderMetric_inner]
    change _ + inner ℝ (v.2 : ℝ) (w.2 : ℝ) = _
    rw [RCLike.inner_apply, conj_trivial, mul_comm]
  have hnegative (t : ℝ) (ht : t < T) (x : M) :
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≤ 1 := by
    by_cases hta : t ≤ a
    · exact (hpast t hta x).le
    have hat : a < t := lt_of_not_ge hta
    have hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ r ∈ Icc (a - 1) t, ∀ y,
        normSq0S (V.base.metric r) y 4 (V.base.rm04 r y) ≤ K := by
      obtain ⟨K, hK, hKbound⟩ := hbound (a - 1) t (by linarith) ht.le
      refine ⟨K, hK, fun r hr y => ?_⟩
      change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric r) Phi) y 4
        (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric r) Phi) y) ≤ K
      rw [riemannNormSq_cross]
      exact hKbound r hr (Phi y)
    have hr := curvatureOperatorImageAt_finrank_le_one_of_initial_cylinder V hV
      (a₀ := a - 1) (by linarith) hat
      (fun r hr => hcarrier (hr.2.trans ht.le))
      (fun r hr => hregular (hr.2.trans_lt ht))
      (hcomp (a - 1) (by linarith)) hcurv
      (fun r hr => hRic r (hr.2.trans ht.le)) (by simp) (G.base.metric a) hinit
      t ⟨hat.le, le_rfl⟩ (Phi.symm x)
    have heq : Module.finrank ℝ (curvatureOperatorImageAt (V.base.metric t) (Phi.symm x)
        (metricAlgebraicCurvatureTensorAt (V.base.metric t) (Phi.symm x))) =
        Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
          (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) := by
      unfold metricAlgebraicCurvatureTensorAt
      rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ _ hdim3,
        ← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ _ hdim]
      change DimensionThree.metricCurvatureOperatorRankAt
        (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi) (Phi.symm x) hdim3 = _
      rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
        DimensionThree.metricCurvatureOperatorRankAt_localPull _ _ _ _ hdim3 hdim]
      simp only [Phi.apply_symm_apply]
    exact heq ▸ hr
  intro t ht x
  have hclosed := isClosed_curvatureOperatorImageAt_finrank_le_on_closed_set S hS hdim x 1
    isClosed_Iic hcarrier
  apply (hclosed.closure_subset ?_).1
  have hsub : Iio T ⊆ {r : ℝ | Module.finrank ℝ
      (curvatureOperatorImageAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) ≤ 1} ∩ Iic T :=
    fun r hr => ⟨hnegative r hr x, (show r < T from hr).le⟩
  apply closure_mono hsub
  rw [closure_Iio]
  exact ht

open Geometry.Riemannian.Topology in
theorem curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_rank_one
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T : ℝ}
    (hcarrier : Iic T ⊆ D.carrier) (hregular : Iio T ⊆ D.regular)
    (hcomplete : ∀ t ≤ T, RiemannianMetricComplete (S.base.metric t))
    (hbound : ∀ u v : ℝ, u < v → v ≤ T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ C)
    {s : ℝ} (hs : s ≤ T) (x₀ : M)
    (hrank : Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric s) x₀
      (metricAlgebraicCurvatureTensorAt (S.base.metric s) x₀)) = 1) :
    ∀ t ≤ T, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hnonflat : ∃ t ≤ T, ∃ x : M, metricRm04At (S.base.metric t) x ≠ 0 := by
    refine ⟨s, hs, x₀, ?_⟩
    intro hz
    have hzero := (DimensionThree.metricCurvatureOperatorRankAt_eq_zero_iff
      (S.base.metric s) x₀ hdim).mpr hz
    rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      (S.base.metric s) x₀ hdim] at hzero
    exact zero_ne_one (hzero.symm.trans hrank)
  have hpositive (t : ℝ) (ht : t ≤ T) (x : M) : 0 < Module.finrank ℝ
      (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) :=
    curvatureOperatorImageAt_finrank_pos_of_complete_ancient_nonflat
      S hS hdim hcarrier hregular hcomplete hbound hnonflat ht x
  have hR (r : ℝ) (hr : r ≤ T) (x : M) :
      metricAlgebraicCurvatureTensorAt (S.base.metric r) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
    curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun q hq => hcarrier (hq.trans hr)) (fun q hq => hregular (hq.trans_le hr))
      (fun q hq => hcomplete q (hq.trans hr)) hdim x
  have hpast (t : ℝ) (ht : t ≤ s - 1) (x : M) :
      Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 1 := by
    have hts : t < s := by linarith
    have hle := curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval
      S hS hdim (a := t - 1) (by linarith) hts
      (fun r hr => hcarrier (hr.2.trans hs))
      (fun r hr => hregular (hr.2.trans_le hs))
      (fun r hr => hR r (hr.2.trans hs)) x x₀
    have hpos := hpositive t (hts.le.trans hs) x
    have hleOne := hle.trans_eq hrank
    exact Nat.le_antisymm hleOne hpos
  let _ : Inhabited M := ⟨x₀⟩
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let _ : SemilocallySimplyConnectedSpace M :=
    manifold_semilocallySimplyConnectedSpace (I := I) (M := M)
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let U := S.universalCover
  have hU : IsSolutionOn U := hS.universalCover S
  have hcomp (t : ℝ) (ht : t ≤ T) : RiemannianMetricComplete (U.base.metric t) :=
    S.universalCover_complete t (hcomplete t ht)
  have hbounded (u v : ℝ) (huv : u < v) (hv : v ≤ T) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc u v, ∀ x : UniversalCover M,
        normSq0S (U.base.metric t) x 4 (metricRm04At (U.base.metric t) x) ≤ C := by
    obtain ⟨C, hC, hb⟩ := hbound u v huv hv
    refine ⟨C, hC, fun t ht x => ?_⟩
    change normSq0S (UniversalCover.liftedMetric (S.base.metric t)) x 4
      (metricRm04At (UniversalCover.liftedMetric (S.base.metric t)) x) ≤ C
    rw [UniversalCover.normSq0S_metricRm04At_liftedMetric]
    exact hb t ht (UniversalCover.proj x)
  have hupper := rank_le_one_on_closed_past U hU hdim (a := s - 1) (by linarith)
    hcarrier hregular hcomp hbounded (fun t ht x =>
      (UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric
        (S.base.metric t) x hdim).trans (hpast t ht (UniversalCover.proj x)))
  intro t ht x
  let y : UniversalCover M := ⟨x, ⟦PathConnectedSpace.somePath x₀ x⟧⟩
  have hy := hupper t ht y
  have heq := UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric
    (S.base.metric t) y hdim
  have hle : Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) ≤ 1 := heq ▸ hy
  have hpos := hpositive t ht x
  omega

end DifferentialGeometry.PDE.RicciFlow
