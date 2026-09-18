import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance sourceCurvatureC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem comparison_constant_le {eps K : ℝ} (heps : 0 ≤ eps)
    (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K) :
    witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2)) ≤ 10 + 2 * K := by
  have hL1 := one_le_witnessLambda heps (by linarith : eps < 1)
  have hL := witnessLambda_le heps4
  have hR := witnessRiemannC_le heps heps4
  have hR0 := witnessRiemannC_nonneg heps (by linarith : eps < 1)
  have hLsq : witnessLambda eps ^ 2 ≤ 16 / 9 := by nlinarith
  have hsum : witnessRiemannC eps + K ≤ 5 + K := by linarith
  have hsum0 : 0 ≤ witnessRiemannC eps + K := add_nonneg hR0 hK
  have hstep := mul_le_mul hLsq hsum hsum0 (by norm_num : (0 : ℝ) ≤ 16 / 9)
  rw [Real.sqrt_sq hK]
  linarith


theorem WindowedModelWitness.source_curvature_bound_at_of_model
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    {s : ℝ} (hs : s ∈ Icc (-modelDepth eps) 0) {y : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps))
    (hrm : W.model.rmNormSq s y ≤ K ^ 2) :
    normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y) 4
      (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) (W.embedding y)) ≤
      sourceCurvatureBound 3 K ^ 2 := by
  classical
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let F := W.embedding
  let h := fun r => W.model.S.base.metric r
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos
  have hR : 0 < modelRadius eps := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hyfull : y ∈ riemannianClosedBallOf (h 0) W.model.basepoint (modelRadius eps) := hy
  have hysrc : y ∈ F.source :=
    W.buffered_ball (riemannianClosedBallOf_mono (h 0) W.model.basepoint
      (le_add_of_nonneg_right zero_le_one) hyfull)
  let y' : sourceOpen F := ⟨y, hysrc⟩
  let : SigmaCompactSpace (sourceOpen F) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (sourceOpen F).isOpen)
  let : SigmaCompactSpace
      (⟨F '' (sourceOpen F : Set W.model.M), image_opens_isOpen F (sourceOpen_subset F)⟩ :
        TopologicalSpace.Opens M) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3
      (image_opens_isOpen F (sourceOpen_subset F)))
  have hcomplete : RiemannianMetricComplete (h 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hmodelnorm : normSq0S (witnessModelMetric F h s) y' 4
      (metricRm04At (witnessModelMetric F h s) y') ≤ K ^ 2 := by
    rw [witnessModelMetric, rmNormSq_restrictOpen (h s) (sourceOpen F) y']
    exact hrm
  have hKb : ∀ a b c : TangentSpace I3 y',
      (witnessModelMetric F h s).inner y'
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessModelMetric F h s)) y' a b c) ≤
        K ^ 2 * (witnessModelMetric F h s).inner y' a a *
          (witnessModelMetric F h s).inner y' b b * (witnessModelMetric F h s).inner y' c c :=
    fun a b c => riemannOp_normSq_le_of_rmNormSq_le (witnessModelMetric F h s) y' hmodelnorm a b c
  let Cop := witnessLambda eps ^ 2 * (witnessRiemannC eps + Real.sqrt (K ^ 2))
  have hT2 : ∀ a b c : TangentSpace I3 y',
      Real.sqrt ((witnessPullbackMetric F ghat s).inner y'
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F ghat s)) y' a b c)
        (riemannOp (cov := LeviCivita (witnessPullbackMetric F ghat s)) y' a b c)) ≤
        Cop * Real.sqrt ((witnessPullbackMetric F ghat s).inner y' a a) *
          Real.sqrt ((witnessPullbackMetric F ghat s).inner y' b b) *
          Real.sqrt ((witnessPullbackMetric F ghat s).inner y' c c) := by
    intro a b c
    exact W.comparison.riemannOp_norm_le (h 0) hcomplete W.model.basepoint hR
      W.eps_pos.le W.eps_lt_one (by have hh := five_le_modelOrder W.eps_pos heps4; omega)
      hs hyfull (sq_nonneg K) hKb a b c
  have hCop0 : 0 ≤ Cop := mul_nonneg (sq_nonneg _)
    (add_nonneg (witnessRiemannC_nonneg W.eps_pos.le W.eps_lt_one) (Real.sqrt_nonneg _))
  have hCople : Cop ≤ 10 + 2 * K := comparison_constant_le W.eps_pos.le heps4 hK
  have hpull := rmNormSq_le_of_riemannOp_norm_le (witnessPullbackMetric F ghat s) y' hCop0 hT2
  have hnat : normSq0S (witnessPullbackMetric F ghat s) y' 4
      (metricRm04At (witnessPullbackMetric F ghat s) y') =
      normSq0S (ghat s) (F y) 4 (metricRm04At (ghat s) (F y)) := by
    rw [witnessPullbackMetric, rmNormSq_openPullbackMetric F (sourceOpen F)
      (sourceOpen_subset F) (ghat s) y']
  rw [hnat] at hpull
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hpull
  have hsq : Cop ^ 2 ≤ (10 + 2 * K) ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ (3 : ℝ) ^ 4)
  change normSq0S (ghat s) (F y) 4 (metricRm04At (ghat s) (F y)) ≤ _
  unfold sourceCurvatureBound
  norm_num at hpull hscale ⊢
  nlinarith

theorem WindowedModelWitness.source_curvature_bound_of_model
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    {s : ℝ} (hs : s ∈ Icc (-(4 : ℝ)) 0) {z : M}
    (hz : z ∈ W.embedding ''
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2) :
    normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
      (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
      sourceCurvatureBound 3 K ^ 2 := by
  have hRtwo : 2 ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos heps4
    rwa [modelRadius_quarter] at hh
  have hdepth : 4 ≤ modelDepth eps := by
    have hh := modelDepth_anti W.eps_pos heps4
    norm_num [modelDepth] at hh ⊢
    exact hh
  obtain ⟨y, hy, rfl⟩ := hz
  exact W.source_curvature_bound_at_of_model heps4 hK ⟨by linarith [hs.1], hs.2⟩
    (riemannianClosedBallOf_mono _ _ hRtwo hy) (hmodel s hs y hy)

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.source_unitBall_compact_subset
    {eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4)
    {s : ℝ} (hs : s ∈ Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x 1) ∧
      riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos s) x 1 ⊆
        W.embedding '' riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2 := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let B := riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos
  have hRtwo : 2 ≤ modelRadius eps := by
    have hh := modelRadius_anti W.eps_pos heps4
    rwa [modelRadius_quarter] at hh
  have hdepth : 4 ≤ modelDepth eps := by
    have hh := modelDepth_anti W.eps_pos heps4
    norm_num [modelDepth] at hh ⊢
    exact hh
  have hs' : s ∈ Icc (-modelDepth eps) 0 := ⟨by linarith [hs.1], hs.2⟩
  have hBcompact : IsCompact B := by
    apply RiemannianMetricComplete.closedEBall_isCompact
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have hBfull : B ⊆ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) :=
    riemannianClosedBallOf_mono _ _ hRtwo
  have hBsource : B ⊆ W.embedding.source :=
    hBfull.trans ((riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have hcapture : riemannianClosedBallOf (ghat s) (W.embedding W.model.basepoint) 1 ⊆
      W.embedding '' B := by
    apply closedBall_subset_image_of_metric_lower (W.model.S.base.metric 0)
      (ghat s) W.embedding W.model.basepoint (L := (3 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hBcompact hBsource
    intro y hy v
    have htime := ancientModel_metric_zero_le W.model W.model_ancient hs.2 y v
    have hlower := (W.comparison.equivalence s hs' y (hBfull hy) v).1
    rw [W.comparison.pullback_eq s y (hBfull hy) (fun _ => v)] at hlower
    have href0 := inner_self_nonneg (W.model.S.base.metric s) y v
    have hquarter : (3 / 4 : ℝ) * (W.model.S.base.metric s).inner y v v ≤
        (ghat s).inner (W.embedding y) (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) := by
      exact (mul_le_mul_of_nonneg_right (by linarith : (3 / 4 : ℝ) ≤ 1 - eps) href0).trans hlower
    have hnonneg := inner_self_nonneg (ghat s) (W.embedding y) (mfderiv I3 I3 W.embedding y v)
    nlinarith
  rw [W.base_map] at hcapture
  have himageCompact : IsCompact (W.embedding '' B) := hBcompact.image_of_continuousOn
    (W.embedding.contMDiffOn_toFun.continuousOn.mono hBsource)
  exact ⟨himageCompact.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist (ghat s) x) continuous_const) hcapture, hcapture⟩


theorem WindowedModelWitness.unitBall_compact_curvature_bound
    {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2)
    {a : ℝ} (ha : a ∈ Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x 1) ∧
      ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ z ∈
        riemannianClosedBallOf (rescaledMetric S t (S.scalar t x) W.scalar_pos a) x 1,
        normSq0S (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z 4
          (metricRm04At (rescaledMetric S t (S.scalar t x) W.scalar_pos s) z) ≤
          sourceCurvatureBound 3 K ^ 2 := by
  obtain ⟨hcompact, hcapture⟩ := W.source_unitBall_compact_subset heps4 ha
  exact ⟨hcompact, fun s hs z hz => W.source_curvature_bound_of_model heps4 hK hmodel hs (hcapture hz)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
