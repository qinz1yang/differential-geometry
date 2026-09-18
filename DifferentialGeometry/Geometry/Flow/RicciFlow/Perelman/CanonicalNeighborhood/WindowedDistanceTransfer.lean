import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

theorem WindowedModelWitness.metricDistance_embedding_bounds
    {delta kappa rho : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hrho : 0 ≤ rho)
    (hroom : Real.sqrt (1 + delta) * (3 * rho) <
      Real.sqrt (1 - delta) * modelRadius delta)
    {y z : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho)
    (hz : z ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho) :
    Real.sqrt (1 - delta) * metricDistance (W.model.S.base.metric 0) y z ≤
        Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t)
          (W.embedding y) (W.embedding z) ∧
      Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t)
          (W.embedding y) (W.embedding z) ≤
        Real.sqrt (1 + delta) * metricDistance (W.model.S.base.metric 0) y z := by
  let g := W.model.S.base.metric 0
  let ghat := rescaledMetric S t (S.scalar t x) W.scalar_pos 0
  have hcomplete : RiemannianMetricComplete g :=
    ⟨MetricComplete.complete (W.model.atTime 0) (W.model_ancient.complete 0 (by simp))⟩
  have hc : IsCompact (riemannianClosedBallOf g W.model.basepoint (modelRadius delta)) :=
    RiemannianMetricComplete.closedEBall_isCompact hcomplete W.model.basepoint _
  have hsource : riemannianClosedBallOf g W.model.basepoint (modelRadius delta) ⊆
      W.embedding.source :=
    (riemannianClosedBallOf_mono g W.model.basepoint
      (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hequiv : ∀ a ∈ riemannianClosedBallOf g W.model.basepoint (modelRadius delta),
      ∀ v : TangentSpace I3 a,
      (1 - delta) * g.inner a v v ≤
          ghat.inner (W.embedding a) (mfderiv I3 I3 W.embedding a v)
            (mfderiv I3 I3 W.embedding a v) ∧
        ghat.inner (W.embedding a) (mfderiv I3 I3 W.embedding a v)
            (mfderiv I3 I3 W.embedding a v) ≤ (1 + delta) * g.inner a v v := by
    intro a ha v
    have h := W.comparison.equivalence 0 ht0 a ha v
    rw [W.comparison.pullback_eq 0 a ha (fun _ => v)] at h
    exact h
  have hR : 0 < modelRadius delta := by
    exact inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have h := crossModel_toReal_transfer g ghat W.embedding W.model.basepoint hR
    W.eps_pos.le W.eps_lt_one hrho hc hsource hequiv hroom y hy z hz
  change Real.sqrt (1 - delta) * metricDistance g y z ≤
      metricDistance ghat (W.embedding y) (W.embedding z) ∧
    metricDistance ghat (W.embedding y) (W.embedding z) ≤
      Real.sqrt (1 + delta) * metricDistance g y z at h
  simpa only [g, ghat, rescaledMetric, parabolicTime_zero, metricDistance, edistOf_scale,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using h

theorem WindowedModelWitness.metricDistance_embedding_bounds_of_small_tolerance
    {delta kappa rho : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hdelta : delta ≤ 1 / 2)
    (hrho : 0 ≤ rho) (hroom : 6 * rho < modelRadius delta)
    {y z : W.model.M}
    (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho)
    (hz : z ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho) :
    metricDistance (W.model.S.base.metric 0) y z / 2 ≤
        Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t)
          (W.embedding y) (W.embedding z) ∧
      Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t)
          (W.embedding y) (W.embedding z) ≤
        2 * metricDistance (W.model.S.base.metric 0) y z := by
  have hminus : 0 < 1 - delta := by linarith
  have hplus : 0 ≤ 1 + delta := by linarith [W.eps_pos]
  have hsminus : 0 < Real.sqrt (1 - delta) := Real.sqrt_pos.mpr hminus
  have hsplus : 0 ≤ Real.sqrt (1 + delta) := Real.sqrt_nonneg _
  have hsminusSq := Real.sq_sqrt hminus.le
  have hsplusSq := Real.sq_sqrt hplus
  have hratio : Real.sqrt (1 + delta) ≤ 2 * Real.sqrt (1 - delta) := by
    nlinarith
  have hroom' : Real.sqrt (1 + delta) * (3 * rho) <
      Real.sqrt (1 - delta) * modelRadius delta := by
    calc
      _ ≤ (2 * Real.sqrt (1 - delta)) * (3 * rho) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = Real.sqrt (1 - delta) * (6 * rho) := by ring
      _ < _ := mul_lt_mul_of_pos_left hroom hsminus
  obtain ⟨hlower, hupper⟩ := W.metricDistance_embedding_bounds hrho hroom' hy hz
  have hdist : 0 ≤ metricDistance (W.model.S.base.metric 0) y z := ENNReal.toReal_nonneg
  have hlow : 1 / 2 ≤ Real.sqrt (1 - delta) := by nlinarith
  have hupp : Real.sqrt (1 + delta) ≤ 2 := by nlinarith
  constructor
  · have h := mul_le_mul_of_nonneg_right hlow hdist
    linarith
  · exact hupper.trans (mul_le_mul_of_nonneg_right hupp hdist)

theorem WindowedModelWitness.metricDistance_image_bounds
    {delta kappa rho H C : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t) (hdelta : delta ≤ 1 / 2)
    (hrho : 0 ≤ rho) (hroom : 6 * rho < modelRadius delta)
    (A : Set W.model.M)
    (hball : A ⊆
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho)
    (hdepth : ∀ y ∈ A,
      2 * H ≤ metricDistance (W.model.S.base.metric 0) W.model.basepoint y)
    (hdiam : ∀ y ∈ A,
      ∀ z ∈ A,
      2 * metricDistance (W.model.S.base.metric 0) y z ≤ C) :
    A ⊆ W.embedding.source ∧
      (∀ y ∈ W.embedding '' A,
      H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y) ∧
      ∀ y ∈ W.embedding '' A,
        ∀ z ∈ W.embedding '' A,
        metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x) := by
  have hQ : 0 < Real.sqrt (S.scalar t x) := Real.sqrt_pos.mpr W.scalar_pos
  have hbase : W.model.basepoint ∈ riemannianClosedBallOf
      (W.model.S.base.metric 0) W.model.basepoint rho := by
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint
      W.model.basepoint ≤ ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact bot_le
  have hsource : A ⊆ W.embedding.source :=
    hball.trans ((riemannianClosedBallOf_mono (W.model.S.base.metric 0)
      W.model.basepoint (show rho ≤ modelRadius delta + 1 by linarith)).trans W.buffered_ball)
  refine ⟨hsource, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := (W.metricDistance_embedding_bounds_of_small_tolerance hdelta hrho hroom
      hbase (hball hy)).1
    rw [W.base_map] at h
    apply (div_le_iff₀ hQ).2
    have hd := hdepth y hy
    nlinarith
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have h := (W.metricDistance_embedding_bounds_of_small_tolerance hdelta hrho hroom
      (hball hy) (hball hz)).2
    apply (le_div_iff₀ hQ).2
    have hd := hdiam y hy z hz
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
