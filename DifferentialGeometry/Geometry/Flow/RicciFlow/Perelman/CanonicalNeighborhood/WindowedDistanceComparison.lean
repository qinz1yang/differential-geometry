import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessSpatialBuffer

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

theorem WindowedModelWitness.metricDistance_bounds_on_model_ball
    {delta kappa rho : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (hdelta : delta ≤ 1 / 4) (hrho : 0 ≤ rho) (hbuffer : 8 * rho ≤ modelRadius delta) :
    ∀ a ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho,
      ∀ b ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho,
        Real.sqrt (1 - delta) * metricDistance (W.model.S.base.metric 0) a b ≤
            Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t) (W.embedding a) (W.embedding b) ∧
          Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t) (W.embedding a) (W.embedding b) ≤
            Real.sqrt (1 + delta) * metricDistance (W.model.S.base.metric 0) a b := by
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hR : 0 < modelRadius delta := inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos)
  have hcomplete : RiemannianMetricComplete (W.model.S.base.metric 0) :=
    ⟨MetricComplete.complete (W.model.atTime 0) (W.model_ancient.complete 0 (by simp))⟩
  have hcpt := RiemannianMetricComplete.closedEBall_isCompact hcomplete W.model.basepoint
    (modelRadius delta)
  have hsource : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius delta) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hequiv : ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint
      (modelRadius delta), ∀ v : TangentSpace I3 y,
      (1 - delta) * (W.model.S.base.metric 0).inner y v v ≤
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner (W.embedding y)
            (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) ∧
        (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner (W.embedding y)
            (mfderiv I3 I3 W.embedding y v) (mfderiv I3 I3 W.embedding y v) ≤
          (1 + delta) * (W.model.S.base.metric 0).inner y v v := by
    intro y hy v
    have hh := W.comparison.equivalence 0 ht0 y hy v
    rw [W.comparison.pullback_eq 0 y hy (fun _ => v)] at hh
    exact hh
  have hlower : (3 : ℝ) / 4 ≤ Real.sqrt (1 - delta) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hupper : Real.sqrt (1 + delta) ≤ (3 : ℝ) / 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have hroom : Real.sqrt (1 + delta) * (3 * rho) <
      Real.sqrt (1 - delta) * modelRadius delta := by
    have hlo := mul_le_mul_of_nonneg_right hlower hR.le
    have hup := mul_le_mul_of_nonneg_right hupper (by positivity : 0 ≤ 3 * rho)
    nlinarith
  have hh := crossModel_metricDistance_transfer (W.model.S.base.metric 0)
    (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) W.embedding W.model.basepoint
    hR W.eps_pos.le W.eps_lt_one hrho hcpt hsource hequiv hroom
  simpa only [rescaledMetric, parabolicTime_zero, metricDistance, edistOf_scale,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg (S.scalar t x))] using hh

theorem WindowedModelWitness.metricDistance_ge_on_image
    {delta kappa rho H : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness delta kappa S x t)
    (hdelta : delta ≤ 1 / 4) (hrho : 0 ≤ rho) (hbuffer : 8 * rho ≤ modelRadius delta)
    {A : Set W.model.M}
    (hA : A ⊆ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint rho)
    (hfar : ∀ y ∈ A, 2 * H ≤ metricDistance (W.model.S.base.metric 0) W.model.basepoint y) :
    ∀ y ∈ W.embedding '' A,
      H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y := by
  rintro _ ⟨y, hy, rfl⟩
  have hp : W.model.basepoint ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint rho := by
    change riemannianEDistOf (W.model.S.base.metric 0) W.model.basepoint W.model.basepoint ≤ _
    rw [riemannianEDistOf_self]
    exact bot_le
  have hh := (W.metricDistance_bounds_on_model_ball hdelta hrho hbuffer
    W.model.basepoint hp y (hA hy)).1
  rw [W.base_map] at hh
  have hhalf : (1 : ℝ) / 2 ≤ Real.sqrt (1 - delta) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  have hdist : 0 ≤ metricDistance (W.model.S.base.metric 0) W.model.basepoint y :=
    ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hhalf hdist
  have hbound : H ≤ Real.sqrt (S.scalar t x) * metricDistance (S.base.metric t) x (W.embedding y) := by
    linarith [hfar y hy]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr W.scalar_pos)).mpr (by
    simpa only [mul_comm] using hbound)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
