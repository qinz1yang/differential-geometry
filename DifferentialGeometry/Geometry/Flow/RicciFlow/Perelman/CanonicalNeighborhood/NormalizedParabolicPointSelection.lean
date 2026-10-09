import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedPointSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedCurvatureWindows

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_parabolic_point_selection_of_not_boundedAtDistance {kappa : ℝ}
    (hkappa : 0 < kappa) :
    ∃ epsStar tau C : ℝ, 0 < epsStar ∧ 0 < tau ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X →
            ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, StrictMono f ∧
              ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ),
                let Q := fun i => (X.term (f i)).S.scalar 0 (x i)
                (∀ i, 0 < r i ∧ r i < D + 1 ∧ 0 < Q i) ∧
                Tendsto Q atTop atTop ∧ Tendsto (fun i => Q i * r i ^ 2) atTop atTop ∧
                (∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
                  metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D + 1) ∧
                ∀ᶠ i in atTop, Icc (-tau / Q i) 0 ⊆ (X.interval (f i)).carrier ∧
                  ∀ t ∈ Icc (-tau / Q i) 0, ∀ y,
                    metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
                      Real.sqrt (FlowMetricBall.rmNormSq (X.term (f i)).S t y) ≤ C * Q i := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hprop⟩ :=
    exists_parabolic_curvature_bound_at_terminal_scalar_scale.{u} hkappa
  refine ⟨epsStar, c / 2, 2 * C, hepsStar, by positivity, by positivity, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hfail
  obtain ⟨D, hD, f, hf, x, r, hr, hQ, hQr, hcontrol⟩ :=
    X.exists_terminal_scalar_point_selection hfail
  let Q : ℕ → ℝ := fun i => (X.term (f i)).S.scalar 0 (x i)
  refine ⟨D, hD, f, hf, x, r, (fun i => ⟨(hr i).1, (hr i).2.1, (hr i).2.2.2⟩),
    hQ, hQr, (fun i y hy => (hcontrol i y hy).1), ?_⟩
  filter_upwards [hf.tendsto_atTop.eventually (hprop eps heps hle sigma hsigma Phi hPhi X),
    hQ.eventually_ge_atTop 1] with i hi hQi
  have hQi' : 1 ≤ Q i := hQi
  have hQpos : 0 < Q i := (hr i).2.2.2
  have htime : -(c / 2) / Q i = -c / (2 * Q i) := by ring
  dsimp only [Q] at htime
  have hcenter := hi (2 * Q i) (by linarith) (x i) (by change Q i ≤ 2 * Q i; linarith)
  refine ⟨by simpa only [Q, htime] using hcenter.1, ?_⟩
  intro t ht y hy
  have hyt : (X.term (f i)).S.scalar 0 y ≤ 2 * Q i := (hcontrol i y hy).2
  have hlocal := hi (2 * Q i) (by linarith) y hyt
  have hmem : y ∈ riemannianClosedBallOf ((X.term (f i)).S.base.metric 0) y
      (c / Real.sqrt (2 * Q i)) := by
    change riemannianEDistOf _ y y ≤ _
    rw [riemannianEDistOf_self]
    exact zero_le
  have hb := hlocal.2 t (by simpa only [Q, htime] using ht) y hmem
  exact hb.trans_eq (by ring)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
