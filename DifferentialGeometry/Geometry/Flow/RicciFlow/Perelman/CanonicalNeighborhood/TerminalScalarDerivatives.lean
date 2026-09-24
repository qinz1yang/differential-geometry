import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredSourceBuffer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem exists_eventually_curvDerivNorm_le_of_terminal_scalar_le
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∀ m : ℕ, ∃ C : ℝ,
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in atTop,
            ∀ y : (X.term i).M, (X.term i).S.scalar 0 y ≤ A →
              curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ C := by
  obtain ⟨epsStar, hepsStar, hprop⟩ := exists_uniform_recentered_backward_curvature_bound hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A m
  obtain ⟨r, delta, K, hr, hdelta, hK, hbound⟩ := hprop eps heps hle sigma hsigma Phi hPhi A
  refine ⟨shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * (delta / 2))
    (Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * delta / 2)) *
      (r / 4) * Real.sqrt K) * K / Real.sqrt (delta / 4) ^ m, fun X => ?_⟩
  filter_upwards [hbound X, X.depth_tendsto.eventually_ge_atTop delta]
    with i hi hdepth
  intro y hy
  obtain ⟨hcarrier, hcurv⟩ := hi 0 ⟨by linarith [X.depth_pos i], le_rfl⟩ y hy
  simp only [zero_sub] at hcarrier hcurv
  have hregular : Ioo (-delta) 0 ⊆ (X.interval i).regular := by
    rw [X.regular_eq i]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hcomplete : RiemannianMetricComplete (I := I3)
      ((X.term i).S.base.metric (-(delta / 2))) :=
    ⟨X.complete i _ (hcarrier ⟨by linarith, by linarith⟩)⟩
  have hrm : ∀ t ∈ Icc (-delta) 0, ∀ z ∈
      riemannianClosedBallOf ((X.term i).S.base.metric 0) y r,
      curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) z ≤ K ^ 2 := by
    intro t ht z hz
    have hd : metricDistance ((X.term i).S.base.metric 0) y z ≤ r :=
      ENNReal.toReal_le_of_le_ofReal hr.le hz
    exact (Real.sqrt_le_iff.mp (hcurv z t hd ht).2).2
  exact curvDerivNorm_le_on_terminal_ball_of_curvature_bound (X.term i).S (X.term i).isSolution
    (by simp [ThreeSpace]) hdelta hr hK hcarrier hregular hcomplete y hrm m 0
    ⟨by linarith, le_rfl⟩ y (by
      change riemannianEDistOf ((X.term i).S.base.metric 0) y y ≤ ENNReal.ofReal (r / 2)
      rw [riemannianEDistOf_self]
      exact bot_le)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
