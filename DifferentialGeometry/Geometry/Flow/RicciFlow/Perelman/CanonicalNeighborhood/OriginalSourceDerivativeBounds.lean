import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceLocalWindow

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

theorem RealizedFiniteHorn.exists_original_source_curvature_derivative_bounds
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, ∃ hc : 0 < c, 0 < epsStar ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence, ∀ x : ℕ → H.space,
              ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (x n),
                ∃ threshold : ℕ → ℕ, ∀ n j, threshold n ≤ j →
                  ∃ S : SolutionOn (I := I3) (M := (X.term (H.subseq j)).M)
                    (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                    IsSolutionOn S ∧
                    (∀ t, S.base.metric t =
                      scaleMetric (metricScalarAt H.metric (x n))
                        (zero_lt_one.trans_le (hQ n))
                        ((X.term (H.subseq j)).S.base.metric
                          (t / metricScalarAt H.metric (x n)))) ∧
                    (∀ t ∈ Icc (-(c / 6)) 0, RiemannianMetricComplete (S.base.metric t)) ∧
                    |S.scalar 0 (H.maps j (x n)) - 1| < 1 / ((n : ℝ) + 2) ∧
                    (∀ y : (X.term (H.subseq j)).M, ∀ t ∈ Icc (-(c / 6)) 0,
                      y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / Real.sqrt 3) →
                      S.scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq S t y) ≤ C * (3 + 13 * Phi 1)) ∧
                    ∀ m : ℕ, ∀ t ∈ Icc (-(c / 24)) 0,
                      ∀ y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
                        (c / (2 * Real.sqrt 3)),
                      curvDerivNorm (I := I3) m (S.base.metric t) y ≤ B m := by
  obtain ⟨epsStar, c, C, hc, hepsStar, hC, hsolutions⟩ :=
    RealizedFiniteHorn.exists_original_source_local_solutions hmod
  refine ⟨epsStar, c, C, hc, hepsStar, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi
  let K : ℝ := C * (3 + 13 * Phi 1)
  have hK : 0 < K := mul_pos hC (by linarith [hPhi.pos 1])
  let B : ℕ → ℝ := fun m =>
    shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (K * ((c / 6) / 2))
      (Real.exp (-((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * (c / 6) / 2)) *
        ((c / Real.sqrt 3) / 4) * Real.sqrt K) * K / Real.sqrt ((c / 6) / 4) ^ m
  refine ⟨B, fun m => div_nonneg
    (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK.le)
    (pow_nonneg (Real.sqrt_nonneg _) m), ?_⟩
  intro X H x hQ
  obtain ⟨threshold, hthreshold⟩ :=
    hsolutions eps heps hepsStar' sigma hsigma Phi hPhi X H x hQ
  refine ⟨threshold, ?_⟩
  intro n j hj
  obtain ⟨S, hS, hmetric, hcomplete, hcenter, hcurv⟩ := hthreshold n j hj
  refine ⟨S, hS, hmetric, hcomplete, hcenter, hcurv, ?_⟩
  intro m t ht y hy
  have hcurvSq : ∀ s ∈ Icc (-(c / 6)) 0,
      ∀ z ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
        (c / Real.sqrt 3),
      curvDerivNormSq (I := I3) 0 (S.base.metric s) z ≤ K ^ 2 := by
    intro s hs z hz
    have hb := (hcurv z s hs hz).2
    have hnonneg : 0 ≤ FlowMetricBall.rmNormSq S s z :=
      Tensor0SBundle.normSq0S_nonneg _ _ _ _
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hK.le).2 hb
    rw [Real.sq_sqrt hnonneg] at hsq
    exact hsq
  have hdim : 2 ≤ Module.finrank ℝ ThreeSpace := by simp [ThreeSpace]
  have ht' : t ∈ Icc (-((c / 6) / 4)) 0 := by
    rwa [show (c / 6) / 4 = c / 24 by ring]
  have hy' : y ∈ riemannianClosedBallOf (S.base.metric 0) (H.maps j (x n))
      ((c / Real.sqrt 3) / 2) := by
    rwa [show (c / Real.sqrt 3) / 2 = c / (2 * Real.sqrt 3) by ring]
  exact curvDerivNorm_le_on_terminal_ball_of_curvature_bound S hS hdim
    (by positivity : 0 < c / 6) (by positivity : 0 < c / Real.sqrt 3) hK
    (subset_refl _) (subset_refl _)
    (hcomplete (-((c / 6) / 2)) ⟨by linarith, by linarith⟩)
    (H.maps j (x n)) hcurvSq m t ht' y hy'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
