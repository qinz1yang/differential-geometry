import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCompatibleBackwardFlow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.OpenPullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem secLower_zero_of_normalized_pullback_metric_convergence
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (hPhi : AdmissiblePinchingFunction Phi)
    (P : MetricCompactLimit (X.toFlowSequence.atTime 0))
    (U : TopologicalSpace.Opens P.limit.M) (hpU : P.limit.basepoint ∈ U)
    (N : ℕ) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (t : ℝ) (ht : t ≤ 0)
    (G : ℕ → SmoothRiemannianMetric I3 U) (g r : SmoothRiemannianMetric I3 U)
    (hsource : ∀ j, (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (j + N)).source)
    (hmetric : ∀ j (x : U) (v w : TangentSpace I3 x),
      (G j).inner x v w =
        ((X.term (P.subseq (j + N))).S.base.metric t).inner
          (P.maps.partialDiffeomorph (j + N) x)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N)) x v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (j + N)) x w))
    (hconv : MetricCInfConvergenceOnCompacts (fun i => G (rho i - N)) g r) :
    SecLower g 0 univ := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Q : PointedRiemannianManifold (I := I3) := {
    M := U
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := ⟨P.limit.basepoint, hpU⟩
    metric := g }
  let f : ℕ → ℕ := fun i => P.subseq (rho i - N + N)
  let F (i : ℕ) := P.maps.partialDiffeomorph (rho i - N + N)
  obtain ⟨Psi, _hPsi, C, hcanonical⟩ :=
    exists_pointed_metric_convergence_of_pullback_on_open
      (X.toFlowSequence.atTime t) P.limit f F U hpU
      (fun i => hsource (rho i - N)) (fun i => P.maps.basepoint_map (rho i - N + N))
      (fun i => G (rho i - N)) g r (fun i => hmetric (rho i - N)) hconv
  have hf : Tendsto f atTop atTop := by
    have heq : f =ᶠ[atTop] fun i => P.subseq (rho i) := by
      filter_upwards [eventually_ge_atTop N] with i hi
      dsimp only [f]
      rw [Nat.sub_add_cancel (hi.trans (hrho.id_le i))]
    exact (P.strictMono.tendsto_atTop.comp hrho.tendsto_atTop).congr' heq.symm
  have htime : ∀ᶠ i in atTop, t ∈ (X.interval (f i)).carrier := by
    filter_upwards [(X.depth_tendsto.comp hf).eventually_ge_atTop (-t)] with i hi
    change -t ≤ X.depth (f i) at hi
    rw [X.carrier_eq]
    exact ⟨by linarith [X.depth_pos (f i)], ht⟩
  have hpinching : ∀ᶠ i in atTop, ∀ y : (X.term (f i)).M,
      curvatureOperatorLowerBoundAt ((X.term (f i)).S.base.metric t) y
        (metricAlgebraicCurvatureTensorAt ((X.term (f i)).S.base.metric t) y)
        (rescalePinchingFunction (X.scale (f i)) Phi
          (metricScalarAt ((X.term (f i)).S.base.metric t) y)) := by
    filter_upwards [htime] with i hi
    intro y
    have h := X.pinching (f i) t hi y
    have hval : ((X.term (f i)).S.base.rm04 t) y =
        metricRm04At ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionFamily.rm04]
      exact metricRm04_apply _ _
    have hK : (X.term (f i)).S.scalar t y =
        metricScalarAt ((X.term (f i)).S.base.metric t) y := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar]
    intro n c v w
    have hh := h n c v w
    simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
      hval, hK] at hh ⊢
    exact hh
  have hmain := sectional_nonnegative_of_pointed_admissible_pinching_eventually
    (X := X.toFlowSequence.atTime t) (L := Q) (F := Psi) C hcanonical hPhi X.scale
    X.scale_pos (X.scale_tendsto.comp hf) hpinching
  intro x _ v w
  have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
    funext i
    fin_cases i <;> simp [vec4]
  simpa only [SecLower, zero_mul, metricRm04StandardAt_apply, hvec] using hmain x v w


theorem exists_compatible_nonnegative_local_backward_flows_on_exhaustion_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
            ConnectedSpace P.limit.M →
            ∃ U : ℕ → TopologicalSpace.Opens P.limit.M,
              (∀ n, (U n : Set P.limit.M) =
                riemannianBallOf (I := I3) P.limit.metric P.limit.basepoint ((n : ℝ) + 1)) ∧
              ExhaustsByOpen (fun n => (U n : Set P.limit.M)) ∧
              (∀ n, IsCompact (closure (U n : Set P.limit.M))) ∧
              ∃ delta : ℕ → ℝ, ∃ hd : ∀ n, 0 < delta n, ∃ N : ℕ → ℕ,
                ∃ S : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
                  (RealTimeInterval.closed (-delta n) 0 (by have := hd n; linarith)),
                  (∀ n i, IsSolutionOn (S n i)) ∧
                  (∀ n i, (U n : Set P.limit.M) ⊆
                    (P.maps.partialDiffeomorph (i + N n)).source) ∧
                  (∀ n i t (x : U n) (v w : TangentSpace I3 x),
                    ((S n i).base.metric t).inner x v w =
                      ((X.term (P.subseq (i + N n))).S.base.metric t).inner
                        (P.maps.partialDiffeomorph (i + N n) x)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x v)
                        (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) x w)) ∧
                  ∃ rho : ℕ → ℕ, StrictMono rho ∧
                    ∃ g : ∀ n, ℝ → SmoothRiemannianMetric I3 (U n),
                      (∀ n, g n 0 = P.limit.metric.restrictOpen (U n)) ∧
                      (∀ n, IsSolutionOn ({ base.metric := g n } :
                        SolutionOn (I := I3) (M := U n)
                          (RealTimeInterval.closed (-delta n / 2) 0
                            (by have := hd n; linarith)))) ∧
                      (∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ,
                        ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
                          ∀ t ∈ Icc (-delta n / 2) 0,
                            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
                              (g n t) (P.limit.metric.restrictOpen (U n)) < epsilon) ∧
                      (∀ n m, ∀ W : TopologicalSpace.Opens P.limit.M,
                        (hWn : W ≤ U n) → (hWm : W ≤ U m) →
                        ∀ t, t ∈ Icc (-delta n / 2) 0 → t ∈ Icc (-delta m / 2) 0 →
                          (g n t).restrictOpenOfSubset hWn =
                            (g m t).restrictOpenOfSubset hWm) ∧
                      (∀ n t, t ∈ Icc (-delta n / 2) 0 → SecLower (g n t) 0 univ) := by
  obtain ⟨epsStar, hepsStar, hmain⟩ :=
    exists_compatible_local_backward_flows_on_exhaustion_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical hconn
  let _ : ConnectedSpace P.limit.M := hconn
  obtain ⟨U, hUeq, hexhausts, hcompact, delta, hd, N, S, hS, hsource, hmetric,
    rho, hrho, g, hg0, hsol, hconv, hoverlap⟩ :=
    hmain eps heps hle sigma hsigma Phi hPhi X P hcanonical hconn
  refine ⟨U, hUeq, hexhausts, hcompact, delta, hd, N, S, hS, hsource, hmetric,
    rho, hrho, g, hg0, hsol, hconv, hoverlap, ?_⟩
  intro n t ht
  have hpU : P.limit.basepoint ∈ U n := by
    change P.limit.basepoint ∈ (U n : Set P.limit.M)
    rw [hUeq n]
    change riemannianEDistOf (I := I3) P.limit.metric P.limit.basepoint P.limit.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  let G : ℕ → SmoothRiemannianMetric I3 (U n) := fun j => (S n j).base.metric t
  have hconv_t : MetricCInfConvergenceOnCompacts
      (fun i => G (rho i - N n)) (g n t)
        (P.limit.metric.restrictOpen (U n)) := by
    intro K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
    refine ⟨j, ?_⟩
    intro i hi
    exact hj i hi t ht
  exact secLower_zero_of_normalized_pullback_metric_convergence X hPhi P (U n) hpU
    (N n) rho hrho t ht.2 G (g n t)
    (P.limit.metric.restrictOpen (U n)) (fun j => hsource n j)
    (fun j x v w => hmetric n j t x v w) hconv_t

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
