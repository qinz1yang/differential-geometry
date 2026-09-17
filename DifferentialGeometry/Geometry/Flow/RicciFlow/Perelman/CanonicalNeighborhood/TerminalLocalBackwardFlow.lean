import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.FixedDomain
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_local_pullback_solutions_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∀ U : TopologicalSpace.Opens P.limit.M,
                  (U : Set P.limit.M) ⊆
                    riemannianClosedBallOf (I := I3) P.limit.metric p radius →
                  ∃ delta : ℝ, ∃ hd : 0 < delta, ∃ N : ℕ,
                    ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                      (RealTimeInterval.closed (-delta) 0 (by linarith)),
                      (∀ i, IsSolutionOn (S i)) ∧
                      (∀ i, (U : Set P.limit.M) ⊆
                        (P.maps.partialDiffeomorph (i + N)).source) ∧
                      (∀ i t (x : U) (v w : TangentSpace I3 x),
                        ((S i).base.metric t).inner x v w =
                          ((X.term (P.subseq (i + N))).S.base.metric t).inner
                            (P.maps.partialDiffeomorph (i + N) x)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w)) ∧
                      (∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                        ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3)
                            (X.term (P.subseq (i + N))).S m t
                            (P.maps.partialDiffeomorph (i + N) x)) ≤ C m) := by
  obtain ⟨epsStar, hepsStar, hjets⟩ :=
    exists_eventually_curvature_jets_on_closed_ball_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete (I := I3) P.limit P.limit_complete⟩
  let K := riemannianClosedBallOf (I := I3) P.limit.metric p radius
  have hK : IsCompact K := hcomplete.closedEBall_isCompact p radius
  obtain ⟨delta, hdelta, C, hC, hbound⟩ :=
    hjets eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius
  obtain ⟨Nsource, hsource⟩ := P.maps.source_subset hK
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hbound.and (eventually_ge_atTop Nsource))
  have hsourceU (i : ℕ) : (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N)).source :=
    hU.trans (hsource (i + N) (hN (i + N) (by omega)).2)
  let D := RealTimeInterval.closed (-delta) 0 (by linarith : -delta ≤ 0)
  have hpull (i : ℕ) :
      ∃ S : SolutionOn (I := I3) (M := U) D,
        IsSolutionOn S ∧ ∀ t (x : U) (v w : TangentSpace I3 x),
          (S.base.metric t).inner x v w =
            ((X.term (P.subseq (i + N))).S.base.metric t).inner
              (P.maps.partialDiffeomorph (i + N) x)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w) := by
    let F := P.maps.partialDiffeomorph (i + N)
    let V : TopologicalSpace.Opens (X.term (P.subseq (i + N))).M :=
      ⟨F '' (U : Set P.limit.M), image_opens_isOpen F (hsourceU i)⟩
    let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
    let e : U ≃ₘ⟮I3, I3⟯ V := PartialDiffeomorph.toOpensDiffeo F (hsourceU i)
    let S₀ := solutionOnPullback (I := I3)
      (solutionOnRestrictOpen (I := I3) (X.term (P.subseq (i + N))).S V) e
    have hS₀ : IsSolutionOn S₀ :=
      isSolutionOn_pullback (I := I3) _
        (isSolutionOn_restrictOpen (I := I3)
          (X.term (P.subseq (i + N))).S (X.term (P.subseq (i + N))).isSolution V) e
    refine ⟨S₀.timeRestrict D,
      isSolutionOn_timeRestrict hS₀ (hN (i + N) (by omega)).1.1
        (hN (i + N) (by omega)).1.2.1, ?_⟩
    intro t x v w
    change (Diffeomorph.pullbackMetric
      (((X.term (P.subseq (i + N))).S.base.metric t).restrictOpen V) e).inner x v w = _
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact congrArg₂
      (fun v' w' => ((X.term (P.subseq (i + N))).S.base.metric t).inner (F x) v' w')
      (PartialDiffeomorph.mfderiv_toOpensDiffeo F (hsourceU i) x v)
      (PartialDiffeomorph.mfderiv_toOpensDiffeo F (hsourceU i) x w)
  choose S hS hmet using hpull
  exact ⟨delta, hdelta, N, S, hS, hsourceU, hmet, C, hC,
    fun i m t ht x => (hN (i + N) (by omega)).1.2.2 m t ht x (hU x.property)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_local_pullback_curvature_bounds_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∀ U : TopologicalSpace.Opens P.limit.M,
                  (U : Set P.limit.M) ⊆
                    riemannianClosedBallOf (I := I3) P.limit.metric p radius →
                  ∃ delta : ℝ, ∃ hd : 0 < delta, ∃ N : ℕ,
                    ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                      (RealTimeInterval.closed (-delta) 0 (by linarith)),
                      (∀ i, IsSolutionOn (S i)) ∧
                      (∀ i, (U : Set P.limit.M) ⊆
                        (P.maps.partialDiffeomorph (i + N)).source) ∧
                      (∀ i t (x : U) (v w : TangentSpace I3 x),
                        ((S i).base.metric t).inner x v w =
                          ((X.term (P.subseq (i + N))).S.base.metric t).inner
                            (P.maps.partialDiffeomorph (i + N) x)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w)) ∧
                      MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
                        (P.limit.metric.restrictOpen U) (P.limit.metric.restrictOpen U) ∧
                      (∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                        ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                          curvDerivNorm m ((S i).base.metric t) x ≤ C m) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_pullback_solutions_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  obtain ⟨delta, hd, N, S, hS, hsource, hmetric, C, hC, hjet⟩ :=
    hlocal eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  have hterminal := metricCInfConvergenceOnCompacts_of_pointed_pullback
    P.maps P.convergence.metrics hcanonical U N hsource
    (fun i => (S i).base.metric 0) (fun i => hmetric i 0)
  refine ⟨delta, hd, N, S, hS, hsource, hmetric, hterminal, C, hC, ?_⟩
  intro i m t ht x
  let _ : TopologicalSpace (X.term (P.subseq (i + N))).M :=
    (X.term (P.subseq (i + N))).topology
  let _ : ChartedSpace ThreeSpace (X.term (P.subseq (i + N))).M :=
    (X.term (P.subseq (i + N))).charted
  let _ : IsManifold I3 ∞ (X.term (P.subseq (i + N))).M :=
    (X.term (P.subseq (i + N))).smooth
  let _ : T2Space (X.term (P.subseq (i + N))).M :=
    (X.term (P.subseq (i + N))).t2
  have he : curvDerivNorm m ((S i).base.metric t) x =
      curvDerivNorm m ((X.term (P.subseq (i + N))).S.base.metric t)
        (P.maps.partialDiffeomorph (i + N) x) :=
    @curvDerivNorm_eq_of_partialDiffeomorph_restriction ThreeSpace ThreeSpace
      P.limit.M (X.term (P.subseq (i + N))).M _ _ _ _ I3
      P.limit.topology P.limit.charted P.limit.smooth P.limit.t2
      (X.term (P.subseq (i + N))).topology (X.term (P.subseq (i + N))).charted
      (X.term (P.subseq (i + N))).smooth (X.term (P.subseq (i + N))).t2
      (P.maps.partialDiffeomorph (i + N)) U (hsource i) ((S i).base.metric t)
      ((X.term (P.subseq (i + N))).S.base.metric t) (hmetric i t) m x
  have hs := DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq
    (I := I3) (X.term (P.subseq (i + N))).S m t
      (P.maps.partialDiffeomorph (i + N) x)
  exact he.trans_le ((congrArg Real.sqrt hs).trans_le (hjet i m t ht x))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_local_metric_subsequence_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∀ U : TopologicalSpace.Opens P.limit.M,
                  (U : Set P.limit.M) ⊆
                    riemannianClosedBallOf (I := I3) P.limit.metric p radius →
                  ∃ delta : ℝ, ∃ hd : 0 < delta, ∃ N : ℕ,
                    ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                      (RealTimeInterval.closed (-delta) 0 (by linarith)),
                      (∀ i, IsSolutionOn (S i)) ∧
                      (∀ i, (U : Set P.limit.M) ⊆
                        (P.maps.partialDiffeomorph (i + N)).source) ∧
                      (∀ i t (x : U) (v w : TangentSpace I3 x),
                        ((S i).base.metric t).inner x v w =
                          ((X.term (P.subseq (i + N))).S.base.metric t).inner
                            (P.maps.partialDiffeomorph (i + N) x)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w)) ∧
                      MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
                        (P.limit.metric.restrictOpen U) (P.limit.metric.restrictOpen U) ∧
                      (∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                        ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                          curvDerivNorm m ((S i).base.metric t) x ≤ C m) ∧
                      (∃ rho : ℕ → ℕ, StrictMono rho ∧
                        ∃ g : ℝ → SmoothRiemannianMetric I3 U,
                          g 0 = P.limit.metric.restrictOpen U ∧ ∀ K : Set U, IsCompact K → ∀ p : ℕ,
                            ∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℕ,
                              ∀ i ≥ n, ∀ t ∈ Icc (-delta / 2) 0,
                                metricDerivNormSupOn K p ((S (rho i)).base.metric t)
                                  (g t) (P.limit.metric.restrictOpen U) < epsilon) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_pullback_curvature_bounds_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨delta, hd, N, S, hS, hsource, hmetric, hterminal, C, hC, hjet⟩ :=
    hlocal eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  have hslab : Icc (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hextract := exists_metric_subsequence_on_closed_interval_of_terminal_convergence
    S hS (P.limit.metric.restrictOpen U) (show -delta / 2 < 0 by linarith)
    hslab hreg hterminal (by
      intro K _hK q
      exact ⟨C q, hC q, Eventually.of_forall fun i t ht x _ =>
        hjet i q t ⟨by linarith [ht.1], ht.2⟩ x⟩)
  exact ⟨delta, hd, N, S, hS, hsource, hmetric, hterminal,
    ⟨C, hC, hjet⟩, hextract⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem exists_local_backward_flow_of_terminal_metric_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
            (∀ i, P.convergence.metrics.domain i =
              CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∀ U : TopologicalSpace.Opens P.limit.M,
                  (U : Set P.limit.M) ⊆
                    riemannianClosedBallOf (I := I3) P.limit.metric p radius → p ∈ U →
                  ∃ delta : ℝ, ∃ hd : 0 < delta, ∃ N : ℕ,
                    ∃ S : ℕ → SolutionOn (I := I3) (M := U)
                      (RealTimeInterval.closed (-delta) 0 (by linarith)),
                      (∀ i, IsSolutionOn (S i)) ∧
                      (∀ i, (U : Set P.limit.M) ⊆
                        (P.maps.partialDiffeomorph (i + N)).source) ∧
                      (∀ i t (x : U) (v w : TangentSpace I3 x),
                        ((S i).base.metric t).inner x v w =
                          ((X.term (P.subseq (i + N))).S.base.metric t).inner
                            (P.maps.partialDiffeomorph (i + N) x)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
                            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w)) ∧
                      MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
                        (P.limit.metric.restrictOpen U) (P.limit.metric.restrictOpen U) ∧
                      (∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                        ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                          curvDerivNorm m ((S i).base.metric t) x ≤ C m) ∧
                      (∃ rho : ℕ → ℕ, StrictMono rho ∧
                        ∃ g : ℝ → SmoothRiemannianMetric I3 U,
                          g 0 = P.limit.metric.restrictOpen U ∧
                          IsSolutionOn ({ base.metric := g } : SolutionOn (I := I3) (M := U)
                            (RealTimeInterval.closed (-delta / 2) 0 (by linarith))) ∧
                          ∀ K : Set U, IsCompact K → ∀ p : ℕ,
                            ∀ epsilon : ℝ, 0 < epsilon → ∃ n : ℕ,
                              ∀ i ≥ n, ∀ t ∈ Icc (-delta / 2) 0,
                                metricDerivNormSupOn K p ((S (rho i)).base.metric t)
                                  (g t) (P.limit.metric.restrictOpen U) < epsilon) := by
  obtain ⟨epsStar, hepsStar, hlocal⟩ :=
    exists_local_metric_subsequence_of_terminal_metric_convergence hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU hpU
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨delta, hd, N, S, hS, hsource, hmetric, hterminal, hjets,
    rho, hrho, g, hg0, hconv⟩ :=
    hlocal eps heps hle sigma hsigma Phi hPhi X P hcanonical p radius hradius U hU
  let Q : PointedRiemannianManifold (I := I3) := {
    M := U
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := ⟨p, hpU⟩
    metric := P.limit.metric.restrictOpen U }
  have hslab : Icc (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-delta / 2) 0 ⊆
      (RealTimeInterval.closed (-delta) 0 (by linarith)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hsolution := isSolutionOn_of_fixed_domain_metric_convergence Q S hS
    (show -delta / 2 < 0 by linarith) hslab (Ioo_subset_Ico_self.trans hreg)
    rho hrho g hconv (by
      intro K hK p
      exact Eventually.of_forall fun i => by
        obtain ⟨L, _hL, hb⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
          (S i) (hS i) (show -delta / 2 < 0 by linarith) hslab hreg Q.metric hK p
        exact ⟨L, fun s hs t ht q hq x hx => hb q hq s hs t ht x hx⟩)
  exact ⟨delta, hd, N, S, hS, hsource, hmetric, hterminal, hjets,
    rho, hrho, g, hg0, hsolution, hconv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
