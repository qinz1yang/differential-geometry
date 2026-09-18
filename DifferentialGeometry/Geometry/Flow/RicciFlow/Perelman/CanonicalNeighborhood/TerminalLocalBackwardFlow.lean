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

theorem exists_local_pullback_solutions_of_slab_curvature_bound
    {X : FlowSequence.{u}} (P : MetricCompactLimit (X.atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    {width depthBound : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (p : P.limit.M) {radius : ℝ} (hradius : 0 ≤ radius) {C₀ : ℝ}
    (hslab : ∀ᶠ i in atTop,
      Icc (-depthBound) 0 ⊆ (X.interval (P.subseq i)).carrier ∧
      Ioo (-depthBound) 0 ⊆ (X.interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-depthBound) 0,
        ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1),
          PointedFlowData.rmNormSq (X.term (P.subseq i)) t
            (P.maps.partialDiffeomorph i x) ≤ C₀)
    (U : TopologicalSpace.Opens P.limit.M)
    (hU : (U : Set P.limit.M) ⊆
      riemannianClosedBallOf (I := I3) P.limit.metric p radius) :
    ∃ N : ℕ, ∃ S : ℕ → SolutionOn (I := I3) (M := U)
      (RealTimeInterval.closed (-width) 0 (by linarith)),
      (∀ i, IsSolutionOn (S i)) ∧
      (∀ i, (U : Set P.limit.M) ⊆ (P.maps.partialDiffeomorph (i + N)).source) ∧
      (∀ i t (x : U) (v w : TangentSpace I3 x),
        ((S i).base.metric t).inner x v w =
          ((X.term (P.subseq (i + N))).S.base.metric t).inner
            (P.maps.partialDiffeomorph (i + N) x)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w)) ∧
      MetricCInfConvergenceOnCompacts (fun i => (S i).base.metric 0)
        (P.limit.metric.restrictOpen U) (P.limit.metric.restrictOpen U) ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
        ∀ i m t, t ∈ Icc (-width) 0 → ∀ x : U,
          curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  obtain ⟨C, hC, hjets⟩ :=
    source_curvature_jets_uniform_on_closed_ball_of_compact_curvature_bound
      P hcanonical hw hwd p hradius hslab
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete P.limit P.limit_complete⟩
  obtain ⟨Ns, hs⟩ := P.maps.source_subset (hcomplete.closedEBall_isCompact p radius)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hslab.and hjets).and (eventually_ge_atTop Ns))
  have hsource (i : ℕ) : (U : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N)).source :=
    hU.trans (hs (i + N) (hN (i + N) (by omega)).2)
  let D := RealTimeInterval.closed (-width) 0 (by linarith : -width ≤ 0)
  have hpull (i : ℕ) : ∃ S : SolutionOn (I := I3) (M := U) D,
      IsSolutionOn S ∧ ∀ t (x : U) (v w : TangentSpace I3 x),
        (S.base.metric t).inner x v w =
          ((X.term (P.subseq (i + N))).S.base.metric t).inner
            (P.maps.partialDiffeomorph (i + N) x)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x v)
            (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N)) x w) := by
    obtain ⟨S', hS', hmetric⟩ := KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (X.term (P.subseq (i + N))).S (X.term (P.subseq (i + N))).isSolution
      (P.maps.partialDiffeomorph (i + N)) U (hsource i)
    refine ⟨S'.timeRestrict D, isSolutionOn_timeRestrict hS' ?_ ?_, hmetric⟩
    · exact (Icc_subset_Icc (by linarith) le_rfl).trans (hN (i + N) (by omega)).1.1.1
    · exact (Ioo_subset_Ioo (by linarith) le_rfl).trans (hN (i + N) (by omega)).1.1.2.1
  choose S hS hmetric using hpull
  refine ⟨N, S, hS, hsource, hmetric, ?_, C, hC, ?_⟩
  · exact metricCInfConvergenceOnCompacts_of_pointed_pullback
      P.maps P.convergence.metrics hcanonical U N hsource
      (fun i => (S i).base.metric 0) (fun i => hmetric i 0)
  · intro i m t ht x
    have he := @curvDerivNorm_eq_of_partialDiffeomorph_restriction ThreeSpace ThreeSpace
      P.limit.M (X.term (P.subseq (i + N))).M _ _ _ _ I3
      P.limit.topology P.limit.charted P.limit.smooth P.limit.t2
      (X.term (P.subseq (i + N))).topology (X.term (P.subseq (i + N))).charted
      (X.term (P.subseq (i + N))).smooth (X.term (P.subseq (i + N))).t2
      (P.maps.partialDiffeomorph (i + N)) U (hsource i) ((S i).base.metric t)
      ((X.term (P.subseq (i + N))).S.base.metric t) (hmetric i t) m x
    have hnorm := DifferentialGeometry.CheegerGromovCompactness.curvNormSq_eq
      (I := I3) (X.term (P.subseq (i + N))).S m t
      (P.maps.partialDiffeomorph (i + N) x)
    exact he.trans_le ((congrArg Real.sqrt hnorm).trans_le
      ((hN (i + N) (by omega)).1.2 m t ht x (hU x.property)))


theorem exists_local_pullback_solutions_of_terminal_scalar_bound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ A : ℝ, ∃ delta : ℝ, ∃ hd : 0 < delta,
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ P : MetricCompactLimit (X.toFlowSequence.atTime 0),
              (∀ i, P.convergence.metrics.domain i =
                CanonicalMetricCompactness.canonicalSourceData P.maps i) →
              (∀ x : P.limit.M, metricScalarAt P.limit.metric x ≤ A) →
              ∀ p : P.limit.M, ∀ radius : ℝ, 0 ≤ radius →
                ∀ U : TopologicalSpace.Opens P.limit.M,
                  (U : Set P.limit.M) ⊆
                    riemannianClosedBallOf (I := I3) P.limit.metric p radius →
                  ∃ N : ℕ, ∃ S : ℕ → SolutionOn (I := I3) (M := U)
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
                    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
                      ∀ i m t, t ∈ Icc (-delta) 0 → ∀ x : U,
                        curvDerivNorm m ((S i).base.metric t) x ≤ C m := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_eventually_curvature_bound_of_terminal_metric_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi A
  obtain ⟨depthBound, B, hdepth, _hB, hcurv⟩ := hbound eps heps hle sigma hsigma Phi hPhi A
  refine ⟨depthBound / 2, half_pos hdepth, ?_⟩
  intro X P hcanonical hscalar p radius hradius U hU
  have hcomplete : RiemannianMetricComplete (I := I3) P.limit.metric :=
    ⟨MetricComplete.complete P.limit P.limit_complete⟩
  have hslab : ∀ᶠ i in atTop,
      Icc (-depthBound) 0 ⊆ (X.interval (P.subseq i)).carrier ∧
      Ioo (-depthBound) 0 ⊆ (X.interval (P.subseq i)).regular ∧
      ∀ t ∈ Icc (-depthBound) 0,
        ∀ x ∈ riemannianClosedBallOf (I := I3) P.limit.metric p (radius + 1),
          PointedFlowData.rmNormSq (X.term (P.subseq i)) t
            (P.maps.partialDiffeomorph i x) ≤ B := by
    filter_upwards [hcurv X P.limit P.subseq P.strictMono P.maps P.convergence.metrics
      hcanonical _ (hcomplete.closedEBall_isCompact p (radius + 1))
      (fun x _ => hscalar x)] with i hi
    refine ⟨hi.2.1, hi.2.2.1, ?_⟩
    intro t ht x hx
    exact (rmNormSq_eq_curvDerivNormSq X (P.subseq i) t
      (P.maps.partialDiffeomorph i x)).le.trans (hi.2.2.2 t ht x hx)
  exact exists_local_pullback_solutions_of_slab_curvature_bound P hcanonical
    (half_pos hdepth) (half_lt_self hdepth) p hradius hslab U hU

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
    obtain ⟨S', hS', hmetric⟩ := KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (X.term (P.subseq (i + N))).S (X.term (P.subseq (i + N))).isSolution
      (P.maps.partialDiffeomorph (i + N)) U (hsourceU i)
    exact ⟨S'.timeRestrict D, isSolutionOn_timeRestrict hS'
      (hN (i + N) (by omega)).1.1
        (hN (i + N) (by omega)).1.2.1, hmetric⟩
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
