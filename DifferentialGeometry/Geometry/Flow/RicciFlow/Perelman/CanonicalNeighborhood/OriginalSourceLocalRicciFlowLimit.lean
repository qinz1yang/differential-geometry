import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceLocalMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FixedDomain

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle RealizedFiniteHorn.metricSpace
  RealizedFiniteHorn.charted RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem RealizedFiniteHorn.exists_original_source_local_ricci_flow_limit
    {kappa : ℝ} (hkappa : 0 < kappa) (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar c C : ℝ, ∃ hc : 0 < c, 0 < epsStar ∧ 0 < C ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∃ B : ℕ → ℝ, ∃ eta : ℝ, (∀ m, 0 ≤ B m) ∧ 0 < eta ∧
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ H : RealizedFiniteHorn X.toFlowSequence,
              ∀ ray : EndRay H.horn.endpoint, ∀ d : ℕ → ℝ, ∀ N : ℕ,
                ∀ hQ : ∀ n, 1 ≤ metricScalarAt H.metric (ray.point (d (N + n))),
                  ∀ j : ℕ → ℕ, StrictMono j →
                    ∃ psi : ℕ → ℕ, StrictMono psi ∧ StrictMono (H.subseq ∘ j ∘ psi) ∧
                    let hq := fun n => zero_lt_one.trans_le (hQ n)
                    let Y := H.rescaledSourceSeq ray d N (j ∘ psi) hq
                    ∃ S : ∀ n, SolutionOn (I := I3) (M := (Y.obj n).M)
                      (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                    (∀ n, IsSolutionOn (S n)) ∧
                    (∀ n t, (S n).base.metric t =
                      scaleMetric (metricScalarAt H.metric (ray.point (d (N + n)))) (hq n)
                        ((X.term (H.subseq (j (psi n)))).S.base.metric
                          (t / metricScalarAt H.metric (ray.point (d (N + n)))))) ∧
                    (∀ n, (S n).base.metric 0 = (Y.obj n).metric) ∧
                    (∀ n, ∀ t ∈ Icc (-(c / 6)) 0,
                      RiemannianMetricComplete ((S n).base.metric t)) ∧
                    (∀ n, |(S n).scalar 0 (Y.obj n).basepoint - 1| < 1 / ((n : ℝ) + 2)) ∧
                    (∀ n, ∀ y : (Y.obj n).M, ∀ t ∈ Icc (-(c / 6)) 0,
                      y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                        (c / Real.sqrt 3) →
                      (S n).scalar t y ≤ 12 ∧
                      Real.sqrt (FlowMetricBall.rmNormSq (S n) t y) ≤ C * (3 + 13 * Phi 1)) ∧
                    (∀ n m, ∀ t ∈ Icc (-(c / 24)) 0,
                      ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                        (c / (2 * Real.sqrt 3)),
                      curvDerivNorm (I := I3) m ((S n).base.metric t) y ≤ B m) ∧
                    (∀ n, ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
                      (c / (2 * Real.sqrt 3)), HasInjRadiusAt (Y.obj n) y eta) ∧
                    ∃ phi : ℕ → ℕ, StrictMono phi ∧
                      StrictMono (H.subseq ∘ j ∘ psi ∘ phi) ∧
                      ∃ Q : Type, ∃ top : TopologicalSpace Q, letI := top
                      ∃ charts : ChartedSpace ThreeSpace Q, letI := charts
                      ∃ hman : IsManifold I3 ∞ Q, letI := hman
                      ∃ hT2 : T2Space Q, letI := hT2
                      ∃ hsecond : SecondCountableTopology Q, letI := hsecond
                      ∃ (gQ : SmoothRiemannianMetric I3 Q)
                        (V U : TopologicalSpace.Opens Q) (q : Q)
                        (F : ∀ k, Q → (Y.obj (phi k)).M)
                        (G : ℕ → SmoothRiemannianMetric I3 U),
                        IsCompact (closure (V : Set Q)) ∧ closure (V : Set Q) ⊆ U ∧ q ∈ V ∧
                        (∀ᶠ k in atTop, ∀ (z : U) (v w : TangentSpace I3 z),
                          (G k).inner z v w = (Y.obj (phi k)).metric.inner (F k z)
                            (mfderiv I3 I3 (F k) (z : Q) v)
                            (mfderiv I3 I3 (F k) (z : Q) w)) ∧
                        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen U) (gQ.restrictOpen U) ∧
                        ∃ offset : ℕ,
                          ∃ f : ∀ k, PartialDiffeomorph I3 I3 Q (Y.obj (phi (k + offset))).M ∞,
                            (∀ k, closure (U : Set Q) ⊆ (f k).source ∧
                              EqOn (f k) (F (k + offset)) (f k).source ∧
                              f k q = (Y.obj (phi (k + offset))).basepoint ∧
                              (∀ y : (Y.obj (phi (k + offset))).M,
                                riemannianEDistOf (Y.obj (phi (k + offset))).metric
                                  (Y.obj (phi (k + offset))).basepoint y ≤
                                    ENNReal.ofReal (c / (4 * Real.sqrt 3)) →
                                y ∈ f k '' closure (V : Set Q)) ∧
                              f k '' closure (V : Set Q) ⊆
                                {y | riemannianEDistOf (Y.obj (phi (k + offset))).metric
                                  (Y.obj (phi (k + offset))).basepoint y <
                                    ENNReal.ofReal (c / (2 * Real.sqrt 3))}) ∧
                            ∃ hVU : V ≤ U,
                              ∃ T : ℕ → SolutionOn (I := I3) (M := V)
                                (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)),
                              (∀ k, IsSolutionOn (T k)) ∧
                              (∀ k t (z : V) (v w : TangentSpace I3 z),
                                ((T k).base.metric t).inner z v w =
                                  ((S (phi (k + offset))).base.metric t).inner (f k z)
                                    (mfderiv I3 I3 (f k) z v) (mfderiv I3 I3 (f k) z w)) ∧
                              (∀ k, (T k).base.metric 0 =
                                (G (k + offset)).restrictOpenOfSubset hVU) ∧
                              ∃ rho : ℕ → ℕ, StrictMono rho ∧
                                StrictMono (fun k => H.subseq (j (psi (phi (rho k + offset))))) ∧
                                ∃ g : ℝ → SmoothRiemannianMetric I3 V,
                                  g 0 = gQ.restrictOpen V ∧
                                  IsSolutionOn ({ base.metric := g } : SolutionOn
                                    (I := I3) (M := V)
                                    (RealTimeInterval.closed (-(c / 24)) 0 (by linarith))) ∧
                                  ∀ K : Set V, IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ,
                                    0 < epsilon → ∃ k0 : ℕ, ∀ k ≥ k0,
                                      ∀ t ∈ Icc (-(c / 24)) 0,
                                        metricDerivNormSupOn K p ((T (rho k)).base.metric t)
                                          (g t) (gQ.restrictOpen V) < epsilon := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨epsStar, c, C, hc, hepsStar, hC, hlimits⟩ :=
    RealizedFiniteHorn.exists_original_source_local_metric_limit hkappa hmod
  refine ⟨epsStar, c, C, hc, hepsStar, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi
  obtain ⟨B, eta, hB, heta, hlimits'⟩ :=
    hlimits eps heps hepsStar' sigma hsigma Phi hPhi
  refine ⟨B, eta, hB, heta, ?_⟩
  intro X H ray d N hQ j hj
  obtain ⟨psi, hpsi, horiginal, S, hS, hmetric, hmetric0, hcomplete, hcenter,
    hcurv, hderiv, hinj, phi, hphi, horiginal', Q, top, charts, hman, hT2, hsecond,
    gQ, V, U, q, F, G, hVcompact, hVUclosure, hqV, hG, hGconv, hmaps⟩ :=
      hlimits' X H ray d N hQ j hj
  let := top
  let := charts
  let := hman
  let := hT2
  let := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace ThreeSpace Q
  let _ : SigmaCompactSpace Q := sigmaCompactSpace_of_locallyCompact_secondCountable
  let hq := fun n => zero_lt_one.trans_le (hQ n)
  let Y := H.rescaledSourceSeq ray d N (j ∘ psi) hq
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hVU : V ≤ U := fun _ hz => hVUclosure (subset_closure hz)
  obtain ⟨offset, hoffset⟩ := eventually_atTop.1 (hG.and hmaps)
  have htail := fun k => hoffset (k + offset) (Nat.le_add_left offset k)
  choose f hfsource hfEq hfbase hfcapture hfimage using fun k => (htail k).2
  have hVsource : ∀ k, (V : Set Q) ⊆ (f k).source :=
    fun k _ hz => hfsource k (subset_closure (hVU hz))
  choose T hT hTmetric using fun k =>
    KappaSolutions.exists_local_solution_of_partialDiffeomorph
      (S (phi (k + offset))) (hS (phi (k + offset))) (f k) V (hVsource k)
  have hterminal : ∀ k, (T k).base.metric 0 =
      (G (k + offset)).restrictOpenOfSubset hVU := by
    intro k
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    have hnear : (f k : Q → (Y.obj (phi (k + offset))).M) =ᶠ[𝓝 (z : Q)]
        F (k + offset) :=
      Filter.eventuallyEq_of_mem ((f k).open_source.mem_nhds (hVsource k z.property))
        (fun y hy => hfEq k hy)
    rw [hTmetric k 0 z v w, hmetric0 (phi (k + offset)),
      hnear.eq_of_nhds, hnear.mfderiv_eq, SmoothRiemannianMetric.restrictSubset_inner]
    exact ((htail k).1 (TopologicalSpace.Opens.inclusion hVU z) v w).symm
  have hTcurv : ∀ k m, ∀ t ∈ Icc (-(c / 24)) 0, ∀ z : V,
      curvDerivNorm m ((T k).base.metric t) z ≤ B m := by
    intro k m t ht z
    rw [curvDerivNorm_eq_of_partialDiffeomorph_restriction
      (f k) V (hVsource k) ((T k).base.metric t) ((S (phi (k + offset))).base.metric t)
      (hTmetric k t) m z]
    have himage := hfimage k ⟨(z : Q), subset_closure z.property, rfl⟩
    change riemannianEDistOf (Y.obj (phi (k + offset))).metric
      (Y.obj (phi (k + offset))).basepoint (f k z) <
        ENNReal.ofReal (c / (2 * Real.sqrt 3)) at himage
    apply hderiv (phi (k + offset)) m t ht (f k z)
    exact le_of_lt himage
  have hshift : StrictMono (fun k : ℕ => k + offset) := fun _ _ h => Nat.add_lt_add_right h _
  have hTterminal : MetricCInfConvergenceOnCompacts (fun k => (T k).base.metric 0)
      (gQ.restrictOpen V) (gQ.restrictOpen V) := by
    have h := (hGconv.comp_subseq hshift).restrictOpenOfSubset hVU
    simp only [SmoothRiemannianMetric.restrictOpen_flat] at h
    exact h.congr (Eventually.of_forall fun k => (hterminal k).symm)
  have hab : -(c / 24) < (0 : ℝ) := by linarith
  have hslab : Icc (-(c / 24)) 0 ⊆
      (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hreg : Ico (-(c / 24)) 0 ⊆
      (RealTimeInterval.closed (-(c / 6)) 0 (by linarith)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  obtain ⟨rho, hrho, g, hg0, hconv⟩ :=
    exists_metric_subsequence_on_closed_interval_of_terminal_convergence T hT
      (gQ.restrictOpen V) hab hslab hreg hTterminal (by
        intro K _ m
        exact ⟨B m, hB m, Eventually.of_forall fun k t ht z _ => hTcurv k m t ht z⟩)
  let P : PointedRiemannianManifold I3 := {
    M := V
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := ⟨q, hqV⟩
    metric := gQ.restrictOpen V }
  have hflow : IsSolutionOn ({ base.metric := g } : SolutionOn (I := I3) (M := V)
      (RealTimeInterval.closed (-(c / 24)) 0 hab.le)) := by
    apply isSolutionOn_of_fixed_domain_metric_convergence P T hT hab hslab
      (Ioo_subset_Ico_self.trans hreg) rho hrho g hconv
    intro K hK p
    exact Eventually.of_forall fun k => by
      obtain ⟨L, _, hL⟩ := exists_metric_time_lipschitz_constant_on_compact_of_solution
        (T k) (hT k) hab hslab hreg (gQ.restrictOpen V) hK p
      exact ⟨L, fun s hs t ht q hq z hz => hL q hq s hs t ht z hz⟩
  refine ⟨psi, hpsi, horiginal, S, hS, hmetric, hmetric0, hcomplete, hcenter,
    hcurv, hderiv, hinj, phi, hphi, horiginal', Q, top, charts, hman, hT2, hsecond,
    gQ, V, U, q, F, G, hVcompact, hVUclosure, hqV, hG, hGconv, offset, f,
    fun k => ⟨hfsource k, hfEq k, hfbase k, hfcapture k, hfimage k⟩,
    hVU, T, hT, hTmetric, hterminal, rho, hrho, ?_, g, hg0, hflow, hconv⟩
  exact horiginal'.comp (hshift.comp hrho)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
