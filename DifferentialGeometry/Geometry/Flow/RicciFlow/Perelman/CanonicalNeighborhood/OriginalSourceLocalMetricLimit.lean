import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.OriginalSourceInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.MetricConvergence

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

theorem RealizedFiniteHorn.exists_original_source_local_metric_limit
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
                        ∀ᶠ k in atTop,
                          ∃ f : PartialDiffeomorph I3 I3 Q (Y.obj (phi k)).M ∞,
                            closure (U : Set Q) ⊆ f.source ∧ EqOn f (F k) f.source ∧
                            f q = (Y.obj (phi k)).basepoint ∧
                            (∀ y : (Y.obj (phi k)).M,
                              riemannianEDistOf (Y.obj (phi k)).metric
                                (Y.obj (phi k)).basepoint y ≤
                                  ENNReal.ofReal (c / (4 * Real.sqrt 3)) →
                              y ∈ f '' closure (V : Set Q)) ∧
                            f '' closure (V : Set Q) ⊆
                              {y | riemannianEDistOf (Y.obj (phi k)).metric
                                (Y.obj (phi k)).basepoint y <
                                  ENNReal.ofReal (c / (2 * Real.sqrt 3))} := by
  classical
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  obtain ⟨epsStar, c, C, hc, hepsStar, hC, hsolutions⟩ :=
    RealizedFiniteHorn.exists_original_source_curvature_derivative_bounds_and_injectivity
      hkappa hmod
  refine ⟨epsStar, c, C, hc, hepsStar, hC, ?_⟩
  intro eps heps hepsStar' sigma hsigma Phi hPhi
  obtain ⟨B, eta, hB, heta, hsolutions'⟩ :=
    hsolutions eps heps hepsStar' sigma hsigma Phi hPhi
  refine ⟨B, eta, hB, heta, ?_⟩
  intro X H ray d N hQ j hj
  obtain ⟨threshold, hthreshold⟩ :=
    hsolutions' X H (fun n => ray.point (d (N + n))) hQ
  obtain ⟨psi, hpsi, hselect⟩ := extraction_forall_of_eventually
    (fun n => hj.tendsto_atTop.eventually (eventually_ge_atTop (threshold n)))
  refine ⟨psi, hpsi, H.strictMono.comp (hj.comp hpsi), ?_⟩
  dsimp only
  let hq := fun n => zero_lt_one.trans_le (hQ n)
  let Y := H.rescaledSourceSeq ray d N (j ∘ psi) hq
  have hall := fun n => hthreshold n (j (psi n)) (hselect n)
  choose S hS hmetric hcomplete hcenter hcurv hderiv hterminal using hall
  have hmetric0 (n : ℕ) : (S n).base.metric 0 = (Y.obj n).metric := by
    rw [hmetric n 0]
    simp only [zero_div]
    rfl
  have hcurv' : ∀ n, ∀ y : (Y.obj n).M, ∀ t ∈ Icc (-(c / 6)) 0,
      y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
        (c / Real.sqrt 3) →
      (S n).scalar t y ≤ 12 ∧
      Real.sqrt (FlowMetricBall.rmNormSq (S n) t y) ≤ C * (3 + 13 * Phi 1) := by
    intro n y t ht hy
    exact hcurv n y t ht ((hmetric0 n).symm ▸ hy)
  have hderiv' : ∀ n m, ∀ t ∈ Icc (-(c / 24)) 0,
      ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
        (c / (2 * Real.sqrt 3)),
      curvDerivNorm (I := I3) m ((S n).base.metric t) y ≤ B m := by
    intro n m t ht y hy
    exact hderiv n m t ht y ((hmetric0 n).symm ▸ hy)
  have hinj : ∀ n, ∀ y ∈ riemannianClosedBallOf (Y.obj n).metric (Y.obj n).basepoint
      (c / (2 * Real.sqrt 3)), HasInjRadiusAt (Y.obj n) y eta := by
    intro n
    have h := hterminal n
    dsimp only at h
    rw [hmetric0 n] at h
    exact h
  refine ⟨S, hS, hmetric, hmetric0, hcomplete, hcenter, hcurv', hderiv', hinj, ?_⟩
  have hcompleteY : SeqMetricComplete Y := by
    refine ⟨fun n => ?_⟩
    have h := hcomplete n 0 ⟨by linarith, le_rfl⟩
    rw [hmetric0 n] at h
    exact h.complete
  have hconn : ∀ n, ConnectedSpace (Y.obj n).M :=
    fun n => X.connected (H.subseq (j (psi n)))
  have hjets : ∀ m : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (Y.obj n) (Y.obj n).basepoint
        (c / (2 * Real.sqrt 3)) m A := by
    intro m
    refine ⟨B m, hB m, Eventually.of_forall fun n y hy => ?_⟩
    have h := hderiv' n m 0 ⟨by linarith, le_rfl⟩ y hy
    rwa [hmetric0 n] at h
  have hinj' : ∀ᶠ n in atTop, ∀ y : (Y.obj n).M,
      riemannianEDistOf (Y.obj n).metric (Y.obj n).basepoint y ≤
        ENNReal.ofReal (c / (4 * Real.sqrt 3)) → HasInjRadiusAt (Y.obj n) y eta := by
    refine Eventually.of_forall fun n y hy => hinj n y ?_
    apply hy.trans
    apply ENNReal.ofReal_le_ofReal
    have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
    apply div_le_div_of_nonneg_left hc.le (by positivity : 0 < 2 * Real.sqrt (3 : ℝ))
    nlinarith
  have hr : (0 : ℝ) ≤ c / (4 * Real.sqrt 3) := by positivity
  have hrR : c / (4 * Real.sqrt 3) < c / (2 * Real.sqrt 3) := by
    apply div_lt_div_of_pos_left hc (by positivity : 0 < 2 * Real.sqrt (3 : ℝ))
    have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
    nlinarith
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, U, q, F, G, hrest⟩ :=
    exists_finite_pointed_metric_comparison_of_local_curvature_injectivity Y hcompleteY hconn
      hr hrR heta hjets hinj'
  refine ⟨phi, hphi, H.strictMono.comp (hj.comp (hpsi.comp hphi)),
    Q, top, charts, hman, hT2, hsecond, gQ, V, U, q, F, G,
    hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2.1, hrest.2.2.2.2.1, ?_⟩
  filter_upwards [hrest.2.2.2.2.2] with k hk
  obtain ⟨Phi, hsource, hmap, hbase, hcapture, himage⟩ := hk
  exact ⟨Phi, hsource, hmap, hbase,
    fun y hy => (Set.image_mono subset_closure) (hcapture y hy), himage⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
