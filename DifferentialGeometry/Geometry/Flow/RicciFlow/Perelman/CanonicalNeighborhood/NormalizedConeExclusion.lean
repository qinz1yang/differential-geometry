import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.ConeExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaledLimit

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} I3) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem intrinsic_end_cone_solution_exclusion
    (L : PointedRiemannianManifold.{u, 0, 0} I3)
    (W : TopologicalSpace.Opens L.M) (hW : PathConnectedSpace W) :
    let _ : PathConnectedSpace W := hW
    let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (q0 : UniformSpace.Completion W) (d : ℝ)
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d)
    (x : ℕ → W) (j : ℕ → ℕ) (hj : StrictMono j) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hQ : Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) atTop atTop)
    (hratio : Tendsto (fun n => A n / metricScalarAt L.metric (x (j n) : L.M)) atTop (𝓝 1))
    (hlower : ∀ᶠ n in atTop, 196 < metricScalarAt L.metric (x n : L.M) * dist (x n : UniformSpace.Completion W) q0 ^ 2)
    (hupper : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt L.metric (x n : L.M) * dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B)
    (P : PointedRiemannianManifold.{0, 0, 0} I3) (hpath : PathConnectedSpace P.M)
    (tau : ℝ) (htau : 0 < tau)
    (S : SolutionOn (I := I3) (M := P.M) (RealTimeInterval.closed (-tau) 0 (by linarith)))
    (C : ℕ → PartialDiffeomorph I3 I3 P.M W ∞) (hS : IsSolutionOn S) (hterminal : S.base.metric 0 = P.metric)
    (hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ)
    (hscalar : metricScalarAt P.metric P.basepoint = 1)
    (hbase : ∀ n, C n P.basepoint = x (j n))
    (r : ℝ) (hr : 0 < r) (hK : IsCompact (riemannianClosedBallOf P.metric P.basepoint r)),
    (∀ᶠ n in atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
      riemannianClosedBallOf (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (x (j n)) (r / 4) ⊆
        (C n) '' riemannianClosedBallOf P.metric P.basepoint r) →
    (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
      ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
        |metricDistance (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (C n a) (C n b) -
          metricDistance P.metric a b| < eta) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro q0 d cone x j hj A hA hQ hratio hlower hupper P hpath tau htau S C hS hterminal
    hsec hscalar hbase r hr hK hcapture hdist
  exact rescaled_end_cone_exclusion (L.metric.restrictOpen W) (fun _ _ => rfl)
    cone x j hj A hA (fun n => metricScalarAt L.metric (x n : L.M))
    hQ hratio (c := 196) (by norm_num) (hlower.mono fun _ h => h.le)
    hupper P hpath tau htau S (fun n a => C n a) hS hterminal
    hsec (by rw [hscalar]; norm_num) hbase r hr hK (hcapture.mono fun _ h => h.2) hdist

theorem normalized_end_cone_exclusion {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      ∀ f : ℕ → ℕ, StrictMono f →
      ∀ L : PointedRiemannianManifold.{u, 0, 0} I3,
      ∀ maps : PointedRiemannianConvergenceMaps (X.toFlowSequence.atTime 0) L f,
      ∀ conv : MetricConvergenceData maps,
      (∀ i, conv.domain i = CanonicalMetricCompactness.canonicalSourceData maps i) →
      (∀ eta : ℝ, 0 < eta → ∃ N : ℕ, ∀ i : ℕ, N ≤ i →
        ∀ y ∈ maps.source i, ∀ v : TangentSpace I3 y,
          (1 - eta) * L.metric.inner y v v ≤
            ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ∧
          ((X.term (f i)).S.base.metric 0).inner (maps.partialDiffeomorph i y)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v)
              (mfderiv I3 I3 (maps.partialDiffeomorph i) y v) ≤
            (1 + eta) * L.metric.inner y v v) →
      ∀ W : TopologicalSpace.Opens L.M, ∀ hW : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hW
      let _ : PseudoMetricSpace W := (L.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∀ q0 : UniformSpace.Completion W, ∀ d : ℝ, 0 < d →
        IsCompact (Metric.closedBall q0 d) →
        Metric.closedBall q0 d ⊆ insert q0 (range (fun x : W => (x : UniformSpace.Completion W))) →
      ∀ x : ℕ → W, Tendsto (fun n => (x n : UniformSpace.Completion W)) atTop (𝓝 q0) →
        Tendsto (fun n => metricScalarAt L.metric (x n : L.M)) atTop atTop →
        (∀ᶠ n in atTop, 196 < metricScalarAt L.metric (x n : L.M) *
          dist (x n : UniformSpace.Completion W) q0 ^ 2) →
        (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt L.metric (x n : L.M) *
          dist (x n : UniformSpace.Completion W) q0 ^ 2 ≤ B) →
        Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation q0 d) → False := by
  obtain ⟨epsStar, hepsStar, hproduce⟩ := exists_local_backward_limit_on_normalized_end.{u} hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp W hW
    instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro q0 d hd hKd hcover x hx hQ hlower hupper hcone
  as_aux_lemma =>
    obtain ⟨cone⟩ := hcone
    obtain ⟨j, k, hj, _, hq, hratio, P, hpath, tau, htau, S, C, hS, hterminal, hsec,
      hscalar, hbase, r, hr, hK, hcapture, hdist⟩ :=
      hproduce eps heps hle sigma hsigma Phi hPhi X f hf L maps conv hcanonical hcomp
        W hW q0 d hd hKd hcover x hx hQ hlower
    as_aux_lemma =>
      clear hproduce
      let A := fun n => (X.term (f (k n))).S.scalar 0
        (maps.partialDiffeomorph (k n) (x (j n) : L.M))
      have hA (n : ℕ) : 0 < A n := lt_of_lt_of_le zero_lt_one (hq n)
      change Tendsto (fun n => A n / metricScalarAt L.metric (x (j n) : L.M)) atTop (𝓝 1) at hratio
      change (∀ᶠ n in atTop, riemannianClosedBallOf P.metric P.basepoint r ⊆ (C n).source ∧
        riemannianClosedBallOf (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (x (j n)) (r / 4) ⊆
          (C n) '' riemannianClosedBallOf P.metric P.basepoint r) at hcapture
      change (∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
        ∀ a ∈ riemannianClosedBallOf P.metric P.basepoint r,
        ∀ b ∈ riemannianClosedBallOf P.metric P.basepoint r,
          |metricDistance (scaleMetric (A n) (hA n) (L.metric.restrictOpen W)) (C n a) (C n b) -
            metricDistance P.metric a b| < eta) at hdist
      generalize hdef : A = A' at hA hratio hcapture hdist
      clear hdef hq A
      as_aux_lemma =>
        exact intrinsic_end_cone_solution_exclusion L W hW q0 d cone x j hj A' hA
          hQ hratio hlower hupper P hpath tau htau S C hS hterminal hsec hscalar hbase r hr hK
          hcapture hdist

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
