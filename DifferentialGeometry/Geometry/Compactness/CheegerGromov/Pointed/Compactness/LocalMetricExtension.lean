import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.MetricConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_finite_pointed_metric_convergence_of_local_metric_agreement
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (g₀ : ∀ k, SmoothRiemannianMetric I (X.obj k).M)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η)
    (hmetric : ∀ᶠ k in atTop, ∀ y ∈ riemannianBallOf
      (X.obj k).metric (X.obj k).basepoint R,
      (g₀ k).inner y = (X.obj k).metric.inner y) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Q : Type uE, ∃ top : TopologicalSpace Q, letI := top
      ∃ charts : ChartedSpace E Q, letI := charts
      ∃ hman : IsManifold (modelWithCornersSelf ℝ E) ∞ Q, letI := hman
      ∃ hT2 : T2Space Q, letI := hT2
      ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
      ∃ (gQ : SmoothRiemannianMetric (modelWithCornersSelf ℝ E) Q)
        (V : TopologicalSpace.Opens Q) (q : Q)
        (Φ : ∀ k, PartialDiffeomorph (modelWithCornersSelf ℝ E) I Q
          (X.obj (phi k)).M ∞)
        (G : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V),
        IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
        (∀ k, closure (V : Set Q) ⊆ (Φ k).source) ∧
        (∀ k, Φ k q = (X.obj (phi k)).basepoint) ∧
        (∀ k, riemannianClosedBallOf (X.obj (phi k)).metric
          (X.obj (phi k)).basepoint r ⊆ (Φ k) '' (V : Set Q)) ∧
        (∀ k, (Φ k) '' closure (V : Set Q) ⊆
          riemannianBallOf (X.obj (phi k)).metric (X.obj (phi k)).basepoint R) ∧
        (∀ k (x : V) (v w : TangentSpace (modelWithCornersSelf ℝ E) x),
          (G k).inner x v w = (g₀ (phi k)).inner (Φ k x)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) v)
            (mfderiv (modelWithCornersSelf ℝ E) I (Φ k) (x : Q) w)) ∧
        MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) := by
  classical
  obtain ⟨phi, hphi, Q, top, charts, hman, hT2, hsecond, gQ, V, U, q, F, G,
    hV, hVU, hq, hG, hconv, hPhi⟩ :=
    exists_finite_pointed_metric_comparison_of_local_curvature_injectivity
      X hcomplete hconn hr hrR hη hjets hinj
  let _ := top
  let _ := charts
  let _ := hman
  let _ := hT2
  let _ := hsecond
  let _ : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace E Q
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let _ : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hVU' : V ≤ U := subset_closure.trans hVU
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hPhi.and hG).and
    (hphi.tendsto_atTop.eventually hmetric))
  let f : ℕ → ℕ := fun k => phi (k + N)
  have hadd : StrictMono (fun k : ℕ => k + N) :=
    fun _ _ h => Nat.add_lt_add_right h N
  have hf : StrictMono f := hphi.comp hadd
  choose Ψ hsource hEq hbase hcapture hupper using
    fun k => (hN (k + N) (by omega)).1.1
  let GV : ℕ → SmoothRiemannianMetric (modelWithCornersSelf ℝ E) V :=
    fun k => (G (k + N)).restrictOpenOfSubset hVU'
  refine ⟨f, hf, Q, top, charts, hman, hT2, hsecond, gQ, V, q, Ψ, GV,
    hV, hq, ?_, hbase, hcapture, hupper, ?_, ?_⟩
  · intro k
    exact hVU.trans (subset_closure.trans (hsource k))
  · intro k x v w
    have hsrc : (x : Q) ∈ (Ψ k).source :=
      hsource k (subset_closure (hVU' x.property))
    have hnear : (Ψ k : Q → (X.obj (f k)).M) =ᶠ[𝓝 (x : Q)] F (k + N) :=
      Filter.eventuallyEq_of_mem ((Ψ k).open_source.mem_nhds hsrc) (hEq k)
    have hderiv := hnear.mfderiv_eq
      (I := modelWithCornersSelf ℝ E) (I' := I)
    have himage : Ψ k x ∈ riemannianBallOf (X.obj (f k)).metric
        (X.obj (f k)).basepoint R := hupper k ⟨x, subset_closure x.property, rfl⟩
    have hmet := (hN (k + N) (by omega)).2 (Ψ k x) himage
    change (G (k + N)).inner ⟨x, hVU' x.property⟩ v w = _
    rw [hmet, hnear.self_of_nhds, hderiv]
    exact (hN (k + N) (by omega)).1.2 ⟨x, hVU' x.property⟩ v w
  · have hc := (hconv.comp_subseq hadd).restrictOpenOfSubset hVU'
    have he : (gQ.restrictOpen U).restrictOpenOfSubset hVU' = gQ.restrictOpen V := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rfl
    rw [he] at hc
    exact hc

end DifferentialGeometry.CheegerGromovCompactness
