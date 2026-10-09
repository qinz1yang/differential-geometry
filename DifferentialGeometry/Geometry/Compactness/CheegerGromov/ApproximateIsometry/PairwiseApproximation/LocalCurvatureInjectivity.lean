import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.MetricConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.CapturedSets

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_bidirectional_pairwise_metric_approximation_of_local_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ p : ℕ,
        ∃ n₀ : ℕ, ∀ k l : ℕ, n₀ ≤ k → n₀ ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              {y : (X.obj (phi k)).M | riemannianEDistOf (X.obj (phi k)).metric
                (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r}
              eps p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              {y : (X.obj (phi l)).M | riemannianEDistOf (X.obj (phi l)).metric
                (X.obj (phi l)).basepoint y ≤ ENNReal.ofReal r}
              eps p Ψ.symm (X.obj (phi l)).metric (X.obj (phi k)).metric) := by
  obtain ⟨phi, hphi, Q, top, C, hman, hT2, hsecond, gQ, V, U, q, f, G,
    hV, hVU, hq, hG, hconv, hPhi⟩ :=
      exists_finite_pointed_metric_comparison_of_local_curvature_injectivity
        X hcomplete hconn hr hrR hη hjets hinj
  let := top
  let := C
  let := hman
  let := hT2
  let := hsecond
  let : LocallyCompactSpace Q := ChartedSpace.locallyCompactSpace E Q
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  refine ⟨phi, hphi, ?_⟩
  exact eventually_pairwise_approximation_and_symm_on_captured_sets V U hV hVU q hq
    (fun k => (X.obj (phi k)).basepoint) (fun k => (X.obj (phi k)).metric)
    (gQ.restrictOpen U) G f
    (fun k => {y : (X.obj (phi k)).M | riemannianEDistOf (X.obj (phi k)).metric
      (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r}) hG hconv
    (hPhi.mono fun k ⟨Φ, hsource, hEq, hbase, hcapture, _⟩ =>
      ⟨Φ, subset_closure.trans hsource, hEq.mono (subset_closure.trans hsource), hbase, fun y hy =>
        (image_mono subset_closure) (hcapture y hy)⟩)

theorem exists_subsequence_pairwise_metric_approximation_of_local_curvature_injectivity
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    {R r η : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hη : 0 < η)
    (hjets : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint R p C)
    (hinj : ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
      riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
        ENNReal.ofReal r → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ p : ℕ,
        ∃ n₀ : ℕ, ∀ k l : ℕ, n₀ ≤ k → n₀ ≤ l →
          ∃ Ψ : PartialDiffeomorph I I (X.obj (phi k)).M (X.obj (phi l)).M ∞,
            Ψ (X.obj (phi k)).basepoint = (X.obj (phi l)).basepoint ∧
            Nonempty (PartialDiffeomorphMetricApproximation
              {y : (X.obj (phi k)).M | riemannianEDistOf (I := I) (X.obj (phi k)).metric
                (X.obj (phi k)).basepoint y ≤ ENNReal.ofReal r}
              eps p Ψ (X.obj (phi k)).metric (X.obj (phi l)).metric) := by
  obtain ⟨phi, hphi, hcompare⟩ :=
    exists_subsequence_bidirectional_pairwise_metric_approximation_of_local_curvature_injectivity
      X hcomplete hconn hr hrR hη hjets hinj
  refine ⟨phi, hphi, ?_⟩
  intro eps heps heps1 p
  obtain ⟨n₀, hn₀⟩ := hcompare eps heps heps1 p
  refine ⟨n₀, ?_⟩
  intro k l hk hl
  obtain ⟨Ψ, hbase, hfwd, _⟩ := hn₀ k l hk hl
  exact ⟨Ψ, hbase, hfwd⟩

end DifferentialGeometry.CheegerGromovCompactness
