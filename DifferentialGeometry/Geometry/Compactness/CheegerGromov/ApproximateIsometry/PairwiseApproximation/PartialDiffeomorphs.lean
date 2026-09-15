import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.Basic
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Inverse

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private theorem closedBall_subset_riemannianClosedBallOf
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn Y) {r s : ℝ} (hrs : r ≤ s) :
    letI := P.ms
    Metric.closedBall Y.basepoint r ⊆ riemannianClosedBallOf Y.metric Y.basepoint s := by
  intro x hx
  change riemannianEDistOf Y.metric Y.basepoint x ≤ ENNReal.ofReal s
  have hreal : riemannianEDistOf Y.metric Y.basepoint x =
      ENNReal.ofReal (@dist Y.M P.ms.toDist Y.basepoint x) := P.realizes Y.basepoint x
  rw [hreal]
  have hd : @dist Y.M P.ms.toDist Y.basepoint x ≤ r := by
    simpa only [Metric.mem_closedBall, dist_comm] using hx
  exact ENNReal.ofReal_le_ofReal (hd.trans hrs)

theorem HasPairwiseApproximateIsometries.of_partial_metric_approximations
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (P : ∀ k : ℕ, ProperMetricOn (X.obj k))
    (hpartial : ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ p : ℕ,
      ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
        ∃ Ψ : PartialDiffeomorph I I (X.obj k).M (X.obj l).M ∞,
          Ψ (X.obj k).basepoint = (X.obj l).basepoint ∧
          Nonempty (PartialDiffeomorphMetricApproximation
            (riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint s)
            ε p Ψ (X.obj k).metric (X.obj l).metric)) :
    HasPairwiseApproximateIsometries (X := X) P := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨?_⟩
  intro r hr ε hε hε1 p
  obtain ⟨N, hN⟩ := hpartial (r + 1) (by linarith) ε hε hε1 p
  refine ⟨N, fun k l hk hl => ?_⟩
  let : MetricSpace (X.obj k).M := (P k).ms
  let : MetricSpace (X.obj l).M := (P l).ms
  let : Nonempty (X.obj k).M := ⟨(X.obj k).basepoint⟩
  obtain ⟨Ψ, hbase, ⟨D⟩⟩ := hN k l hk hl
  let R := r + 1 / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hRs : R ≤ r + 1 := by dsimp [R]; linarith
  have hsmall : Metric.closedBall (X.obj k).basepoint r ⊆
      riemannianClosedBallOf (X.obj k).metric (X.obj k).basepoint (r + 1) :=
    closedBall_subset_riemannianClosedBallOf (X.obj k) (P k) (by linarith)
  have hsource : Metric.ball (X.obj k).basepoint R ⊆ Ψ.source :=
    ((Metric.ball_subset_closedBall.trans
      (closedBall_subset_riemannianClosedBallOf (X.obj k) (P k) hRs)).trans D.source_sub)
  have hU : IsOpen (Metric.ball (X.obj k).basepoint R) := by
    have hb := Metric.isOpen_ball (x := (X.obj k).basepoint) (ε := R)
    rwa [ProperMetricOn.top_eq (X.obj k) (P k)] at hb
  let U : TopologicalSpace.Opens (X.obj k).M := ⟨Metric.ball (X.obj k).basepoint R, hU⟩
  have Dsmall := D.mono hsmall le_rfl hε1
  refine ⟨R, hrR, Ψ, ?_, Ψ.toPartialEquiv.injOn.mono hsource, hbase, ⟨Dsmall.forward⟩, ?_⟩
  · intro z
    exact Ψ.isLocalDiffeomorphAt I I ∞ (hsource z.property)
  · refine ⟨Dsmall.reverse.congr (fun y hy => ?_)⟩
    exact DifferentialGeometry.PartialDiffeomorph.invFunOn_eventuallyEq_symm_on_image
      Ψ (U := U) hsource y ((image_mono (Metric.closedBall_subset_ball hrR)) hy)

end DifferentialGeometry.CheegerGromovCompactness
