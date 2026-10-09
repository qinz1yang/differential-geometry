import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitInterfaceProps
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Restriction
import DifferentialGeometry.Topology.Manifold.OrientationExhaustion
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false

/-! # CH12-CX6: pointed compactness on actual base components and limit orientation -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem late_sequence_complete_CX6 (S : LatePointSequence_S13 F) : SeqMetricComplete S.pointedSeq := by
  constructor
  intro n
  let : CompactSpace (S.pointedSeq.obj n).M := (inferInstance : CompactSpace (S.slices n).stage.Carrier)
  unfold MetricComplete
  infer_instance

/-- The permitted compactness inputs are explicit fixed-ball curvature jets and
injectivity radii.  No limit, hyperbolic metric, or convergence witness is input. -/
theorem exists_actual_canonical_limit_CX6 (S : LatePointSequence_S13 F)
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound
        (S.pointedSeq.connectedComponent.obj n) (S.pointedSeq.connectedComponent.obj n).basepoint R p C)
    (hinj : ∀ R : ℝ, 0 < R → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
      ∀ x : (S.pointedSeq.connectedComponent.obj n).M,
        riemannianEDistOf (S.pointedSeq.connectedComponent.obj n).metric
          (S.pointedSeq.connectedComponent.obj n).basepoint x ≤ ENNReal.ofReal R →
        HasInjRadiusAt (S.pointedSeq.connectedComponent.obj n) x η) :
    ∃ Q : MetricCompactLimit S.pointedSeq,
      (∀ n, Q.convergence.metrics.domain n = CanonicalMetricCompactness.canonicalSourceData Q.maps n) ∧
      ConnectedSpace Q.limit.M ∧ (∀ n, IsCompact (closure (Q.maps.source n))) ∧
      (∀ n, IsConnected (Q.maps.source n)) ∧
      (∀ n, closure (Q.maps.source n) ⊆ Q.maps.source (n + 1)) := by
  obtain ⟨Q, hcan, _, hconn, hcpt, hsrcconn, hnest⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      S.pointedSeq.connectedComponent (late_sequence_complete_CX6 S).connectedComponent
      (fun n => (S.pointedSeq.obj n).connectedComponent_connected) hjets hinj
  let U : ∀ n, Opens (S.pointedSeq.obj n).M :=
    fun n => connectedComponentOpen (I := ThreeModel) (S.pointedSeq.obj n).basepoint
  have hp : ∀ n, (S.pointedSeq.obj n).basepoint ∈ U n := fun _ => mem_connectedComponent
  let Φ : PointedRiemannianConvergenceMaps S.pointedSeq Q.limit Q.subseq := Q.maps.liftTargetOpen U hp
  obtain ⟨C, hC⟩ := Q.maps.exists_canonical_metric_convergence_liftTargetOpen U hp Q.convergence.metrics hcan
  let R : MetricCompactLimit S.pointedSeq :=
    { subseq := Q.subseq
      strictMono := Q.strictMono
      limit := Q.limit
      limit_complete := Q.limit_complete
      maps := Φ
      convergence := ⟨C⟩ }
  exact ⟨R, hC, hconn, hcpt, hsrcconn, hnest⟩

/-- Orientation descends from the actual oriented slices on a nested connected
exhaustion.  The global orientation is obtained by aligning signs at the basepoint. -/
theorem actual_limit_oriented_CX6 (S : LatePointSequence_S13 F) (σ : ℕ → ℕ)
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (Φ : PointedRiemannianConvergenceMaps S.pointedSeq L σ)
    (hconn : ∀ n, IsConnected (Φ.source n))
    (hnest : ∀ n, closure (Φ.source n) ⊆ Φ.source (n + 1)) :
    Nonempty (ManifoldOrientation ThreeModel L.M 3) := by
  let U : ℕ → Opens L.M := fun n => ⟨Φ.source n, (Φ.partialDiffeomorph n).open_source⟩
  have hU : Monotone U := monotone_nat_of_le_succ fun n => subset_closure.trans (hnest n)
  have hcover : ∀ x : L.M, ∃ n, x ∈ U n := by
    intro x
    obtain ⟨n, hn⟩ := Φ.source_subset (isCompact_singleton (x := x))
    exact ⟨n, hn n le_rfl (mem_singleton x)⟩
  let o : ∀ n, Manifold.SmoothOrientation ThreeModel (S.slices (σ n)).stage.Carrier := fun n =>
    Manifold.smoothOrientationOfManifoldOrientation ThreeModel (by
      rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
      exact { dimension_eq := finrank_euclideanSpace_fin
              orientation := (S.slices (σ n)).stage.orientation.orientation
              locally_constant := (S.slices (σ n)).stage.orientation.locally_constant })
  obtain ⟨_, _, O, _⟩ := Manifold.exists_subsequence_preserves_smoothOrientation_on_monotone_open_cover
    ThreeModel U hU hcover (fun n => (hconn n).isPreconnected) L.basepoint Φ.base_mem
    Φ.partialDiffeomorph (fun _ => Subset.rfl) o
  obtain ⟨O', _⟩ := Manifold.exists_manifoldOrientation_eq_of_smoothOrientation ThreeModel O
  exact ⟨by simpa only [ThreeSpace, finrank_euclideanSpace_fin] using O'⟩

end GC.LongTime.Ch12
