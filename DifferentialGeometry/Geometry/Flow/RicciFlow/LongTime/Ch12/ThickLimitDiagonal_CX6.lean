import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitApproximation_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

/-! # CH12-CX6: actual late realizations for the double diagonal -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric
open GC.LongTime Set Filter TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem model_complete_CX6 (M : FiniteVolumeHyperbolicModel.{u}) :
    MetricComplete (modelPointed_S13 M) := M.complete.complete

/-- Row j is sampled after time j, on radius 4(j+1), through order j,
with two-sided error 1/(j+2).  Its image captures the actual radius-(j+1)
ball.  Thus no abstract model is substituted for an actual time slice. -/
theorem exists_actual_diagonal_CX6 (w : ℝ)
    (models : ℕ → FiniteVolumeHyperbolicModel.{u})
    (hactual : ∀ j, IsActualWThickLimit_S13 F w (models j)) :
    ∃ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w ∧
      (∀ j : ℕ, (j : ℝ) < (S.slices j).time) ∧
      ∃ B : ∀ j, PartialDiffeomorph ThreeModel ThreeModel (models j).Carrier (S.pointedSeq.obj j).M ∞,
        ∃ U : ∀ j, Opens (models j).Carrier,
          (∀ j, (models j).basepoint ∈ U j) ∧
          (∀ j, B j (models j).basepoint = (S.pointedSeq.obj j).basepoint) ∧
          (∀ j, riemannianBallOf (S.pointedSeq.obj j).metric (S.pointedSeq.obj j).basepoint
            ((j : ℝ) + 1) ⊆ B j '' (U j : Set (models j).Carrier)) ∧
          ∀ j, Nonempty (PartialDiffeomorphMetricApproximation (U j : Set (models j).Carrier)
            (1 / ((j : ℝ) + 2)) j (B j) (models j).metric (S.pointedSeq.obj j).metric) := by
  classical
  have hrow : ∀ j, ∃ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w ∧
      ∃ Φ : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 (models j)) id,
        ∃ C : MetricConvergenceData Φ,
          ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData Φ n := hactual
  choose rows hrows Φ C hcan using hrow
  let B (j n : ℕ) : PartialDiffeomorph ThreeModel ThreeModel
      (models j).Carrier ((rows j).pointedSeq.obj n).M ∞ := (Φ j).partialDiffeomorph n
  let K (j : ℕ) := riemannianClosedBallOf (models j).metric (models j).basepoint (4 * ((j : ℝ) + 1))
  let U (j : ℕ) : Opens (models j).Carrier := ⟨interior (K j), isOpen_interior⟩
  have hp (j : ℕ) : (models j).basepoint ∈ U j :=
    mem_interior_riemannianClosedBallOf (models j).metric (models j).basepoint (by positivity)
  have hchoose (j : ℕ) : ∃ n : ℕ, (j : ℝ) < ((rows j).slices n).time ∧
      Nonempty (PartialDiffeomorphMetricApproximation (I := ThreeModel) (U j : Set (models j).Carrier)
        (1 / ((j : ℝ) + 2)) j (B j n)
          (models j).metric ((rows j).pointedSeq.obj n).metric) ∧
      riemannianBallOf ((rows j).pointedSeq.obj n).metric ((rows j).pointedSeq.obj n).basepoint
        ((j : ℝ) + 1) ⊆ (Φ j).map n '' (U j : Set (models j).Carrier) := by
    have hK : IsCompact (K j) := (models j).complete.closedEBall_isCompact _ _
    have heps : 0 < 1 / ((j : ℝ) + 2) := by positivity
    have heps1 : 1 / ((j : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have ha := eventually_partial_approximation_CX6 (Φ j) (C j) (hcan j) (K j) hK
      (U j : Set (models j).Carrier) (Subset.refl _) j heps heps1
    have href : ∀ n, ((C j).domain n).referenceMetric = ((C j).domain n).limitMetric := by
      intro n
      rw [hcan j n]
      exact canonicalSourceData_referenceMetric_eq_limitMetric _ _
    have hcap := (Φ j).eventually_ball_subset_image_closed_ball (C j) href
      (model_complete_CX6 (models j)) (modelPointed_S13 (models j)).basepoint
      (A := (j : ℝ) + 1) (R := 3 * ((j : ℝ) + 1)) (L := 2) (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have ht := (rows j).times_tendsto.eventually (eventually_gt_atTop (j : ℝ))
    have hall := ht.and (ha.and hcap)
    obtain ⟨n, htime, happrox, _, hcapture⟩ := hall.exists
    refine ⟨n, htime, happrox, ?_⟩
    have hbase : (Φ j).map n (modelPointed_S13 (models j)).basepoint =
        ((rows j).pointedSeq.obj n).basepoint := (Φ j).basepoint_map n
    rw [hbase] at hcapture
    apply hcapture.trans (image_mono ?_)
    intro x hx
    apply riemannianBallOf_subset_interior_riemannianClosedBallOf (models j).metric (models j).basepoint
      (4 * ((j : ℝ) + 1))
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  choose n hn happrox hcapture using hchoose
  let S : LatePointSequence_S13 F :=
    { slices := fun j => (rows j).slices (n j)
      times_tendsto := tendsto_atTop_mono (fun j => (hn j).le) tendsto_natCast_atTop_atTop
      point := fun j => (rows j).point (n j) }
  refine ⟨S, fun j => hrows j (n j), hn, fun j => (Φ j).partialDiffeomorph (n j), U,
    hp, fun j => (Φ j).basepoint_map (n j), hcapture, happrox⟩

end GC.LongTime.Ch12
