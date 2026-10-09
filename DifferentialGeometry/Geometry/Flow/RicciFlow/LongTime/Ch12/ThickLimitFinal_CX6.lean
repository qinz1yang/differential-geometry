import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitClosedness_CX6

set_option autoImplicit false

/-! # CH12-CX6: the three LTF05 endpoints -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Curvature
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- LTF05 with explicit LTF03 and fixed-ball compactness inputs. -/
theorem ltf05_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (w : ℝ)
    (hjets : ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ n in atTop, HasLocalCurvDerivBound
          (S.pointedSeq.connectedComponent.obj n) (S.pointedSeq.connectedComponent.obj n).basepoint R p C)
    (hinj : ∀ S : LatePointSequence_S13 F, IsWThickSequence_S13 S w →
      ∀ R : ℝ, 0 < R → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
        ∀ x : (S.pointedSeq.connectedComponent.obj n).M,
          riemannianEDistOf (S.pointedSeq.connectedComponent.obj n).metric
            (S.pointedSeq.connectedComponent.obj n).basepoint x ≤ ENNReal.ofReal R →
          HasInjRadiusAt (S.pointedSeq.connectedComponent.obj n) x η) :
    ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w ∧
    ActualThickLimitsSequentiallyCompact_S13 Hp hdec hneg w ∧
    (0 < w → (∀ M : FiniteVolumeHyperbolicModel.{u}, ¬ IsActualWThickLimit_S13 F w M) →
      ∃ T : ℝ, ∀ s : RegularSlice F.observation, T < s.time → ∀ p : s.stage.Carrier,
        ¬ ∃ r : ℝ, 0 < r ∧ curvatureRadius s.normalizedMetric p = ENNReal.ofReal r ∧
          ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r) := by
  have he := thickSequenceHasHyperbolicSubsequence_CX6 Hp hdec hneg hLTF03 w hjets hinj
  exact ⟨he, actualThickLimitsSequentiallyCompact_of_extraction_CX6 Hp hdec hneg w he,
    fun hw hempty => eventually_no_thick_points_CX6 Hp hdec hneg w hw he hempty⟩

end GC.LongTime.Ch12
