import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitBasic_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvature_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCompactness_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitTransport_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSmall_CX6

set_option autoImplicit false

/-! # CH12-CX6: LTF05 hyperbolic extraction with the exact S13 conclusion -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- The extracted limit is first realized on a genuine Type 0 manifold.
The returned universe-u model is specifically its S13 ULift. -/
theorem exists_hyperbolic_subsequence_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (S : LatePointSequence_S13 F)
    (hjets : ∀ R : ℝ, 0 < R → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound
        (S.pointedSeq.connectedComponent.obj n) (S.pointedSeq.connectedComponent.obj n).basepoint R p C)
    (hinj : ∀ R : ℝ, 0 < R → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop,
      ∀ x : (S.pointedSeq.connectedComponent.obj n).M,
        riemannianEDistOf (S.pointedSeq.connectedComponent.obj n).metric
          (S.pointedSeq.connectedComponent.obj n).basepoint x ≤ ENNReal.ofReal R →
        HasInjRadiusAt (S.pointedSeq.connectedComponent.obj n) x η) :
    ∃ σ : ℕ → ℕ, ∃ hσ : StrictMono σ, ∃ H : FiniteVolumeHyperbolicModel.{0},
      PointedSmoothConverges_S13 (S.subsequence σ hσ) (uliftModel_S13.{u} H) := by
  obtain ⟨Q, hcan, hconn, _, hsrcconn, hnest⟩ := exists_actual_canonical_limit_CX6 S hjets hinj
  let : ConnectedSpace Q.limit.M := hconn
  obtain ⟨O⟩ := actual_limit_oriented_CX6 S Q.subseq Q.limit Q.maps hsrcconn hnest
  have hcurv := (canonical_limit_hyperbolic_CX6 Hp hdec hneg hLTF03 S Q.subseq Q.strictMono
    Q.limit Q.maps Q.convergence.metrics hcan).2
  obtain ⟨V, _, hV⟩ := canonical_limit_volume_bound_CX6 Hp
  have hvol := (hV S Q.subseq Q.strictMono Q.limit Q.maps Q.convergence.metrics hcan).trans_lt
    (ENNReal.ofReal_lt_top : ENNReal.ofReal V < ⊤)
  obtain ⟨H, e, hp, hg⟩ := exists_ulift_hyperbolic_model_CX6 Q.limit O Q.limit_complete hcurv hvol
  let L := modelPointed_S13 (uliftModel_S13.{u} H)
  let e' : L.M ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.limit.M := e
  let Φ := pullback_limit_maps_CX6 Q.maps e' hp
  obtain ⟨C, hC⟩ := exists_canonical_pullback_limit_CX6 Q.maps Q.convergence.metrics hcan e' hp hg
  obtain ⟨C', hC'⟩ := exists_canonical_subseq_convergence_CX6 Φ C hC
  exact ⟨Q.subseq, Q.strictMono, H, sequence_subseq_maps_CX6 Φ, C', hC'⟩

/-- Explicit fixed-ball compactness suppliers, together with LTF03, discharge
exactly the frozen S13 extraction predicate. -/
theorem thickSequenceHasHyperbolicSubsequence_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
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
    ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w := by
  intro _ S hS
  obtain ⟨σ, hσ, H, hconv⟩ := exists_hyperbolic_subsequence_CX6 Hp hdec hneg hLTF03 S
    (hjets S hS) (hinj S hS)
  exact ⟨σ, hσ, uliftModel_S13 H, hconv⟩

end GC.LongTime.Ch12
