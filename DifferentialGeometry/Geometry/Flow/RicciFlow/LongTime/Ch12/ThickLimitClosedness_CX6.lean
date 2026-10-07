import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitComposition_CX6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitExtraction_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

set_option autoImplicit false

/-! # CH12-CX6: actual thick limits are sequentially compact -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Curvature
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

/-- Closedness is proved by the two diagonals, using only S13 extraction.
No model-family convergence or closedness premise is supplied. -/
theorem actualThickLimitsSequentiallyCompact_of_extraction_CX6
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F) (w : ℝ)
    (hextract : ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w) :
    ActualThickLimitsSequentiallyCompact_S13 Hp hdec hneg w := by
  intro hw models hmodels
  obtain ⟨S, hS, _, B, U, hp, hb, hcap, happrox⟩ := exists_actual_diagonal_CX6 w models hmodels
  obtain ⟨σ, hσ, M, hconv⟩ := hextract hw S hS
  have hactual : IsActualWThickLimit_S13 F w M :=
    ⟨S.subsequence σ hσ, thick_subsequence_CX6 hS σ hσ, hconv⟩
  obtain ⟨Φ, C, hcan⟩ := hconv
  let A : PointedRiemannianConvergenceMaps S.pointedSeq (modelPointed_S13 M) σ :=
    PointedRiemannianConvergenceMaps.ofSubseq (X := S.pointedSeq) σ Φ
  let C₀ : MetricConvergenceData A := MetricConvergenceData.ofSubseq (X := S.pointedSeq) σ C
  have hcan₀ : ∀ n, C₀.domain n = CanonicalMetricCompactness.canonicalSourceData A n := by
    intro n
    change MetricSourceData.ofSubseq (X := S.pointedSeq) σ n (C.domain n) = _
    rw [hcan n]
    rfl
  let Y : PointedRiemannianSeq.{u, 0, 0} ThreeModel := ⟨fun j => modelPointed_S13 (models j)⟩
  let : ConnectedSpace (modelPointed_S13 M).M := M.connected
  obtain ⟨k, hk, Ψ, D, hD⟩ := exists_convergence_of_diagonal_CX6 (Y := Y)
    (model_complete_CX6 M) σ hσ A C₀ hcan₀ B U hp hb hcap happrox
  obtain ⟨D', hD'⟩ := exists_canonical_subseq_convergence_CX6 Ψ D hD
  exact ⟨σ ∘ k, hσ.comp hk, M, hactual, sequence_subseq_maps_CX6 Ψ, D', hD'⟩

/-- LTF03 and explicit fixed-ball CG bounds prove the frozen S13 closedness statement. -/
theorem actualThickLimitsSequentiallyCompact_CX6 {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
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
    ActualThickLimitsSequentiallyCompact_S13 Hp hdec hneg w :=
  actualThickLimitsSequentiallyCompact_of_extraction_CX6 Hp hdec hneg w
    (thickSequenceHasHyperbolicSubsequence_CX6 Hp hdec hneg hLTF03 w hjets hinj)

end GC.LongTime.Ch12
