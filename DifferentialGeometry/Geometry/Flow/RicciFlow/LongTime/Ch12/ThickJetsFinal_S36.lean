import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickJetsInj_S36
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitExtraction_CX6
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.VolumeInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent

set_option autoImplicit false

/-! # CH12-S36: the exact S13 extraction predicate (LTF05a) from hjets/hinj of S36 -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12
universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

/-- LTF05a (`ThickSequenceHasHyperbolicSubsequence_S13`) from LTF03, W2 and Q1-scale in seed form:
`hjets`/`hinj` of `thickSequenceHasHyperbolicSubsequence_CX6` are discharged (for `0 < w`). -/
theorem thickSequenceHasHyperbolicSubsequence_S36 (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v R : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v R)
    (hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    (w : ℝ)
    (hQ1 : ∀ w : ℝ, 0 < w → ∃ T a v : ℝ, 0 < a ∧ 0 < v ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r →
        curvatureRadius s.normalizedMetric p = ENNReal.ofReal r →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        HasNormalizedSeed_S13 s p a v) :
    ThickSequenceHasHyperbolicSubsequence_S13 Hp hdec hneg w := by
  intro hw S hS
  obtain ⟨σ, hσ, H, hconv⟩ := exists_hyperbolic_subsequence_CX6 Hp hdec hneg hLTF03 S
    (hjets_of_supplies_S36 Hp hdec hneg hLTF03 hW2 w hw hQ1 S hS)
    (hinj_of_supplies_S36 Hp hdec hneg hLTF03 hW2 w hw hQ1 S hS)
  exact ⟨σ, hσ, uliftModel_S13 H, hconv⟩

end GC.LongTime.Ch12
