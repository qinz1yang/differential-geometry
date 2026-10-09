import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCenterMain_CX8
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.W2Assembly_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdP6Scal_S23
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitCurvHI_S20
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThickLimitSeedReduce_O5

set_option autoImplicit false

/-!
# CH12-S32 (G1): LTF03 from P6 and the W2 / G2 statements

Pure wiring, no new mathematics.  `hLTF03_of_P6_W2_S32` composes
`seedHyperbolicOnFixedBallsSeq_O5` (O5, S1) with `hcenter_CX8` (the parabolic centre theorem, whose
only analytic input is the S8 `hW2`), and with `hcurv_of_scalar_upper_S20` applied to
`hscal_of_P6_S23` (the scalar upper bound on fixed normalised balls, from the canonical
neighbourhood hypothesis `P6_S23` and the same `hW2` and `hcenter`).
`hLTF03_of_P6_G2_S32` replaces `hW2` by the KL84.2 backward-seed statement `hG2` of
`W2Assembly_CX2.lean`, via `W2_of_G2_CX2`.
-/

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.LongTime
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12
universe u

/-- LTF03 (negative branch) from the canonical-neighbourhood hypothesis `P6_S23` and the
S8 hypothesis `hW2` (binder copied verbatim from `hcenter_CX8`). -/
theorem hLTF03_of_P6_W2_S32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F) (hP6 : P6_S23 Hp)
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
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2)) :
    ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L :=
  seedHyperbolicOnFixedBallsSeq_O5 Hp hdec hneg (hcenter_CX8 Hp hW2)
    (hcurv_of_scalar_upper_S20 Hp (hscal_of_P6_S23 Hp hP6 hW2 (hcenter_CX8 Hp hW2)))

/-- LTF03 (negative branch) from `P6_S23` and the KL84.2 backward-seed statement `hG2`
(binder copied verbatim from the `variable (hG2 …)` of `W2Assembly_CX2.lean`, l.24–49). -/
theorem hLTF03_of_P6_G2_S32 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F) (hP6 : P6_S23 Hp)
    (hG2 : ∀ w : ℝ, 0 < w → ∃ a c c₁ Λ₀ b₀ T₀ : ℝ,
      0 < a ∧ 2 * a ^ 2 < c ∧ 0 < c₁ ∧ 1 ≤ Λ₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, T₀ ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b₀ * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume
          (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ₀ * (Hp.records n i).nominalRadius h ≤ r) →
        ∃ y ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) p r,
          ∀ v : Icc (0 : ℝ) s.history.horizon, s.time - c * r ^ 2 ≤ v.val →
          ∃ yv : (s.history.stageAt v).Carrier,
            (v.val = s.time → HEq yv y) ∧
            hasSmallParabolicCurvature s.history v yv (a * r) ∧
            ENNReal.ofReal (c₁ * (a * r) ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage v) v) yv (a * r) ∧
            ∃ A : BackwardPointTrace s.history (s.history.activeStage v)
                (s.history.activeStage (sliceTop_S8 s))
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) y,
              A.point (s.history.activeStage v) le_rfl
                (s.history.activeStage_mono (show v ≤ sliceTop_S8 s from v.property.2)) = yv) :
    ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L :=
  hLTF03_of_P6_W2_S32 Hp hdec hneg hP6 (W2_of_G2_CX2 Hp hdec hG2)

end GC.LongTime.Ch12
