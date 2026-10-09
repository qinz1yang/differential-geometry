import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862Step866R_O79
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HUR_O79
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HG2cV4_O69
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HSeed_S139

/-!
# CH12-O79 G3c: `hG2c_R_O79` — the hG2c leaf (κ-certificate) on the region contract

`hG2c_R_O79 Hp hdec hP2 hprof hKL82R := hG2c_v4_O69 Hp hdec hP2 hprof
(step866_v3_of_contracts_R_O79 Hp (hSeed_S139 Hp) (hUR_O79 Hp hdec hprof) hKL82R)`.
Conclusion = that of `hG2c_v4_O69` (= `hG2c_O57`, verbatim).  Remaining inline input beyond the
`hG2c_v4_O69` ones (`hdec`, `hP2`, `hprof`): `hKL82R` (`[FROZEN] CH12-O79 G3`; producer O78's
regional KL82 with a common `τ₈₂`, composed with `regInput_of_reg_O77`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- **G3c**: the hG2c leaf from the region contract (A13-8 modulo the regional KL82 `hKL82R`). -/
theorem hG2c_R_O79 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {Ctime : ℝ≥0} (hP2 : P2_O2 Hp Ctime)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius)
    (hKL82R : ∀ w : ℝ, 0 < w → ∃ τ₈₂ M : ℝ, 0 < τ₈₂ ∧ τ₈₂ ≤ 1 ∧ 0 < M ∧
      (∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
          (r0 τ : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
            (H.activeStage_mono hat) x0),
          0 < r0 → 0 < τ → τ ≤ τ₈₂ → (a : ℝ) = top - τ * r0 ^ 2 →
          Reg_O77 H hat X r0 →
          ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
          ENNReal.ofReal (w * (r0 / 4) ^ 3 / 10) ≤
            ballVolume (H.stageMetric (H.activeStage a) a)
              (X.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) (r0 / 4)) ∧
      (∀ (H : ObservedHistory.{u}) (top : Icc (0 : ℝ) H.horizon) (x0 : (H.stageAt top).Carrier)
          (r0 : ℝ) (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ top)
          (X : BackwardPointTrace H (H.activeStage a) (H.activeStage top)
            (H.activeStage_mono hat) x0),
          0 < r0 → (a : ℝ) = top - τ₈₂ / 2 * r0 ^ 2 →
          Reg_O77 H hat X r0 →
          ENNReal.ofReal (w * r0 ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage top) top) x0 r0 →
          ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ top),
            (top : ℝ) - τ₈₂ / 2 * r0 ^ 2 / 2 ≤ v →
            ∀ q ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
                (X.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
                (r0 / 4),
              Real.sqrt (normSq0S (H.stageMetric (H.activeStage v) v) q 4
                  (metricRm04At (H.stageMetric (H.activeStage v) v) q)) ≤ M / r0 ^ 2)) :
    ∃ ε C₁ K τ₁ τ₂ κ₀ b T : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ 1 ≤ C₁ ∧ 0 < K ∧ 0 < τ₁ ∧ 0 < τ₂ ∧
      0 < κ₀ ∧ 0 < b ∧ (τ₁ + τ₂) * b ^ 2 ≤ 1 / 2 ∧ 0 < T ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r0 : ℝ), 0 < r0 →
        r0 ≤ b * Real.sqrt s.time →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, C₁ * (Hp.records n i).nominalRadius h ≤ r0) →
        (∀ q ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          SectionalBoundedBelowAt
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            q (-(r0 ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z ρ) →
        ∃ (a : Icc (0 : ℝ) s.history.horizon) (hat : a ≤ sliceTop_S8 s)
          (X : BackwardPointTrace s.history (s.history.activeStage a)
            (s.history.activeStage (sliceTop_S8 s)) (s.history.activeStage_mono hat) x0),
          (a : ℝ) = s.time - τ₁ * r0 ^ 2 ∧
          ∀ (u : Icc (0 : ℝ) s.history.horizon) (hau : a ≤ u) (hut : u ≤ sliceTop_S8 s),
            s.history.isTracedRegion u
              (X.point (s.history.activeStage u) (s.history.activeStage_mono hau)
                (s.history.activeStage_mono hut))
              (κ₀ * r0) (τ₂ * r0 ^ 2) (K * (r0 ^ 2)⁻¹) :=
  hG2c_v4_O69 Hp hdec hP2 hprof
    (step866_v3_of_contracts_R_O79 Hp (hSeed_S139 Hp) (hUR_O79 Hp hdec hprof) hKL82R)

end GC.LongTime.Ch12
