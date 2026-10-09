import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862HUPartsV2b_O71
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedStripBig_O69
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiringTail_S118
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862UnscathedRegion_S111
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL83Core_CX7
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TracedFamily_S130

/-!
# CH12-O69 G4: `hU_O69 : <hU v2b>` (`[FROZEN v2b] CH12-O69 hU`) — final assembly of the hU core
`hU_v2b_of_parts_O71 Hp (seedStrip_big_O69 Hp) hscale hrc` ([FROZEN v3] CH12-O71 inputs), with
`hscale := (hscale_of_prof_S119).choose_spec.2 Hp hprof`, `hrc := hrc_of_hdec_S118 Hp hdec`.
Fallback if only `hU_of_parts_O71` is delivered: same call, then drop its last conjunct.
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

/-- **G4** (O69): the hU core in the `[FROZEN v2b] CH12-O69 hU` shape. -/
theorem hU_O69 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
    ∀ σ ℓ wst : ℝ, 0 < σ → σ ≤ 1 → 0 < ℓ → 0 < wst →
      ∃ B c C₀ b₀ T₀ : ℝ, 0 < B ∧ 0 < c ∧ c ≤ ℓ ∧ 1 ≤ C₀ ∧ 0 < b₀ ∧ 0 < T₀ ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (u : Icc (0 : ℝ) N.horizon), T₀ ≤ (u : ℝ) → (u : ℝ) ≤ s.time →
      ∀ (x : (N.stageAt u).Carrier) (r : ℝ), 0 < r → r ≤ b₀ * Real.sqrt u →
      ∀ (a : Icc (0 : ℝ) N.horizon) (hau : a ≤ u)
        (X : BackwardPointTrace N (N.activeStage a) (N.activeStage u) (N.activeStage_mono hau) x),
        (u : ℝ) - r ^ 2 ≤ a →
        (∀ m (i : Fin (F.tower.history m).eventCount),
          (F.tower.history m).time i.succ ∈ Icc ((a : ℝ) - c * r ^ 2) a →
          ∀ h, C₀ * (Hp.records m i).nominalRadius h ≤ r) →
        (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) (20 * r),
            Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
              (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2) →
        (∀ (i : Fin N.eventCount) (hf : N.activeStage a ≤ i.castSucc)
            (hl : i.succ ≤ N.activeStage u) (U : Set (N.stage i.succ).Carrier),
          U ⊆ riemannianBallOf (N.event i).outputMetric
            (X.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) → IsPreconnected U →
          (∀ y ∈ U, metricScalarAt (N.event i).outputMetric y ≤ (9 * B) / r ^ 2) →
          ∀ (x' : (N.event i).incoming.terminalRegularOpen) (y : (N.stage i.succ).Carrier),
            y ∈ U → (N.event i).RegularCrossing x'.val y →
            U ⊆ interior (range (N.event i).oldOutput)) →
        (∀ (v : Icc (0 : ℝ) N.horizon) (hav : a ≤ v) (hvu : v ≤ u),
          ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
              (X.point (N.activeStage v) (N.activeStage_mono hav) (N.activeStage_mono hvu)) r,
            SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) →
        ∀ y : (N.stageAt a).Carrier,
        y ∈ riemannianBallOf (N.stageMetric (N.activeStage a) a)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau)) (r / 2) →
        (∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ a)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage a) (N.activeStage_mono ha') y),
          (a' : ℝ) = a - ℓ * r ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwa : w ≤ a),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
              (σ * r) ∧
            ENNReal.ofReal (wst * (σ * r) ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwa))
                (σ * r)) →
        ∃ (ae : Icc (0 : ℝ) N.horizon) (haa : ae ≤ a)
          (Z : BackwardPointTrace N (N.activeStage ae) (N.activeStage a) (N.activeStage_mono haa)
            (X.point (N.activeStage a) le_rfl (N.activeStage_mono hau))),
          (ae : ℝ) = a - c * r ^ 2 ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) (20 * r),
              Real.sqrt (normSq0S (N.stageMetric (N.activeStage v) v) q 4
                (metricRm04At (N.stageMetric (N.activeStage v) v) q)) ≤ B / r ^ 2) ∧
          (∀ (i : Fin N.eventCount) (hf : N.activeStage ae ≤ i.castSucc)
              (hl : i.succ ≤ N.activeStage u) (U : Set (N.stage i.succ).Carrier),
            U ⊆ riemannianBallOf (N.event i).outputMetric
              ((X.concat Z).point i.succ (hf.trans i.castSucc_lt_succ.le) hl) (20 * r) →
            IsPreconnected U →
            (∀ y ∈ U, metricScalarAt (N.event i).outputMetric y ≤ (9 * B) / r ^ 2) →
            ∀ (x' : (N.event i).incoming.terminalRegularOpen) (y : (N.stage i.succ).Carrier),
              y ∈ U → (N.event i).RegularCrossing x'.val y →
              U ⊆ interior (range (N.event i).oldOutput)) ∧
          (∀ (v : Icc (0 : ℝ) N.horizon) (hav : ae ≤ v) (hvu : v ≤ u),
            ∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v)
                ((X.concat Z).point (N.activeStage v) (N.activeStage_mono hav)
                  (N.activeStage_mono hvu)) r,
              SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r ^ 2)⁻¹)) :=
  hU_v2b_of_parts_O71 Hp (seedStrip_big_O69 Hp) ((hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof)
    (hrc_of_hdec_S118 Hp hdec)

end GC.LongTime.Ch12
