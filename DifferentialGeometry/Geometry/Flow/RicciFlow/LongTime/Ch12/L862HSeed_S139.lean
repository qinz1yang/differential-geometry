import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862SeedStripGen_S139
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862TraceFamily_CX12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer

/-!
# CH12-S139 G2: `hSeed_S139` = `child_to_seedStrip866` (hSeed of `[FROZEN] CH12-O57 G2`)

`hSeed_S139 Hp : <hSeed binder text of frozen_seedStrip_O57, verbatim>`, from `seedStrip_gen_S139`
(G1, general observed history) applied to the slice tower history `N = sliceTowerHistory_CX2 s`.
The pinching input of the KL82.1 seed lemma on the whole prefix `v' ≤ v` of `N` is
`tower_pinching_S139` (fixed Hamilton--Ivey region of every stage metric of every tower history,
`history_region_O3`, turned into `curvatureOperatorLowerBoundAt` exactly as in
`slice_pinching_input_CX12`); it holds for all `v ≤ N.horizon`, so the frozen binder needs no
`v ≤ s.time` premise.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Curvature.DimensionThree
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- One admissible pinching function for the stage metrics of every history of the tower, at
every time of its horizon (not only on the prefix `v ≤ s.time` of a slice). -/
theorem tower_pinching_S139 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (m : ℕ) (v : Icc (0 : ℝ) (F.tower.history m).toHistory.horizon), ∀ x,
        curvatureOperatorLowerBoundAt
          ((F.tower.history m).toHistory.stageMetric
            ((F.tower.history m).toHistory.activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt
            ((F.tower.history m).toHistory.stageMetric
              ((F.tower.history m).toHistory.activeStage v) v) x)
          (Phi (metricScalarAt
            ((F.tower.history m).toHistory.stageMetric
              ((F.tower.history m).toHistory.activeStage v) v) x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      Hp.pinchingShift_pos
  refine ⟨Phi, hPhi, fun m v x => ?_⟩
  let gm := (F.tower.history m).toHistory.stageMetric
    ((F.tower.history m).toHistory.activeStage v) v
  have hvm : (v : ℝ) ≤ (m : ℝ) := by
    have h := v.2.2
    have e : ((F.tower.history m).toHistory).horizon = (m : ℝ) := F.tower.horizon_eq m
    exact h.trans (le_of_eq e)
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt gm x hdim
  have hreg := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion gm
    (Hp.pinchingShift + v) x).mp (history_region_O3 Hp m v v.2.1 hvm _ rfl x)
  have hb := hbound (Hp.pinchingShift + v) (le_add_of_nonneg_right v.2.1) _ _ hreg
  have hp := hPhi.pos (metricScalarAt gm x)
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin gm x basis horth] at hb
  exact (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le gm basis horth).mpr (by linarith)

/-- **G2** `hSeed_S139` (`child_to_seedStrip866`): the binder type of `frozen_seedStrip_O57`,
verbatim. -/
theorem hSeed_S139 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∀ ε K κ τ₁ τ₂ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < K → 0 < κ → 0 < τ₁ → 0 < τ₂ →
      ∃ σ ℓ wst : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < ℓ ∧ ℓ ≤ τ₁ ∧ 0 < wst ∧
      ∀ s : RegularSlice F.observation, let N := sliceTowerHistory_CX2 s;
      ∀ (v : Icc (0 : ℝ) N.horizon) (y : (N.stageAt v).Carrier) (r' : ℝ), 0 < r' →
        (∀ q ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v) y r',
          SectionalBoundedBelowAt (N.stageMetric (N.activeStage v) v) q (-(r' ^ 2)⁻¹)) →
        (∀ z ∈ riemannianBallOf (N.stageMetric (N.activeStage v) v) y r',
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ r' →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * ρ ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage v) v) z ρ) →
        (∃ (a : Icc (0 : ℝ) N.horizon) (hav : a ≤ v)
          (X : BackwardPointTrace N (N.activeStage a) (N.activeStage v) (N.activeStage_mono hav) y),
          (a : ℝ) = v - τ₁ * r' ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a ≤ w) (hwv : w ≤ v),
            N.isTracedRegion w
              (X.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
              (κ * r') (τ₂ * r' ^ 2) (K * (r' ^ 2)⁻¹)) →
        ∃ (a' : Icc (0 : ℝ) N.horizon) (ha' : a' ≤ v)
          (Y : BackwardPointTrace N (N.activeStage a') (N.activeStage v) (N.activeStage_mono ha') y),
          (a' : ℝ) = v - ℓ * r' ^ 2 ∧
          ∀ (w : Icc (0 : ℝ) N.horizon) (haw : a' ≤ w) (hwv : w ≤ v),
            hasSmallParabolicCurvature N w
              (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
              (σ * r') ∧
            ENNReal.ofReal (wst * (σ * r') ^ 3) ≤
              ballVolume (N.stageMetric (N.activeStage w) w)
                (Y.point (N.activeStage w) (N.activeStage_mono haw) (N.activeStage_mono hwv))
                (σ * r') := by
  obtain ⟨Phi, hPhi, hpin⟩ := tower_pinching_S139 Hp
  intro ε K κ τ₁ τ₂ hε hε2 hK hκ hτ₁ hτ₂
  obtain ⟨σ, ℓ, wst, hσ, hσ1, hℓ, hℓτ, hwst, hgen⟩ :=
    seedStrip_gen_S139.{u} ε K κ τ₁ τ₂ hε hε2 hK hκ hτ₁ hτ₂
  refine ⟨σ, ℓ, wst, hσ, hσ1, hℓ, hℓτ, hwst, fun s => ?_⟩
  intro N v y r' hr' hsec hvol hgood
  exact hgen (sliceTowerHistory_CX2 s) hPhi v
    (fun v' _ x => hpin (sliceTowerIndex_CX2 s) v' x) y r' hr' hsec hvol hgood

end GC.LongTime.Ch12
