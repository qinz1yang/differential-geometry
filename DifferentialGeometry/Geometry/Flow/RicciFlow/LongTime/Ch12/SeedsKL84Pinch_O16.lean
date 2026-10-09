import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84GlueV2_O12
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer

/-!
# CH12-O16 G1: slice pinching `hpinchS` from `Hp.pinching`

`hpinchS_O16 Hp` is the `hpinchS` input of `hG2_of_kl82_v2_O12` (shape frozen in
`[FROZEN] CH12-O12 addendum`): one admissible pinching function `Phi` (depending only on the
profile) with `Rm ≥ -Phi(R)` (curvature-operator form) at every point of every stage of every slice
history, at every time `v ≤ sliceTop_S8 s`.

Proof: the fixed Hamilton–Ivey region of `Hp.pinching` at time `v` is transported to the active
stage of the slice history at `v` (`observe_slice_stage` / `observe_slice_metric` and
`postData_observe_O3`); the pointwise Hamilton–Ivey bound
`exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion` (shift `a₀ = pinchingShift`)
then gives the curvature-operator lower bound.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Curvature.DimensionThree
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

/-- Pointwise: a point in the fixed Hamilton–Ivey region with shift `a ≥ a₀` satisfies the
curvature-operator lower bound `Phi(R)`, for the admissible `Phi` of the pointwise HI lemma. -/
theorem curvatureOperatorLowerBoundAt_of_fixedHI_O16 {X : Type u} [TopologicalSpace X]
    [ChartedSpace ThreeSpace X] [IsManifold ThreeModel ∞ X] [T2Space X]
    {a₀ : ℝ} {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, a₀ ≤ a → ∀ R ν : ℝ,
      (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (gm : SmoothRiemannianMetric ThreeModel X) {a : ℝ} (ha : a₀ ≤ a) (x : X)
    (hx : InFixedHamiltonIveyRegion gm a x) :
    curvatureOperatorLowerBoundAt gm x (metricAlgebraicCurvatureTensorAt gm x)
      (Phi (metricScalarAt gm x)) := by
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt gm x hdim
  have hr := (inFixedHamiltonIveyRegion_iff_mem_fixedHamiltonIveyRegion gm a x).mp hx
  have hb := hbound a ha _ _ hr
  have hp := hPhi.pos (metricScalarAt gm x)
  rw [leastCurvatureOperatorEigenvalueAt_eq_sectionalMin gm x basis horth] at hb
  refine (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le gm basis horth).mpr ?_
  linarith

section Slice

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- The fixed Hamilton–Ivey region of `Hp.pinching`, on the active stage of the slice history at
any time `v` of the slice history. -/
theorem slice_history_region_O16 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (v : Icc (0 : ℝ) s.history.horizon) :
    ∀ x, InFixedHamiltonIveyRegion (s.history.stageMetric (s.history.activeStage v) v)
      (Hp.pinchingShift + v) x := by
  have hv0 : (0 : ℝ) ≤ v := v.2.1
  have hvs : (v : ℝ) ≤ s.time := v.2.2
  let t : Icc (0 : ℝ) (v : ℝ) := ⟨v, hv0, le_rfl⟩
  have hst := F.observation.observe_slice_stage v s.time hv0 s.positive.le hvs t
  have hmet := F.observation.observe_slice_metric v s.time hv0 s.positive.le hvs t
  obtain ⟨hs0, hm0⟩ := postData_observe_O3 F.observation v hv0
  have hlast : (F.observation.observe v hv0).activeStage t =
      Fin.last (F.observation.observe v hv0).eventCount :=
    (F.observation.observe v hv0).activeStage_at_horizon
  have hst' : postStage F.observation v = s.history.stageAt v := by
    refine hs0.trans ?_
    have h1 : (F.observation.observe v hv0).stageAt t =
        (F.observation.observe v hv0).stage (Fin.last _) := by
      change (F.observation.observe v hv0).stage ((F.observation.observe v hv0).activeStage t) = _
      rw [hlast]
    exact h1.symm.trans hst
  have hm' : HEq (postMetric F.observation v)
      (s.history.stageMetric (s.history.activeStage v) v) := by
    refine hm0.trans ?_
    refine (stageMetric_heq_of_index_eq_O3 _ hlast.symm (v : ℝ)).trans ?_
    exact hmet
  exact stageMetric_transport_O3 hst' hm'
    (fun Q m => ∀ x : Q.Carrier, InFixedHamiltonIveyRegion m (Hp.pinchingShift + v) x)
    (Hp.pinching v hv0)

/-- **G1 (`hpinchS`)**: the slice-form admissible pinching input of `hG2_of_kl82_v2_O12`, frozen
in `[FROZEN] CH12-O12 addendum`, from `Hp.pinching`. -/
theorem hpinchS_O16 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ s : RegularSlice F.observation, ∀ v : Icc (0 : ℝ) s.history.horizon, v ≤ sliceTop_S8 s →
        ∀ x, curvatureOperatorLowerBoundAt (s.history.stageMetric (s.history.activeStage v) v) x
          (metricAlgebraicCurvatureTensorAt (s.history.stageMetric (s.history.activeStage v) v) x)
          (Phi (metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x)) := by
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      Hp.pinchingShift_pos
  refine ⟨Phi, hPhi, fun s v _ x => ?_⟩
  have ha : Hp.pinchingShift ≤ Hp.pinchingShift + v := le_add_of_nonneg_right v.2.1
  exact curvatureOperatorLowerBoundAt_of_fixedHI_O16 hPhi hbound _ ha x
    (slice_history_region_O16 Hp s v x)

end Slice

end GC.LongTime.Ch12
