import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBound_O22
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Pinch_O16

/-!
# CH12-O22 G2 (b3), slice form: `R ≤ M` ⇒ `|Rm| ≤ C M` on every slice-history stage

Combines `hpinchS_O16` (Hamilton–Ivey pinching on the slice history, admissible `Phi`) with
`sqrt_normSq_le_of_pinching_O22`.  The output is in the exact `Real.sqrt (normSq0S … 4
(metricRm04At …))` form of the `hbound` input of `slice_seed_tracedRegion_CX2`.
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

/-- (b3) on the slice history: one constant `C` (depending only on the pinching of `Hp`) with
`|Rm| ≤ C M` wherever `R ≤ M`, `1 ≤ M`, at every stage time `v ≤ top`. -/
theorem slice_rm_bound_of_scalar_O22 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : RegularSlice F.observation) (v : Icc (0 : ℝ) s.history.horizon),
      v ≤ sliceTop_S8 s → ∀ (x : (s.history.stageAt v).Carrier) (Mb : ℝ), 1 ≤ Mb →
      metricScalarAt (s.history.stageMetric (s.history.activeStage v) v) x ≤ Mb →
      Real.sqrt (normSq0S (s.history.stageMetric (s.history.activeStage v) v) x 4
        (metricRm04At (s.history.stageMetric (s.history.activeStage v) v) x)) ≤ C * Mb := by
  obtain ⟨Phi, hPhi, hpin⟩ := hpinchS_O16 Hp
  refine ⟨Real.sqrt 3 * (1 + 4 * Phi 1), ?_, ?_⟩
  · have := hPhi.pos 1
    have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  intro s v hv x Mb hM hR
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := finrank_euclideanSpace_fin
  exact sqrt_normSq_le_of_pinching_O22 hPhi _ x hdim hM (hpin s v hv x) hR

end GC.LongTime.Ch12
