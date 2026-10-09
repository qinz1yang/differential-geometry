import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.L862PrefixSectional_O37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86RmBound_O22
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRicciShift

/-!
# CH12-O37 G2d: scale-invariant `|Rm|` from a scalar bound on the tower prefix

On the prefix `v ≤ s.time` of `N := sliceTowerHistory_CX2 s`, at a late scale `r ≤ b √v`, a scalar
bound `R ≤ K / r²` gives `|Rm| ≤ 2√3 (K/2 + 2) / r²` (sectional lower bound `−r⁻²` from the fixed
Hamilton–Ivey region, then the dimension-three curvature-operator estimate). In Sublemma 86.6 this
converts the scalar bound `K₀ τ⁻¹ r⁻²` of `hKL82` into the parent's curvature bound with a constant
independent of the a-priori bound of the children (no circularity in the choice of `K`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow

namespace GC.LongTime.Ch12

universe u

/-- Scale-invariant curvature bound from a scalar bound, on the tower prefix. -/
theorem rm_of_scalar_prefix_O37
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ b : ℝ, 0 < b ∧ ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (v : ℝ) ≤ s.time →
      ∀ (x : ((sliceTowerHistory_CX2 s).stageAt v).Carrier) (r : ℝ),
      0 < r → r ≤ b * Real.sqrt v →
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ K / r ^ 2 →
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x)) ≤
        2 * Real.sqrt 3 * (K / 2 + 2) / r ^ 2 := by
  obtain ⟨b, hb, hsec⟩ := sectional_of_scalar_prefix_O37 Hp hK
  refine ⟨b, hb, fun s v hvs x r hr hrb hR => ?_⟩
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  have hs := hsec s v hvs x r hr hrb hR
  have hlow :=
    (DimensionThree.sectionalBoundedBelowAt_iff_curvatureOperatorLowerBoundAt hdim).mp hs
  have h := sqrt_normSq_le_of_lowerBound_O22 _ x hdim (L := (r ^ 2)⁻¹) (Rb := K / r ^ 2)
    (by positivity) (by positivity) hlow hR
  have he : 2 * Real.sqrt 3 * (K / r ^ 2 / 2 + 2 * (r ^ 2)⁻¹) =
      2 * Real.sqrt 3 * (K / 2 + 2) / r ^ 2 := by
    field_simp
  exact h.trans_eq he

end GC.LongTime.Ch12
