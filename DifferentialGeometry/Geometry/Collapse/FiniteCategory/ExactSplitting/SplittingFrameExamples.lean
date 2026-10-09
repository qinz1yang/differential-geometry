import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrameLinear

/-!
# Actual real-line consumers of the linear splitting frame

The finite-order Euclidean metric and original real-line product isometry instantiate both
the metric identity and the exponential identity without additional geometric inputs.
-/

set_option autoImplicit false

noncomputable section

open Bundle WithLp
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local instance realFrameDimension : NeZero (Module.finrank ℝ ℝ) :=
  ⟨by rw [Module.finrank_self]; decide⟩

def realFrameMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) 3 ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _) :=
  { inner := (riemannianMetricVectorSpace ℝ).inner
    symm := (riemannianMetricVectorSpace ℝ).symm
    pos := (riemannianMetricVectorSpace ℝ).pos
    isVonNBounded := (riemannianMetricVectorSpace ℝ).isVonNBounded
    contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le le_top }

def realFrameSplitting : ℝ ≃ᵢ WithLp 2 (ℝ × PUnit) :=
  (IsometryEquiv.withLpProdUnique 2 ℝ PUnit).symm

private theorem realFrame_enorm : ∀ (x : ℝ) (w : TangentSpace 𝓘(ℝ, ℝ) x),
    ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (realFrameMetric.inner x w w)) := by
  intro x w
  change ‖(w : ℝ)‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ (w : ℝ) w))
  rw [← norm_eq_sqrt_real_inner, ← ofReal_norm]

theorem real_splittingFrame_inner (x u v : ℝ) :
    realFrameMetric.inner x (splittingFrame (r := 2) realFrameMetric realFrameSplitting x u)
      (splittingFrame (r := 2) realFrameMetric realFrameSplitting x v) = inner ℝ u v :=
  inner_splittingFrame (r := 2) realFrameMetric le_rfl realFrame_enorm realFrameSplitting x u v

theorem real_splittingFrame_expMap (x u s : ℝ) :
    realFrameMetric.expMap (⟨x, s • splittingFrame (r := 2) realFrameMetric realFrameSplitting
      x u⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) = realFrameSplitting.symm
      (toLp 2 ((realFrameSplitting x).fst + s • u, (realFrameSplitting x).snd)) :=
  expMap_splittingFrame (r := 2) realFrameMetric le_rfl realFrame_enorm realFrameSplitting x u s

end DifferentialGeometry.Geometry.ExactSplitting
