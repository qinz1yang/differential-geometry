import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Lie brackets of chart-constant fields and of their pullbacks vanish

`FiberBundle.extend E v` is the vector field which is constant, equal to `v`, in the chart at the
base point `x` of `v`. Boundary and corners are allowed throughout.

* `mlieBracket_fiberBundleExtend_eq_zero`: the Lie bracket of two such fields vanishes at `x`;
* `mlieBracket_mpullback_fiberBundleExtend_eq_zero`: if `f` is `C²` at `x₀`, the pullbacks
  `f^* (extend v)`, `f^* (extend w)` of two chart-constant fields at `f x₀` have vanishing bracket
  at `x₀` (naturality of the bracket, `VectorField.mpullback_mlieBracket`). For a local inverse
  `f` of a `C²` embedding these pullbacks are the pushforwards of chart-constant fields.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter FiberBundle
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A chart-constant field is the inverse trivialization applied to the coordinates of its value at
the base point. -/
theorem fiberBundleExtend_eq_symmL
    (x : M) (v : TangentSpace I x) {y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    FiberBundle.extend E v y =
      (trivializationAt E (TangentSpace I) x).symmL ℝ y
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v) := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  unfold FiberBundle.extend
  rw [e.symmL_apply hy, e.apply_eq_prod_continuousLinearEquivAt ℝ x hx v]
  apply congrArg (e.symm y)
  exact congrFun (e.coe_continuousLinearEquivAt_eq (R := ℝ) hx) v

private theorem extendBracket_pullback_eventuallyEq (x : M) (v : TangentSpace I x) :
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
        (FiberBundle.extend E v) (Set.range I) =ᶠ[nhdsWithin (extChartAt I x x)
          ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I)]
      fun _ : E => (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v := by
  rw [preimage_univ, univ_inter]
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
  simp only [VectorField.mpullbackWithin_apply]
  have hysrc : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x).map_target hy
  have hybase : (extChartAt I x).symm y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hysrc
  rw [fiberBundleExtend_eq_symmL (I := I) x v hybase]
  rw [TangentBundle.symmL_trivializationAt hysrc]
  rw [(extChartAt I x).right_inv hy]
  exact ContinuousLinearMap.IsInvertible.inverse_apply_self
    (isInvertible_mfderivWithin_extChartAt_symm (I := I) hy) _

/-- The Lie bracket of two chart-constant fields vanishes at the base point. -/
theorem mlieBracket_fiberBundleExtend_eq_zero (x : M) (v w : TangentSpace I x) :
    VectorField.mlieBracket I (FiberBundle.extend E v) (FiberBundle.extend E w) x = 0 := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply]
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (extendBracket_pullback_eventuallyEq x v) (extendBracket_pullback_eventuallyEq x w)
    (by simp)]
  rw [show VectorField.lieBracketWithin ℝ
      (fun _ : E => (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)
      (fun _ : E => (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w)
      ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x) = 0 by
    simp [VectorField.lieBracketWithin]]
  exact ContinuousLinearMap.map_zero _

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Pullbacks of chart-constant fields commute.** If `f` is `C²` at `x₀`, the pullbacks by `f`
of two fields that are constant in the chart at `f x₀` have vanishing Lie bracket at `x₀`. -/
theorem mlieBracket_mpullback_fiberBundleExtend_eq_zero {f : M → M'} {x₀ : M}
    (hf : ContMDiffAt I I' 2 f x₀) (v w : TangentSpace I' (f x₀)) :
    VectorField.mlieBracket I (VectorField.mpullback I I' f (FiberBundle.extend E' v))
      (VectorField.mpullback I I' f (FiberBundle.extend E' w)) x₀ = 0 := by
  have h2 : minSmoothness ℝ 2 = 2 := by rw [minSmoothness_of_isRCLikeNormedField]
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [h2]
    exact IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' (minSmoothness ℝ 2) M' := by
    rw [h2]
    exact IsManifold.of_le (n := ∞) (by simp)
  rw [← VectorField.mpullback_mlieBracket (FiberBundle.mdifferentiableAt_extend I' E' v)
    (FiberBundle.mdifferentiableAt_extend I' E' w) hf h2.le]
  rw [VectorField.mpullback_apply, mlieBracket_fiberBundleExtend_eq_zero]
  exact ContinuousLinearMap.map_zero _

/-- **Pullbacks of commuting fields commute.** If `f` is `C²` at `x₀` and the bracket of `V, W`
vanishes at `f x₀`, so does the bracket of their pullbacks at `x₀`. -/
theorem mlieBracket_mpullback_eq_zero {f : M → M'} {x₀ : M} (hf : ContMDiffAt I I' 2 f x₀)
    {V W : (y : M') → TangentSpace I' y}
    (hV : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E'))
      (fun y => (⟨y, V y⟩ : TotalSpace E' (TangentSpace I'))) (f x₀))
    (hW : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E'))
      (fun y => (⟨y, W y⟩ : TotalSpace E' (TangentSpace I'))) (f x₀))
    (h0 : VectorField.mlieBracket I' V W (f x₀) = 0) :
    VectorField.mlieBracket I (VectorField.mpullback I I' f V)
      (VectorField.mpullback I I' f W) x₀ = 0 := by
  have h2 : minSmoothness ℝ 2 = 2 := by rw [minSmoothness_of_isRCLikeNormedField]
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [h2]
    exact IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I' (minSmoothness ℝ 2) M' := by
    rw [h2]
    exact IsManifold.of_le (n := ∞) (by simp)
  rw [← VectorField.mpullback_mlieBracket hV hW hf h2.le, VectorField.mpullback_apply, h0]
  exact ContinuousLinearMap.map_zero _

end DifferentialGeometry.VectorField
