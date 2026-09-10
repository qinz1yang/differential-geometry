import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mpullback_openSubtype_symm (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (V : ∀ x : U, TangentSpace I x) {x : M} (hx : x ∈ U) :
    _root_.VectorField.mpullback I I (openSubtypePartialDiffeomorph I U hU).symm V x =
      V ⟨x, hx⟩ := by
  let f := openSubtypePartialDiffeomorph I U hU
  have hxf : x ∈ f.symm.source := by simpa [f] using hx
  change (mfderiv I I f.symm x).inverse (V (f.symm x)) = V ⟨x, hx⟩
  rw [Poincare.VectorField.inverse_mfderiv_partialDiffeomorph f.symm (by simp) hxf]
  have hi : mfderiv I I f.symm.symm (f.symm x) = ContinuousLinearMap.id ℝ E :=
    DifferentialGeometry.mfderiv_subtype_val U (f.symm x)
  rw [hi]
  change V (f.symm x) = V ⟨x, hx⟩
  rw [openSubtypePartialDiffeomorph_symm_apply I U hU hx]

theorem mpullback_openSubtype (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (V : ∀ x : M, TangentSpace I x) (x : U) :
    _root_.VectorField.mpullback I I (openSubtypePartialDiffeomorph I U hU) V x =
      V x.val := by
  change (mfderiv I I (Subtype.val : U → M) x).inverse (V x.val) = V x.val
  rw [DifferentialGeometry.mfderiv_subtype_val]
  change (ContinuousLinearEquiv.refl ℝ E).toContinuousLinearMap.inverse (V x.val) = V x.val
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

end Poincare.Manifold
