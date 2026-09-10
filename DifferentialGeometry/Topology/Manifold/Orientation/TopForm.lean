import DifferentialGeometry.Bundle.Orientation.TopForm
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

open Set Bundle Module DifferentialGeometry.ContinuousAlternatingMap
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.Orientation

variable {m : ℕ} {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_continuous_tangentTopForm (hm : finrank ℝ E = m)
    (o : ∀ x : M, _root_.Orientation ℝ (TangentSpace I x) (Fin m))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I) o) :
    ∃ η : ∀ x : M, TangentSpace I x [⋀^Fin m]→L[ℝ] ℝ,
      Continuous (fun x => TotalSpace.mk' (E [⋀^Fin m]→L[ℝ] ℝ) x (η x)) ∧
      (∀ x, η x ≠ 0) ∧ ∀ x, η x ∈ positiveForms (o x) := by
  obtain ⟨η, hη, hpos⟩ :=
    DifferentialGeometry.VectorBundle.exists_continuous_topForm_of_isCompatibleOrientation
      I (TangentSpace I) hm o ho
  exact ⟨η, hη, fun x => ne_zero_of_mem_positiveForms (hpos x), hpos⟩

omit [FiniteDimensional ℝ E] in
theorem isCompatibleOrientation_model (p : _root_.Orientation ℝ E (Fin m)) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace 𝓘(ℝ, E))
      (fun _ : E => p) := by
  intro x
  let t := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hbase (y : E) : y ∈ t.baseSet := mem_univ y
  refine ⟨t, inferInstance, univ, Filter.univ_mem, (fun y _ => hbase y), p, ?_⟩
  intro y hy
  let e : E ≃L[ℝ] E := t.continuousLinearEquivAt ℝ y (hbase y)
  change (_root_.Orientation.map (Fin m) e.toLinearEquiv) p = p
  have heq : e = ContinuousLinearEquiv.refl ℝ E := by
    ext v
    change (t.continuousLinearEquivAt ℝ y (hbase y) : E → E) v = v
    rw [Trivialization.coe_continuousLinearEquivAt_eq,
      TangentBundle.continuousLinearMapAt_model_space]
    rfl
  rw [heq]
  exact congrArg (fun q => q p) (_root_.Orientation.map_refl (Fin m))

end DifferentialGeometry.Manifold.Orientation
