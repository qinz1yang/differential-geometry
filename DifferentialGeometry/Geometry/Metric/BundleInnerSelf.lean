import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import DifferentialGeometry.Bundle.ContinuousLinearMapSection.PointwiseSmoothness

/-!
# Riemannian bundles from a smooth squared fibre norm

Let `V` be a topological vector bundle over a `C^n` manifold whose fibres carry inner products
(no smoothness of the bundle itself is needed). If the squared fibre norm
`z ↦ ⟪z, z⟫` is a smooth function on the total space, then the fibrewise inner products form a
smooth Riemannian structure, `IsContMDiffRiemannianBundle`. In a local trivialization `e` the
coordinate bilinear form at `b` is `(v, w) ↦ ⟪e⁻¹_b v, e⁻¹_b w⟫`, which by polarization is a
combination of the squared norm along the smooth local sections `b ↦ e⁻¹_b u`.

Mathlib provides the converse direction (`ContMDiffWithinAt.inner_bundle`).
-/

set_option autoImplicit false

noncomputable section

open Bundle ContinuousLinearMap Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Metric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)] [FiberBundle F V] [VectorBundle ℝ F V]

omit [FiniteDimensional ℝ F] in
/-- A local trivialization's inverse applied to a fixed model vector is a smooth local section
near the base point of the trivialization. -/
theorem contMDiffAt_trivializationAt_symmL_section (b₀ : B) (u : F) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n
      (fun b => TotalSpace.mk' F b ((trivializationAt F V b₀).symmL ℝ b u)) b₀ := by
  let e := trivializationAt F V b₀
  have hb₀ : b₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V b₀
  rw [contMDiffAt_section]
  apply (contMDiffAt_const (c := u)).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hb₀] with b hb
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb]
  exact e.continuousLinearMapAt_symmL hb u

/-- **Smooth Riemannian structure from a smooth squared fibre norm.** -/
theorem isContMDiffRiemannianBundle_of_contMDiff_inner_self
    (h : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) n
      (fun z : TotalSpace F V => inner ℝ z.2 z.2)) :
    IsContMDiffRiemannianBundle IB n F V := by
  refine ⟨fun _ => innerSL ℝ, ?_, fun _ _ _ => rfl⟩
  intro b₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise
  intro v
  apply contMDiffAt_clm_of_pointwise
  intro w
  let e := trivializationAt F V b₀
  have hb₀ : b₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V b₀
  have hQ (u : F) : ContMDiffAt IB 𝓘(ℝ, ℝ) n
      (fun b => inner ℝ (e.symmL ℝ b u) (e.symmL ℝ b u)) b₀ :=
    (h _).comp b₀ (contMDiffAt_trivializationAt_symmL_section (n := n) b₀ u)
  have hpol := (ContMDiffAt.sub (ContMDiffAt.sub (hQ (v + w)) (hQ v)) (hQ w)).div_const 2
  apply hpol.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hb₀] with b hb
  rw [inCoordinates_apply_eq₂ hb hb (by simp)]
  simp only [map_add, real_inner_add_add_self]
  change (Trivialization.linearMapAt ℝ (Bundle.Trivial.trivialization B ℝ) b) _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply, innerSL_apply_apply]
  have hsymm (u : F) : e.symmL ℝ b u = (trivializationAt F V b₀).symm b u :=
    e.symmL_apply (R := ℝ) hb u
  rw [hsymm v, hsymm w]
  ring

/-- **Smooth Riemannian structure from a smooth squared fibre norm**, norm form. -/
theorem isContMDiffRiemannianBundle_of_contMDiff_norm_sq
    (h : ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) n (fun z : TotalSpace F V => ‖z.2‖ ^ 2)) :
    IsContMDiffRiemannianBundle IB n F V :=
  isContMDiffRiemannianBundle_of_contMDiff_inner_self
    (h.congr fun z => real_inner_self_eq_norm_sq z.2)

end DifferentialGeometry.Geometry.Metric
