import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section
open Set Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

theorem exists_interior_coordinates {x : M} (hx : I.IsInteriorPoint x) :
    ∃ d : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞,
      x ∈ d.source ∧ d.source ⊆ I.interior M ∧
      (d : M → E) = extChartAt I x ∧ (d.symm : E → M) = (extChartAt I x).symm := by
  let p := extChartAt I x
  let S := p.source ∩ p ⁻¹' interior p.target
  have hS : IsOpen S := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) isOpen_interior
  let e : PartialEquiv M E :=
    { toFun := p
      invFun := p.symm
      source := S
      target := interior p.target
      map_source' := fun _ hy ↦ hy.2
      map_target' := fun y hy ↦ ⟨p.map_target (interior_subset hy), by
        change p (p.symm y) ∈ interior p.target
        rwa [p.right_inv (interior_subset hy)]⟩
      left_inv' := fun _ hy ↦ p.left_inv hy.1
      right_inv' := fun _ hy ↦ p.right_inv (interior_subset hy) }
  let d : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    { toPartialEquiv := e
      open_source := hS
      open_target := isOpen_interior
      contMDiffOn_toFun := (contMDiffOn_extChartAt (I := I) (x := x)).mono
        (fun y hy ↦ by simpa only [p, extChartAt_source] using hy.1)
      contMDiffOn_invFun := (contMDiffOn_extChartAt_symm x).mono interior_subset }
  refine ⟨d, ⟨mem_extChartAt_source x, I.isInteriorPoint_iff.mp hx⟩, ?_, rfl, rfl⟩
  intro y hy
  exact (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H x)
    (show y ∈ (chartAt H x).source by simpa only [p, extChartAt_source] using hy.1)).2 hy.2

end Poincare.Topology.Manifold
