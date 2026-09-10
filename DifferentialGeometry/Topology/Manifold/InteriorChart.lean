import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false
open Set
open scoped Manifold ContDiff
noncomputable section
namespace Poincare.Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M]

def interiorChart (x : M) : PartialDiffeomorph I 𝓘(𝕜, E) M E n where
  toFun := extChartAt I x
  invFun := (extChartAt I x).symm
  source := (chartAt H x).source ∩ (extChartAt I x) ⁻¹' interior (extChartAt I x).target
  target := interior (extChartAt I x).target
  map_source' _ hy := hy.2
  map_target' y hy := by
    refine ⟨?_, ?_⟩
    · simpa only [extChartAt_source] using (extChartAt I x).map_target (interior_subset hy)
    · change extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
      rw [(extChartAt I x).right_inv (interior_subset hy)]
      exact hy
  left_inv' y hy := (extChartAt I x).left_inv (by simpa only [extChartAt_source] using hy.1)
  right_inv' _ hy := (extChartAt I x).right_inv (interior_subset hy)
  open_source := isOpen_extChartAt_preimage x isOpen_interior
  open_target := isOpen_interior
  contMDiffOn_toFun := contMDiffOn_extChartAt.mono inter_subset_left
  contMDiffOn_invFun := (contMDiffOn_extChartAt_symm x).mono interior_subset


@[simp]
theorem interiorChart_apply (x y : M) : interiorChart I n x y = extChartAt I x y := rfl


@[simp]
theorem interiorChart_symm_apply (x : M) (y : E) :
    (interiorChart I n x).symm y = (extChartAt I x).symm y := rfl


@[simp]
theorem interiorChart_source (x : M) :
    (interiorChart I n x).source =
      (chartAt H x).source ∩ (extChartAt I x) ⁻¹' interior (extChartAt I x).target := rfl


@[simp]
theorem interiorChart_target (x : M) :
    (interiorChart I n x).target = interior (extChartAt I x).target := rfl

theorem mem_interiorChart_source_iff (x : M) :
    x ∈ (interiorChart I n x).source ↔ I.IsInteriorPoint x := by
  simp only [interiorChart_source, mem_inter_iff, mem_chart_source, true_and, mem_preimage]
  exact I.isInteriorPoint_iff.symm


theorem isInteriorPoint_of_mem_interiorChart_source (hn : n ≠ 0) {x y : M}
    (hy : y ∈ (interiorChart I n x).source) : I.IsInteriorPoint y :=
  (I.isInteriorPoint_iff_of_mem_atlas hn (chart_mem_atlas H x) hy.1).mpr hy.2

omit [IsManifold I n M] in
theorem isInteriorPoint_of_model_partialDiffeomorph
    (f : PartialDiffeomorph 𝓘(𝕜, E) I E M n) (hn : n ≠ 0)
    {x : E} (hx : x ∈ f.source) : I.IsInteriorPoint (f x) := by
  have hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) I n f x := ⟨f, hx, fun _ _ => rfl⟩
  exact (hf.isInteriorPoint_iff hn).mp BoundarylessManifold.isInteriorPoint

end Poincare.Manifold
