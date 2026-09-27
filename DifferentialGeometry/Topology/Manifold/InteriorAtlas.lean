import DifferentialGeometry.Topology.Manifold.InteriorChart
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [IsManifold I n M]
  [BoundarylessManifold I M]

@[reducible]
def interiorChartedSpace : ChartedSpace E M where
  atlas := range (fun x : M => (interiorChart I n x).toOpenPartialHomeomorph)
  chartAt x := (interiorChart I n x).toOpenPartialHomeomorph
  mem_chart_source x :=
    (mem_interiorChart_source_iff I n x).mpr BoundarylessManifold.isInteriorPoint
  chart_mem_atlas x := ⟨x, rfl⟩


theorem extChartAt_interiorAtlas_apply (x y : M) :
    let _ := interiorChartedSpace I n (M := M)
    extChartAt 𝓘(𝕜, E) x y = extChartAt I x y := rfl

theorem extChartAt_interiorAtlas_symm_apply (x : M) (y : E) :
    let _ := interiorChartedSpace I n (M := M)
    (extChartAt 𝓘(𝕜, E) x).symm y = (extChartAt I x).symm y := rfl

theorem interiorIsManifold :
    let _ := interiorChartedSpace I n (M := M)
    IsManifold 𝓘(𝕜, E) n M := by
  let _ := interiorChartedSpace I n (M := M)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨y, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ]
  convert! contMDiffOn_iff_contDiffOn.mp
    ((interiorChart I n x).symm.trans (interiorChart I n y)).contMDiffOn


theorem contMDiff_interiorAtlas_id :
    let _ := interiorChartedSpace I n (M := M)
    ContMDiff 𝓘(𝕜, E) I n (id : M → M) := by
  let _ := interiorChartedSpace I n (M := M)
  change ContMDiff 𝓘(𝕜, E) I n (id : M → M)
  intro x
  rw [contMDiffAt_iff_source]
  have hx := (mem_interiorChart_source_iff I n x).mpr
    BoundarylessManifold.isInteriorPoint
  have h := (interiorChart I n x).symm.contMDiffOn.contMDiffAt
    ((interiorChart I n x).open_target.mem_nhds ((interiorChart I n x).map_source hx))
  simp only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ,
    Function.id_comp]
  change ContMDiffAt 𝓘(𝕜, E) I n (fun y => (extChartAt I x).symm y)
    (extChartAt I x x)
  exact h


theorem contMDiff_id_interiorAtlas :
    let _ := interiorChartedSpace I n (M := M)
    ContMDiff I 𝓘(𝕜, E) n (id : M → M) := by
  let _ := interiorChartedSpace I n (M := M)
  change ContMDiff I 𝓘(𝕜, E) n (id : M → M)
  intro x
  rw [contMDiffAt_iff_target]
  refine ⟨continuousAt_id, ?_⟩
  change ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x
  exact contMDiffAt_extChartAt

def interiorAtlasDiffeomorph :
    let _ := interiorChartedSpace I n (M := M)
    M ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ M := by
  let _ := interiorChartedSpace I n (M := M)
  exact { toEquiv := Equiv.refl M
          contMDiff_toFun := contMDiff_id_interiorAtlas I n
          contMDiff_invFun := contMDiff_interiorAtlas_id I n }


@[simp]
theorem interiorAtlasDiffeomorph_apply (x : M) :
    interiorAtlasDiffeomorph I n x = x := rfl


theorem interiorAtlasDiffeomorph_symm_apply (x : M) :
    let _ := interiorChartedSpace I n (M := M)
    (interiorAtlasDiffeomorph I n).symm x = x := rfl

omit [BoundarylessManifold I M] in
def intrinsicInterior (hn : n ≠ 0) : TopologicalSpace.Opens M :=
  ⟨I.interior M, I.isOpen_interior hn⟩

omit [BoundarylessManifold I M] in
instance boundarylessManifold_intrinsicInterior (hn : n ≠ 0) :
    BoundarylessManifold I (intrinsicInterior I n hn (M := M)) where
  isInteriorPoint' x := I.isInteriorPoint_iff_isInteriorPoint_val.mpr x.property

omit [BoundarylessManifold I M] in
theorem contMDiff_intrinsicInterior_val (hn : n ≠ 0) :
    let _ := interiorChartedSpace I n (M := intrinsicInterior I n hn (M := M))
    ContMDiff 𝓘(𝕜, E) I n
      (Subtype.val : intrinsicInterior I n hn (M := M) → M) := by
  let U := intrinsicInterior I n hn (M := M)
  let _ := interiorChartedSpace I n (M := U)
  exact (contMDiff_subtype_val (I := I) (U := U)).comp
    (contMDiff_interiorAtlas_id I n (M := U))

end DifferentialGeometry.Manifold
