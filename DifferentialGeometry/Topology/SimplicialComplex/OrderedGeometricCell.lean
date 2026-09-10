import DifferentialGeometry.Topology.SimplicialComplex.OrderedCellAttachment
import DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationMap
import DifferentialGeometry.Topology.SimplicialComplex.GeometricFaceHomeomorphism
import DifferentialGeometry.Topology.Simplex.Reindex
import DifferentialGeometry.Topology.SimplicialSet.BoundaryRealization
import DifferentialGeometry.Topology.Category.TopCat.ClosedCover

set_option autoImplicit false
noncomputable section
open CategoryTheory Simplicial Opposite

namespace Poincare.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (hs : s ∈ K.faces)
  {n : ℕ} (hn : s.card = n + 1)

def orderedFaceRealizationHomeomorph :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≃ₜ convexHull ℝ (s : Set E) :=
  (SimplexCategory.toTopHomeo ⦋n⦌).trans
    ((Poincare.Simplex.reindexHomeomorph (s.orderIsoOfFin hn).toEquiv).trans
      (geometricFaceHomeomorphism K hs))


@[simp]
theorem orderedFaceRealizationHomeomorph_apply (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) =
      ∑ i, (SimplexCategory.toTopHomeo ⦋n⦌ x).val i • (s.orderEmbOfFin hn) i := by
  exact Poincare.Simplex.vertexMap_reindex (s.orderIsoOfFin hn).toEquiv
    (fun i : s ↦ (i : E)) (SimplexCategory.toTopHomeo ⦋n⦌ x)

theorem orderedFaceCellMap_geometricRealizationMap_apply
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    geometricRealizationMap K
        (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) =
      geometricSimplexMap K
        (orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn).val
        (SimplexCategory.toTopHomeo ⦋n⦌ x) := by
  let a := (orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn).val
  have hu : (TopCat.toSSetObjEquiv _ (op ⦋n⦌))
      ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app _ a)
        (SimplexCategory.toTopHomeo ⦋n⦌ x) =
      SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x := by
    change (((sSetTopAdj.unit.app
      (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app (op ⦋n⦌) a).down).hom
        (ULift.up (SimplexCategory.toTopHomeo ⦋n⦌ x)) = _
    rw [sSetTopAdj_unit_app_app_down]
    change SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn)
      ((SimplexCategory.toTopHomeo ⦋n⦌).symm (SimplexCategory.toTopHomeo ⦋n⦌ x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← hu]
  exact geometricRealizationMap_unit_apply K a _

@[reassoc]
theorem orderedFaceCellMap_geometricRealizationMap :
    SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) ≫
        geometricRealizationMap K =
      (TopCat.isoOfHomeo (orderedFaceRealizationHomeomorph K s hs hn)).hom ≫
        Poincare.TopCat.subspaceInclusion
          (Geometry.SimplicialComplex.convexHull_subset_space hs) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  change (geometricRealizationMap K
    (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) =
      (orderedFaceRealizationHomeomorph K s hs hn x : E)
  rw [orderedFaceCellMap_geometricRealizationMap_apply,
    orderedFaceRealizationHomeomorph_apply]
  rfl

theorem orderedFaceRealizationHomeomorph_mem_costar_iff
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) ∈ (geometricFaceCostar K s).space ↔
      SimplexCategory.toTopHomeo ⦋n⦌ x ∈ Poincare.Simplex.boundary (Fin (n + 1)) := by
  change Poincare.Simplex.vertexMap (fun i : s ↦ (i : E))
    (Poincare.Simplex.reindexHomeomorph (s.orderIsoOfFin hn).toEquiv
      (SimplexCategory.toTopHomeo ⦋n⦌ x)) ∈ (geometricFaceCostar K s).space ↔ _
  rw [vertexMap_mem_geometricFaceCostar_iff K hs,
    Poincare.Simplex.reindexHomeomorph_mem_boundary]

theorem orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (orderedFaceRealizationHomeomorph K s hs hn x : E) ∈ (geometricFaceCostar K s).space ↔
      x ∈ Set.range (SSet.toTop.map (SSet.boundary n).ι) := by
  rw [orderedFaceRealizationHomeomorph_mem_costar_iff]
  have hr := Poincare.SSet.range_toTopHomeo_boundary.{u} n
  constructor
  · intro hx
    have hx' : SimplexCategory.toTopHomeo ⦋n⦌ x ∈ Set.range
        (fun y : SSet.toTop.obj (SSet.boundary n : SSet.{u}) ↦
          SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y)) := by
      rw [hr]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, (SimplexCategory.toTopHomeo ⦋n⦌).injective hy⟩
  · rintro ⟨y, rfl⟩
    have hx : SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y) ∈
        Set.range (fun y : SSet.toTop.obj (SSet.boundary n : SSet.{u}) ↦
          SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map (SSet.boundary n).ι y)) := ⟨y, rfl⟩
    rwa [hr] at hx

theorem orderedFaceCellMap_geometricRealizationMap_mem_costar_iff
    (x : SSet.toTop.obj (Δ[n] : SSet.{u})) :
    (geometricRealizationMap K
      (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) ∈
        (geometricFaceCostar K s).space ↔
      x ∈ Set.range (SSet.toTop.map (SSet.boundary n).ι) := by
  have he := congrArg Subtype.val
    (ConcreteCategory.congr_hom (orderedFaceCellMap_geometricRealizationMap K s hs hn) x)
  change (geometricRealizationMap K
    (SSet.toTop.map (orderedFaceCellMap K.toPreAbstractSimplicialComplex s hs hn) x) : E) =
      (orderedFaceRealizationHomeomorph K s hs hn x : E) at he
  rw [he]
  exact orderedFaceRealizationHomeomorph_mem_costar_iff_mem_boundary_range K s hs hn x

end Poincare.Topology.SimplicialComplex
