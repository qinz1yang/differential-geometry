import DifferentialGeometry.Topology.SimplicialComplex.GeometricFaceBoundary

set_option autoImplicit false
noncomputable section
open Set Finset
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}


def geometricFaceHomeomorphism (hs : s ∈ K.faces) :
    stdSimplex ℝ s ≃ₜ convexHull ℝ (s : Set E) :=
  (DifferentialGeometry.Simplex.vertexHomeomorphism (K.indep hs)).trans
    (Homeomorph.setCongr (by congr 1; ext a; simp))


@[simp]
theorem geometricFaceHomeomorphism_apply (hs : s ∈ K.faces) (x : stdSimplex ℝ s) :
    (geometricFaceHomeomorphism K hs x : E) =
      DifferentialGeometry.Simplex.vertexMap (fun i : s => (i : E)) x := rfl


def geometricFaceBoundaryMap (hs : s ∈ K.faces) :
    C(DifferentialGeometry.Simplex.boundary s,
      ↥(convexHull ℝ (s : Set E) ∩ (geometricFaceCostar K s).space)) where
  toFun x := ⟨(geometricFaceHomeomorphism K hs x.val).val,
    (geometricFaceHomeomorphism K hs x.val).prop,
    (vertexMap_mem_geometricFaceCostar_iff K hs x.val).mpr x.prop⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((geometricFaceHomeomorphism K hs).continuous.comp continuous_subtype_val)).subtype_mk _


theorem geometricFaceBoundaryMap_bijective (hs : s ∈ K.faces) :
    Function.Bijective (geometricFaceBoundaryMap K hs) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (geometricFaceHomeomorphism K hs).injective
    have he : (geometricFaceBoundaryMap K hs x : E) = (geometricFaceBoundaryMap K hs y : E) :=
      congrArg Subtype.val h
    exact Subtype.ext he
  · intro y
    let x := (geometricFaceHomeomorphism K hs).symm ⟨y.val, y.prop.1⟩
    have he : DifferentialGeometry.Simplex.vertexMap (fun i : s => (i : E)) x = y.val :=
      congrArg Subtype.val ((geometricFaceHomeomorphism K hs).apply_symm_apply ⟨y.val, y.prop.1⟩)
    have hx : x ∈ DifferentialGeometry.Simplex.boundary s :=
      (vertexMap_mem_geometricFaceCostar_iff K hs x).mp (he.symm ▸ y.prop.2)
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩


def geometricFaceBoundaryHomeomorphism (hs : s ∈ K.faces) :
    DifferentialGeometry.Simplex.boundary s ≃ₜ
      ↥(convexHull ℝ (s : Set E) ∩ (geometricFaceCostar K s).space) := by
  let : CompactSpace (DifferentialGeometry.Simplex.boundary s) :=
    isCompact_iff_compactSpace.mp DifferentialGeometry.Simplex.isClosed_boundary.isCompact
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (geometricFaceBoundaryMap K hs) (geometricFaceBoundaryMap_bijective K hs))
    (geometricFaceBoundaryMap K hs).continuous


@[simp]
theorem geometricFaceBoundaryHomeomorphism_val (hs : s ∈ K.faces)
    (x : DifferentialGeometry.Simplex.boundary s) :
    (geometricFaceBoundaryHomeomorphism K hs x : E) =
      (geometricFaceHomeomorphism K hs x.val : E) := rfl

end DifferentialGeometry.Topology.SimplicialComplex
