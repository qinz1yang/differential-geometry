import DifferentialGeometry.Topology.SimplicialComplex.VertexStarContractible
import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic
import DifferentialGeometry.Topology.Homology.Local.Manifold
import DifferentialGeometry.Topology.Homotopy.ConvexProduct

set_option autoImplicit false
noncomputable section
open Set CategoryTheory ContinuousMap Poincare.Homology
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (p : E)


def vertexStarNeighborhoodHomeomorphism :
    ((Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p) ≃ₜ vertexOpenStar K p where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (hp : {p} ∈ K.faces)
include hp


def puncturedOpenStarHomeomorphism :
    ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set (vertexOpenStar K p)) ≃ₜ
      puncturedVertexOpenStar K p where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem neighborhood_puncture_iff
    (y : (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p) :
    y ∈ ({(⟨⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩,
        vertex_mem_openStar K p hp⟩ :
          (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p)}ᶜ : Set _) ↔
      vertexStarNeighborhoodHomeomorphism K p y ∈
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) :=
  not_congr (vertexStarNeighborhoodHomeomorphism K p).injective.eq_iff.symm


def puncturedVertexStarHomotopyEquiv :
    puncturedVertexOpenStar K p ≃ₕ (geometricLink K {p}).space :=
  (puncturedVertexStarHomeomorphism K p hp).toHomotopyEquiv.trans
    (Poincare.HomotopyEquiv.productConvex _ (convex_Ioo (0 : ℝ) 1)
      ⟨1 / 2, by constructor <;> norm_num⟩)


@[simp]
theorem puncturedVertexStarHomotopyEquiv_symm_apply (y : (geometricLink K {p}).space) :
    ((puncturedVertexStarHomotopyEquiv K p hp).symm y).val =
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • y.val := by
  change (1 / 2 : ℝ) • p + (1 - 1 / 2 : ℝ) • y.val = _
  norm_num


theorem finiteHomologyType_puncturedVertexStar (k : Type u) [Field k] :
    finiteHomologyType k (TopCat.of (puncturedVertexOpenStar K p)) :=
  (finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of (puncturedVertexOpenStar K p))
    (Y := TopCat.of (geometricLink K {p}).space)
    (puncturedVertexStarHomotopyEquiv K p hp)).mpr
      (finiteHomologyType_geometricSpace (geometricLink K {p}) k)


theorem eulerChar_puncturedVertexStar (k : Type u) [Field k] :
    eulerChar k (TopCat.of (puncturedVertexOpenStar K p)) =
      eulerChar k (TopCat.of (geometricLink K {p}).space) :=
  eulerChar_eq_of_homotopyEquiv k
    (X := TopCat.of (puncturedVertexOpenStar K p))
    (Y := TopCat.of (geometricLink K {p}).space)
    (puncturedVertexStarHomotopyEquiv K p hp)


theorem finiteHomologyType_localGeometricVertex (k : Type u) [Field k] :
    Poincare.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of K.space)
        ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space)
        (ModuleCat.of k k)) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hx : x ∈ U := vertex_mem_openStar K p hp
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
    (Y := TopCat.of (puncturedVertexOpenStar K p))
    (puncturedOpenStarHomeomorphism K p hp)).mpr
      (finiteHomologyType_puncturedVertexStar K p hp k)
  have hs := finiteHomologyType_relativeChainComplex (TopCat.of (vertexOpenStar K p))
    ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k hf
    (finiteHomologyType_vertexOpenStar K p hp k)
  let e := relativeChainIso (X := TopCat.of U) (Y := TopCat.of (vertexOpenStar K p))
    (ModuleCat.of k k) (vertexStarNeighborhoodHomeomorphism K p)
    (neighborhood_puncture_iff K p hp)
  have hn := (Poincare.HomologicalComplex.finiteHomologyType_iff_of_quasiIso e.hom).mpr hs
  exact (finiteHomologyType_puncturedNeighborhood_iff (TopCat.of K.space) U x hx k
    (isOpen_vertexOpenStar K p)).mp hn


theorem relativeEulerChar_vertex_eq_one_sub_link (k : Type u) [Field k] :
    relativeEulerChar (TopCat.of K.space)
      ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space) k =
        1 - eulerChar k (TopCat.of (geometricLink K {p}).space) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' vertexOpenStar K p
  let x : K.space := ⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩
  have hx : x ∈ U := vertex_mem_openStar K p hp
  have he : ∀ y : U,
      y ∈ ({(⟨x, hx⟩ : U)}ᶜ : Set U) ↔
        vertexStarNeighborhoodHomeomorphism K p y ∈
          ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set (vertexOpenStar K p)) :=
    neighborhood_puncture_iff K p hp
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
    (Y := TopCat.of (puncturedVertexOpenStar K p))
    (puncturedOpenStarHomeomorphism K p hp)).mpr
      (finiteHomologyType_puncturedVertexStar K p hp k)
  calc
    _ = relativeEulerChar (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) k :=
      (relativeEulerChar_puncturedNeighborhood (TopCat.of K.space) U x hx k
        (isOpen_vertexOpenStar K p)).symm
    _ = relativeEulerChar (TopCat.of (vertexOpenStar K p))
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k :=
      relativeEulerChar_eq_of_homeomorph (X := TopCat.of U)
        (Y := TopCat.of (vertexOpenStar K p)) k (vertexStarNeighborhoodHomeomorphism K p) he
    _ = 1 - eulerChar k (TopCat.of (geometricLink K {p}).space) := by
      rw [relativeEulerChar_eq_sub (TopCat.of (vertexOpenStar K p))
        ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _) k hf (finiteHomologyType_vertexOpenStar K p hp k),
        eulerChar_vertexOpenStar K p hp k,
        eulerChar_eq_of_homeomorph k
          (X := TopCat.of ({(⟨p, vertex_mem_openStar K p hp⟩ : vertexOpenStar K p)}ᶜ : Set _))
          (Y := TopCat.of (puncturedVertexOpenStar K p)) (puncturedOpenStarHomeomorphism K p hp),
        eulerChar_puncturedVertexStar K p hp k]


theorem faceEulerChar_vertexLink_eq_one_sub_local (k : Type u) [Field k] :
    faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) =
      1 - relativeEulerChar (TopCat.of K.space)
        ({(⟨p, Geometry.SimplicialComplex.vertices_subset_space hp⟩ : K.space)}ᶜ : Set K.space) k := by
  have h := relativeEulerChar_vertex_eq_one_sub_link K p hp k
  rw [eulerChar_geometricSpace_eq_faceEulerChar] at h
  change _ = 1 - faceEulerChar (link K.toPreAbstractSimplicialComplex {p}) at h
  omega

end Poincare.Topology.SimplicialComplex
