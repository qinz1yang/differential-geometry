import DifferentialGeometry.Topology.SimplicialComplex.GeometricBoundaryPair

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry.Homology
open scoped Manifold
namespace DifferentialGeometry.Topology.SimplicialComplex
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} (hLK : L ≤ K)


def geometricSubcomplexHomeomorphism :
    L.space ≃ₜ ((Subtype.val : K.space → E) ⁻¹' L.space) where
  toFun x := ⟨⟨x.val, geometricSpace_mono hLK x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] (e : K.space ≃ₜ M)
  (hboundary : e '' ((Subtype.val : K.space → E) ⁻¹' L.space) = (𝓡∂ n).boundary M)


def geometricSubcomplexBoundaryHomeomorphism : L.space ≃ₜ (𝓡∂ n).boundary M :=
  (geometricSubcomplexHomeomorphism hLK).trans
    (e.subtype (geometricSubcomplex_mem_boundary_iff e hboundary))


@[simp]
theorem geometricSubcomplexBoundaryHomeomorphism_apply (x : L.space) :
    (geometricSubcomplexBoundaryHomeomorphism hLK e hboundary x : M) =
      e ⟨x.val, geometricSpace_mono hLK x.property⟩ := rfl

include hLK e hboundary


theorem finiteHomologyType_boundary_of_geometric_pair [Finite L.faces] (k : Type) [Field k] :
    finiteHomologyType k (TopCat.of ((𝓡∂ n).boundary M)) :=
  (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of L.space) (Y := TopCat.of ((𝓡∂ n).boundary M))
    (geometricSubcomplexBoundaryHomeomorphism hLK e hboundary)).mp
      (finiteHomologyType_geometricSpace L k)


theorem eulerChar_boundary_eq_faceEulerChar [Finite L.faces] (k : Type) [Field k] :
    eulerChar k (TopCat.of ((𝓡∂ n).boundary M)) = faceEulerChar L.toPreAbstractSimplicialComplex :=
  (eulerChar_eq_of_homeomorph k
    (X := TopCat.of L.space) (Y := TopCat.of ((𝓡∂ n).boundary M))
    (geometricSubcomplexBoundaryHomeomorphism hLK e hboundary)).symm.trans
      (eulerChar_geometricSpace_eq_faceEulerChar L k)

omit hLK hboundary [ChartedSpace (EuclideanHalfSpace n) M] in
theorem finiteHomologyType_of_geometric_homeomorphism [Finite K.faces] (k : Type) [Field k] :
    finiteHomologyType k (TopCat.of M) :=
  (finiteHomologyType_iff_of_homeomorph k (X := TopCat.of K.space) (Y := TopCat.of M) e).mp
    (finiteHomologyType_geometricSpace K k)

omit hLK hboundary [ChartedSpace (EuclideanHalfSpace n) M] in
theorem eulerChar_eq_faceEulerChar_of_geometric_homeomorphism [Finite K.faces]
    (k : Type) [Field k] :
    eulerChar k (TopCat.of M) = faceEulerChar K.toPreAbstractSimplicialComplex :=
  (eulerChar_eq_of_homeomorph k (X := TopCat.of K.space) (Y := TopCat.of M) e).symm.trans
    (eulerChar_geometricSpace_eq_faceEulerChar K k)


theorem finiteHomologyType_relativeBoundary_of_geometric_pair
    [Finite K.faces] [Finite L.faces] (k : Type) [Field k] :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) ((𝓡∂ n).boundary M) (ModuleCat.of k k)) :=
  finiteHomologyType_relativeChainComplex (TopCat.of M) ((𝓡∂ n).boundary M) k
    (finiteHomologyType_boundary_of_geometric_pair hLK e hboundary k)
    (finiteHomologyType_of_geometric_homeomorphism e k)


theorem relativeEulerChar_boundary_eq_faceDifference
    [Finite K.faces] [Finite L.faces] (k : Type) [Field k] :
    relativeEulerChar (TopCat.of M) ((𝓡∂ n).boundary M) k =
      faceEulerChar K.toPreAbstractSimplicialComplex - faceEulerChar L.toPreAbstractSimplicialComplex := by
  rw [relativeEulerChar_eq_sub (TopCat.of M) ((𝓡∂ n).boundary M) k
    (finiteHomologyType_boundary_of_geometric_pair hLK e hboundary k)
    (finiteHomologyType_of_geometric_homeomorphism e k),
    eulerChar_eq_faceEulerChar_of_geometric_homeomorphism e k,
    eulerChar_boundary_eq_faceEulerChar hLK e hboundary k]

end DifferentialGeometry.Topology.SimplicialComplex
