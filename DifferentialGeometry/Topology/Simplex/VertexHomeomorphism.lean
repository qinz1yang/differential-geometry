import DifferentialGeometry.Topology.Simplex.VertexMap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Simplex
variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexMapToHull (v : ι → E) : C(stdSimplex ℝ ι, convexHull ℝ (Set.range v)) where
  toFun x := ⟨vertexMap v x, vertexMap_mem_convexHull v x⟩
  continuous_toFun := (vertexMap v).continuous.subtype_mk _


theorem vertexMapToHull_surjective (v : ι → E) : Function.Surjective (vertexMapToHull v) := by
  intro x
  have hx : x.val ∈ Set.range (vertexMap v) := (range_vertexMap v).symm ▸ x.prop
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

def vertexHomeomorphism {v : ι → E} (hv : AffineIndependent ℝ v) :
    stdSimplex ℝ ι ≃ₜ convexHull ℝ (Set.range v) :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (vertexMapToHull v)
    ⟨fun _ _ h => vertexMap_injective hv (congrArg Subtype.val h), vertexMapToHull_surjective v⟩)
    (vertexMapToHull v).continuous


@[simp]
theorem vertexHomeomorphism_apply {v : ι → E} (hv : AffineIndependent ℝ v)
    (x : stdSimplex ℝ ι) : (vertexHomeomorphism hv x : E) = ∑ i, x.val i • v i := rfl

end DifferentialGeometry.Simplex
