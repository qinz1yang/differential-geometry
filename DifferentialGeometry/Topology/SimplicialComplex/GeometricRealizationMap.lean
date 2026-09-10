import DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet
import DifferentialGeometry.Topology.Simplex.VertexMap
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

set_option autoImplicit false
noncomputable section
open CategoryTheory Simplicial Opposite
namespace Poincare.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E)


theorem geometricVertexSum_mem_space {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n)
    (x : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    Poincare.Simplex.vertexMap s.val.obj x ∈ K.space := by
  have hs : Finset.univ.image s.val.obj ∈ K.faces := s.prop
  have hh : Poincare.Simplex.vertexMap s.val.obj x ∈
      convexHull ℝ (↑(Finset.univ.image s.val.obj) : Set E) := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      Poincare.Simplex.vertexMap_mem_convexHull s.val.obj x
  exact Geometry.SimplicialComplex.convexHull_subset_space (K := K) hs hh


def geometricSimplexMap {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n) :
    C(stdSimplex ℝ (Fin (n.unop.len + 1)), K.space) where
  toFun x := ⟨Poincare.Simplex.vertexMap s.val.obj x, geometricVertexSum_mem_space K s x⟩
  continuous_toFun := (Poincare.Simplex.vertexMap s.val.obj).continuous.subtype_mk _


@[simp]
theorem geometricSimplexMap_apply {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n)
    (x : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    (geometricSimplexMap K s x : E) = ∑ i, x.val i • s.val.obj i := rfl


theorem geometricSimplexMap_naturality {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n)
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj m)
    (x : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    geometricSimplexMap K ((orderedSimplicialSet K.toPreAbstractSimplicialComplex).map f s) x =
      geometricSimplexMap K s (stdSimplex.map f.unop.toOrderHom x) := by
  apply Subtype.ext
  exact (Poincare.Simplex.vertexMap_map s.val.obj f.unop.toOrderHom x).symm

def geometricSingularMap : orderedSimplicialSet K.toPreAbstractSimplicialComplex ⟶
    TopCat.toSSet.obj (TopCat.of K.space) where
  app n := ↾fun s => (TopCat.toSSetObjEquiv (TopCat.of K.space) n).symm (geometricSimplexMap K s)
  naturality {m n} f := by
    ext s
    apply (TopCat.toSSetObjEquiv (TopCat.of K.space) n).injective
    apply ContinuousMap.ext
    intro x
    exact geometricSimplexMap_naturality K f s x

def geometricRealizationMap :
    SSet.toTop.obj (orderedSimplicialSet K.toPreAbstractSimplicialComplex) ⟶ TopCat.of K.space :=
  (sSetTopAdj.homEquiv _ _).symm (geometricSingularMap K)

theorem geometricRealizationMap_unit :
    sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex) ≫
      TopCat.toSSet.map (geometricRealizationMap K) = geometricSingularMap K :=
  (sSetTopAdj.homEquiv _ _).apply_symm_apply (geometricSingularMap K)

theorem geometricRealizationMap_unit_apply {n : SimplexCategoryᵒᵖ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).obj n)
    (t : stdSimplex ℝ (Fin (n.unop.len + 1))) :
    geometricRealizationMap K
      ((TopCat.toSSetObjEquiv _ n)
        ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app n s) t) =
      geometricSimplexMap K s t := by
  have hh := congrArg (fun f : orderedSimplicialSet K.toPreAbstractSimplicialComplex ⟶
      TopCat.toSSet.obj (TopCat.of K.space) => f.app n s) (geometricRealizationMap_unit K)
  exact congrArg (fun f => TopCat.toSSetObjEquiv (TopCat.of K.space) n f t) hh

theorem geometricSimplexMap_injective {n : ℕ}
    (s : (orderedSimplicialSet K.toPreAbstractSimplicialComplex).nonDegenerate n) :
    Function.Injective (geometricSimplexMap K s.val) := by
  have hs := ((orderedSimplicialSet_mem_nonDegenerate_iff K.toPreAbstractSimplicialComplex s.val).mp
    s.prop).injective
  let e : Fin (n + 1) ↪ (Finset.univ.image s.val.val.obj) :=
    ⟨fun i => ⟨s.val.val.obj i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩,
      fun _ _ h => hs (congrArg Subtype.val h)⟩
  have hv : AffineIndependent ℝ s.val.val.obj := (K.indep s.val.prop).comp_embedding e
  intro x y h
  exact Poincare.Simplex.vertexMap_injective hv (congrArg Subtype.val h)

theorem geometricRealizationMap_surjective : Function.Surjective (geometricRealizationMap K) := by
  intro x
  obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp x.prop
  let n := s.card - 1
  have hn : s.card = n + 1 :=
    (Nat.sub_add_cancel (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs))).symm
  let a := orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn
  have hrange : Set.range a.val.val.obj = (s : Set E) := by
    rw [← vertices_orderedSimplexOfFace K.toPreAbstractSimplicialComplex s hs hn]
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rfl
  have hx' : x.val ∈ Set.range (Poincare.Simplex.vertexMap a.val.val.obj) := by
    rw [Poincare.Simplex.range_vertexMap, hrange]
    exact hx
  obtain ⟨t, ht⟩ := hx'
  refine ⟨(TopCat.toSSetObjEquiv _ (op ⦋n⦌))
    ((sSetTopAdj.unit.app (orderedSimplicialSet K.toPreAbstractSimplicialComplex)).app _ a.val) t, ?_⟩
  exact (geometricRealizationMap_unit_apply K a.val t).trans (Subtype.ext ht)

end Poincare.Topology.SimplicialComplex
