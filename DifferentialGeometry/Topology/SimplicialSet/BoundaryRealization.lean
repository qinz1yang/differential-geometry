import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import DifferentialGeometry.Topology.Homology.SmallChains.Subspace

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace DifferentialGeometry.SSet


def simplexBoundarySet (n : ℕ) : Set (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
  {p | ∃ i : Fin (n + 1), (p.down : Convexity.StdSimplex ℝ (Fin (n + 1))).weights i = 0}


theorem isClosed_simplexBoundarySet (n : ℕ) : IsClosed (simplexBoundarySet.{u} n) := by
  change IsClosed (Set.ofPred (fun p : ULift.{u} (Convexity.StdSimplex ℝ (Fin (n + 1))) ↦
    ∃ i : Fin (n + 1), p.down.weights i = 0))
  rw [Set.ofPred_exists]
  exact isClosed_iUnion_of_finite (fun i ↦ isClosed_eq
    ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_uliftDown)
      continuous_const)


def boundaryRealizationMap (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
      SimplexCategory.toTop.obj ⦋n⦌ :=
  _root_.SSet.toTop.map (_root_.SSet.boundary n).ι ≫ _root_.SSet.toTopSimplex.hom.app ⦋n⦌


theorem stdSimplexToTop_app_down {n m : ℕ}
    (σ : (Δ[n] : _root_.SSet.{u}) _⦋m⦌) :
    ((_root_.SSet.stdSimplexToTop.app ⦋n⦌).app (op ⦋m⦌) σ).down =
      SimplexCategory.toTop.map (_root_.SSet.stdSimplex.objEquiv σ) := by
  change ((sSetTopAdj.unit.app (Δ[n] : _root_.SSet.{u})).app (op ⦋m⦌) σ).down ≫
    _root_.SSet.toTopSimplex.hom.app ⦋n⦌ = _
  rw [sSetTopAdj_unit_app_app_down]
  have hσ : _root_.SSet.yonedaEquiv.symm σ =
      _root_.SSet.stdSimplex.map (_root_.SSet.stdSimplex.objEquiv σ) := by
    apply _root_.SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply, _root_.SSet.yonedaEquiv_map]
    exact (Equiv.symm_apply_apply _ σ).symm
  have hn := _root_.SSet.toTopSimplex.hom.naturality (_root_.SSet.stdSimplex.objEquiv σ)
  change _root_.SSet.toTop.map (_root_.SSet.stdSimplex.map (_root_.SSet.stdSimplex.objEquiv σ)) ≫
    _root_.SSet.toTopSimplex.hom.app ⦋n⦌ =
      _root_.SSet.toTopSimplex.hom.app ⦋m⦌ ≫
        SimplexCategory.toTop.map (_root_.SSet.stdSimplex.objEquiv σ) at hn
  rw [hσ, Category.assoc, hn]
  rw [← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ SimplexCategory.toTop.map (_root_.SSet.stdSimplex.objEquiv σ))
    (_root_.SSet.toTopSimplex.app ⦋m⦌).inv_hom_id).trans (Category.id_comp _)

private theorem coordinateMap_zero_of_not_mem_range {n m : ℕ}
    (σ : (Δ[n] : _root_.SSet.{u}) _⦋m⦌) (i : Fin (n + 1))
    (hi : i ∉ Set.range σ) (p : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    (Convexity.StdSimplex.map (_root_.SSet.stdSimplex.objEquiv σ) p).weights i = 0 := by
  exact Finsupp.mapDomain_of_notMem_range p.weights i hi

private theorem boundaryCanonicalSimplex_mem (n : ℕ) (m : SimplexCategoryᵒᵖ)
    (σ : (_root_.SSet.boundary n : _root_.SSet.{u}).obj m) :
    (_root_.SSet.stdSimplexToTop.app ⦋n⦌).app m σ.val ∈
      (DifferentialGeometry.Homology.smallSingularSimplices (SimplexCategory.toTop.obj ⦋n⦌)
        (fun _ : Unit ↦ simplexBoundarySet n)).obj m := by
  refine ⟨(), ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨i, hi⟩ := (_root_.SSet.mem_boundary_iff_notMem_range σ.val).mp σ.property
  refine ⟨i, ?_⟩
  change (((((_root_.SSet.stdSimplexToTop.app ⦋n⦌).app m σ.val).down :
    SimplexCategory.toTop.obj m.unop ⟶ SimplexCategory.toTop.obj ⦋n⦌).hom
      (ULift.up z)).down : Convexity.StdSimplex ℝ (Fin (n + 1))).weights i = 0
  rw [stdSimplexToTop_app_down]
  exact coordinateMap_zero_of_not_mem_range σ.val i hi z

private def boundaryToSmallSingular (n : ℕ) :
    (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
      DifferentialGeometry.Homology.smallSingularSimplices (SimplexCategory.toTop.obj ⦋n⦌)
        (fun _ : Unit ↦ simplexBoundarySet n) :=
  _root_.SSet.Subcomplex.lift
    ((_root_.SSet.boundary n).ι ≫ _root_.SSet.stdSimplexToTop.app ⦋n⦌) (by
      intro m ρ hρ
      obtain ⟨σ, rfl⟩ := hρ
      exact boundaryCanonicalSimplex_mem n m σ)


def boundarySingularMap (n : ℕ) :
    (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
      TopCat.toSSet.obj (TopCat.of (simplexBoundarySet n)) :=
  boundaryToSmallSingular n ≫
    (DifferentialGeometry.Homology.singularSubspaceIso (SimplexCategory.toTop.obj ⦋n⦌)
      (simplexBoundarySet n)).inv


@[reassoc]
theorem boundarySingularMap_inclusion (n : ℕ) :
    boundarySingularMap n ≫ TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(simplexBoundarySet n, SimplexCategory.toTop.{u}.obj ⦋n⦌))) =
      (_root_.SSet.boundary n).ι ≫ _root_.SSet.stdSimplexToTop.app ⦋n⦌ := by
  rw [boundarySingularMap, Category.assoc,
    DifferentialGeometry.Homology.singularSubspaceIso_inv_inclusion]
  rfl


def boundaryRealizationLift (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ⟶
      TopCat.of (simplexBoundarySet n) :=
  (sSetTopAdj.homEquiv _ _).symm (boundarySingularMap n)


@[reassoc]
theorem boundaryRealizationLift_inclusion (n : ℕ) :
    boundaryRealizationLift n ≫
        TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(simplexBoundarySet n, SimplexCategory.toTop.{u}.obj ⦋n⦌)) =
      boundaryRealizationMap n := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_right, boundaryRealizationLift,
    Equiv.apply_symm_apply, boundarySingularMap_inclusion,
    boundaryRealizationMap, sSetTopAdj.homEquiv_naturality_left]
  rfl


theorem range_boundaryRealizationMap_subset (n : ℕ) :
    Set.range (boundaryRealizationMap.{u} n) ⊆ simplexBoundarySet n := by
  rintro _ ⟨x, rfl⟩
  have he := ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion.{u} n) x
  rw [← he]
  exact (boundaryRealizationLift n x).property

private theorem exists_coordinateFace_preimage {n : ℕ}
    (p : Convexity.StdSimplex ℝ (Fin (n + 2))) (i : Fin (n + 2)) (hi : p.weights i = 0) :
    ∃ q : Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex.map i.succAbove q = p := by
  apply (Convexity.StdSimplex.mem_range_map_iff i.succAbove p).mpr
  intro j hj
  have hji : j = i := by simpa only [Fin.range_succAbove, Set.mem_compl_iff,
    Set.mem_singleton_iff, not_not] using hj
  simpa only [hji] using hi


@[reassoc]
theorem boundaryRealizationMap_face {n : ℕ} (i : Fin (n + 2)) :
    _root_.SSet.toTop.map (_root_.SSet.boundary.ι.{u} i) ≫ boundaryRealizationMap (n + 1) =
      _root_.SSet.toTopSimplex.hom.app ⦋n⦌ ≫ SimplexCategory.toTop.map (SimplexCategory.δ i) := by
  rw [boundaryRealizationMap, ← Category.assoc, ← Functor.map_comp, _root_.SSet.boundary.ι_ι]
  exact _root_.SSet.toTopSimplex.hom.naturality (SimplexCategory.δ i)


theorem simplexBoundarySet_subset_range (n : ℕ) :
    simplexBoundarySet n ⊆ Set.range (boundaryRealizationMap.{u} n) := by
  intro p hp
  obtain ⟨i, hi⟩ := hp
  cases n with
  | zero =>
    have hs := (p.down : Convexity.StdSimplex ℝ (Fin 1)).total_of_fintype
    have he : (p.down : Convexity.StdSimplex ℝ (Fin 1)).weights i = 1 := by
      change (∑ j : Fin 1, (p.down : Convexity.StdSimplex ℝ (Fin 1)).weights j) = 1 at hs
      simpa only [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) i] using hs
    exact False.elim (zero_ne_one (hi.symm.trans he))
  | succ n =>
    obtain ⟨q, hq⟩ := exists_coordinateFace_preimage
      (p.down : Convexity.StdSimplex ℝ (Fin (n + 2))) i hi
    let x := (_root_.SSet.toTopSimplex.inv.app ⦋n⦌).hom (ULift.up q)
    refine ⟨(_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom x, ?_⟩
    have hf : _root_.SSet.toTopSimplex.inv.app ⦋n⦌ ≫
        _root_.SSet.toTop.map (_root_.SSet.boundary.ι i) ≫ boundaryRealizationMap (n + 1) =
        SimplexCategory.toTop.map (SimplexCategory.δ i) := by
      rw [boundaryRealizationMap_face]
      exact _root_.SSet.toTopSimplex.inv_hom_id_app_assoc _ _
    have he := ConcreteCategory.congr_hom hf (ULift.up q)
    change boundaryRealizationMap (n + 1)
      ((_root_.SSet.toTop.map (_root_.SSet.boundary.ι i)).hom x) = _ at he
    refine he.trans ?_
    apply ULift.ext
    exact hq


theorem range_boundaryRealizationMap (n : ℕ) :
    Set.range (boundaryRealizationMap.{u} n) = simplexBoundarySet n :=
  Set.Subset.antisymm (range_boundaryRealizationMap_subset n) (simplexBoundarySet_subset_range n)


theorem surjective_boundaryRealizationLift (n : ℕ) :
    Function.Surjective (boundaryRealizationLift.{u} n) := by
  intro p
  obtain ⟨x, hx⟩ := simplexBoundarySet_subset_range n p.property
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact (ConcreteCategory.congr_hom (boundaryRealizationLift_inclusion n) x).trans hx

theorem range_toTopHomeo_boundary (n : ℕ) :
    Set.range (fun x : _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet.{u}) ↦
      SimplexCategory.toTopHomeo ⦋n⦌ ((_root_.SSet.toTop.map (_root_.SSet.boundary n).ι).hom x)) =
        Set.ofPred (fun p : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦
          ∃ i : Fin (n + 1), p.weights i = 0) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact range_boundaryRealizationMap_subset n ⟨x, rfl⟩
  · intro p hp
    obtain ⟨x, hx⟩ := simplexBoundarySet_subset_range n
      (show (ULift.up p : SimplexCategory.toTop.{u}.obj ⦋n⦌) ∈ simplexBoundarySet n from hp)
    refine ⟨x, ?_⟩
    exact congrArg ULift.down hx

end DifferentialGeometry.SSet
