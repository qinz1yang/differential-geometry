import DifferentialGeometry.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.Homology.SimplexBoundary
import DifferentialGeometry.Topology.Simplex.VertexMap
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module Set
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

abbrev Square : Type := Fin 2 → unitInterval

theorem square_nullhomotopic : (ContinuousMap.id Square).Nullhomotopic := by
  refine ⟨fun _ => (0 : unitInterval), ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => fun i => ⟨(1 - (p.1 : ℝ)) * (p.2 i : ℝ), ?_, ?_⟩, ?_⟩
    ?_ ?_⟩⟩
  · exact mul_nonneg (by linarith [(p.1).property.1, (p.1).property.2]) (p.2 i).property.1
  · nlinarith [(p.1).property.1, (p.1).property.2, (p.2 i).property.1, (p.2 i).property.2]
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have h1 : Continuous fun p : unitInterval × Square => (1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : unitInterval × Square => ((p.2 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact h1.mul h2
  · intro v
    funext i
    apply Subtype.ext
    simp
  · intro v
    funext i
    apply Subtype.ext
    simp

theorem square_contractible : ContractibleSpace Square :=
  (contractible_iff_id_nullhomotopic Square).mpr square_nullhomotopic

theorem subsingleton_homology_two_square :
    Subsingleton (integralSingularHomology 2 Square) :=
  letI := square_contractible
  integralSingularHomology_subsingleton_of_contractible 2 (by omega) Square

def halfPoint : unitInterval := ⟨1 / 2, by norm_num⟩

def squarePoint (a b : unitInterval) : Square := ![a, b]

def squareOrigin : Square := squarePoint 0 0
def squareEast : Square := squarePoint 1 0
def squareNorthEast : Square := squarePoint 1 1
def squareNorth : Square := squarePoint 0 1
def squareMidEast : Square := squarePoint halfPoint 0
def squareMidNorth : Square := squarePoint halfPoint 1

theorem squarePoint_zero (a b : unitInterval) : squarePoint a b 0 = a := rfl
theorem squarePoint_one (a b : unitInterval) : squarePoint a b 1 = b := rfl

def squareAffineMap (n : ℕ) (v : Fin (n + 1) → Square) :
    C(stdSimplex ℝ (Fin (n + 1)), Square) where
  toFun t := fun i => ⟨Simplex.vertexMap (fun j => (v j i : ℝ)) t, by
    refine convexHull_min ?_ (convex_Icc 0 1)
      (Simplex.vertexMap_mem_convexHull (fun j => (v j i : ℝ)) t)
    rintro x ⟨j, rfl⟩
    exact (v j i).property⟩
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (Simplex.vertexMap (fun j => (v j i : ℝ))).continuous

theorem squareAffineMap_apply_coe (n : ℕ) (v : Fin (n + 1) → Square)
    (t : stdSimplex ℝ (Fin (n + 1))) (i : Fin 2) :
    ((squareAffineMap n v t i : unitInterval) : ℝ) = ∑ j, (t.val j) * (v j i : ℝ) := by
  simp [squareAffineMap, Simplex.vertexMap_apply, smul_eq_mul]

def squareAffineSimplex (n : ℕ) (v : Fin (n + 1) → Square) :
    integralSingularSimplex n Square :=
  (integralSingularSimplexEquiv n Square).symm (squareAffineMap n v)

@[simp] theorem squareAffineSimplex_val (n : ℕ) (v : Fin (n + 1) → Square) :
    (TopCat.of Square).toSSetObjEquiv (Opposite.op ⦋n⦌) (squareAffineSimplex n v) =
      squareAffineMap n v :=
  Equiv.apply_symm_apply _ _

theorem squareAffineSimplex_face_eval (n : ℕ) (v : Fin (n + 2) → Square)
    (i : Fin (n + 2)) (t : stdSimplex ℝ (Fin (n + 1))) (i' : Fin 2) :
    (((integralSingularSimplexEquiv n Square)
        ((TopCat.toSSet.obj (TopCat.of Square)).δ i (squareAffineSimplex (n + 1) v))) t i'
        : ℝ) =
      (((integralSingularSimplexEquiv n Square)
        (squareAffineSimplex n (fun j => v (i.succAbove j)))) t i' : ℝ) := by
  simp only [integralSingularSimplexEquiv]
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [squareAffineSimplex_val, squareAffineSimplex_val]
  exact Simplex.vertexMap_map (fun j => (v j i' : ℝ)) i.succAbove t

theorem squareAffineSimplex_face (n : ℕ) (v : Fin (n + 2) → Square) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of Square)).δ i (squareAffineSimplex (n + 1) v) =
      squareAffineSimplex n (fun j => v (i.succAbove j)) := by
  apply (integralSingularSimplexEquiv n Square).injective
  apply ContinuousMap.ext
  intro t
  apply funext
  intro i'
  exact Subtype.ext (squareAffineSimplex_face_eval n v i t i')

theorem squareTriangleFace_zero (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((0 : Fin 3).succAbove j)) = ![Q, R] := by
  funext j
  fin_cases j <;> rfl

theorem squareTriangleFace_one (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((1 : Fin 3).succAbove j)) = ![P, R] := by
  funext j
  fin_cases j <;> rfl

theorem squareTriangleFace_two (P Q R : Square) :
    (fun j : Fin 2 => ![P, Q, R] ((2 : Fin 3).succAbove j)) = ![P, Q] := by
  funext j
  fin_cases j <;> rfl

def squareTriangleChain (P Q R : Square) : (integralSingularChains Square).X 2 :=
  integralSimplexChain 2 (squareAffineSimplex 2 ![P, Q, R])

def squareSegmentChain (P Q : Square) : (integralSingularChains Square).X 1 :=
  integralSimplexChain 1 (squareAffineSimplex 1 ![P, Q])

theorem squareTriangleChain_boundary (P Q R : Square) :
    (integralSingularChains Square).d 2 1 (squareTriangleChain P Q R) =
      squareSegmentChain Q R - squareSegmentChain P R + squareSegmentChain P Q := by
  rw [squareTriangleChain, integralSimplexChain_boundary]
  rw [Fin.sum_univ_three]
  rw [squareAffineSimplex_face, squareAffineSimplex_face, squareAffineSimplex_face]
  rw [squareTriangleFace_zero, squareTriangleFace_one, squareTriangleFace_two]
  norm_num
  abel

def squareFundamentalChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareEast squareNorthEast -
    squareTriangleChain squareOrigin squareNorth squareNorthEast

def squareLeftHalfChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareMidEast squareMidNorth -
    squareTriangleChain squareOrigin squareNorth squareMidNorth

def squareRightHalfChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareMidEast squareEast squareNorthEast -
    squareTriangleChain squareMidEast squareMidNorth squareNorthEast

def squareCornerChain : (integralSingularChains Square).X 2 :=
  squareTriangleChain squareOrigin squareMidEast squareEast -
    squareTriangleChain squareNorth squareMidNorth squareNorthEast

theorem square_fold_identity :
    (integralSingularChains Square).d 2 1
      (squareFundamentalChain - squareLeftHalfChain - squareRightHalfChain +
        squareCornerChain) = 0 := by
  simp only [map_sub, map_add]
  simp only [squareFundamentalChain, squareLeftHalfChain, squareRightHalfChain, squareCornerChain,
    map_sub]
  rw [squareTriangleChain_boundary, squareTriangleChain_boundary, squareTriangleChain_boundary,
    squareTriangleChain_boundary, squareTriangleChain_boundary, squareTriangleChain_boundary,
    squareTriangleChain_boundary, squareTriangleChain_boundary]
  abel

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]
variable {Z : Type u} [TopologicalSpace Z]

def singularSimplexImage (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    integralSingularSimplex n Y :=
  ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm
    (f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ))

@[simp] theorem singularSimplexImage_val (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    (TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌) (singularSimplexImage n f σ) =
      f.comp ((TopCat.of X).toSSetObjEquiv (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

theorem singularSimplexImage_face (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) :
    singularSimplexImage n f ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (TopCat.toSSet.obj (TopCat.of Y)).δ i (singularSimplexImage (n + 1) f σ) := by
  apply ((TopCat.of Y).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImage_val]
  ext t
  simp only [ContinuousMap.comp_apply]
  rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply, singularSimplexImage_val]
  rfl

theorem singularSimplexImage_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) (σ : integralSingularSimplex n X) :
    singularSimplexImage n (g.comp f) σ = singularSimplexImage n g (singularSimplexImage n f σ) := by
  apply ((TopCat.of Z).toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  rw [singularSimplexImage_val, singularSimplexImage_val, singularSimplexImage_val, ContinuousMap.comp_assoc]

def singularChainImage (n : ℕ) (f : C(X, Y)) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains Y).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains Y).X n) ℕ
    (fun σ => integralSimplexChain n (singularSimplexImage n f σ))

theorem singularChainImage_simplex (n : ℕ) (f : C(X, Y)) (σ : integralSingularSimplex n X) :
    singularChainImage n f (integralSimplexChain n σ) =
      integralSimplexChain n (singularSimplexImage n f σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ

theorem singularChainImage_d (n : ℕ) (f : C(X, Y)) :
    (singularChainImage n f).comp (((integralSingularChains X).d (n + 1) n).hom) =
      (((integralSingularChains Y).d (n + 1) n).hom).comp (singularChainImage (n + 1) f) := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
  rw [integralSimplexChain_boundary, map_sum]
  conv_rhs => rw [singularChainImage_simplex, integralSimplexChain_boundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, singularChainImage_simplex, singularSimplexImage_face]

theorem singularChainImage_comp (n : ℕ) (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainImage n (g.comp f) = (singularChainImage n g).comp (singularChainImage n f) := by
  apply (integralSingularChainBasis n X).ext
  intro σ
  simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, singularChainImage_simplex]
  rw [singularSimplexImage_comp]

end DifferentialGeometry.Topology
