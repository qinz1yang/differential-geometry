import DifferentialGeometry.Topology.Homology.SimplexBoundary
import DifferentialGeometry.Topology.Homology.SimplexDegreeChainLevel

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology Simplicial

namespace DifferentialGeometry.Topology.SimplexPrism

universe u

def prismAffine (m : ℕ) {ι : Type*} [Fintype ι] (v : ι → Fin 2 × Fin (m + 1)) :
    C(stdSimplex ℝ ι, unitInterval × stdSimplex ℝ (Fin (m + 1))) where
  toFun q :=
    (⟨(stdSimplex.map (fun j => (v j).1) q).val 1,
        (stdSimplex.map (fun j => (v j).1) q).property.1 1,
        stdSimplex.le_one _ _⟩,
      stdSimplex.map (fun j => (v j).2) q)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact (continuous_apply 1).comp
        (continuous_subtype_val.comp (stdSimplex.continuous_map (fun j => (v j).1)))
    · exact stdSimplex.continuous_map (fun j => (v j).2)

def simplexFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩

theorem prismAffine_face (m : ℕ) {k : ℕ} (v : Fin (k + 2) → Fin 2 × Fin (m + 1))
    (i : Fin (k + 2)) :
    (prismAffine m v).comp (simplexFaceMap k i) =
      prismAffine m (fun j : Fin (k + 1) => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro q
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun s : stdSimplex ℝ (Fin 2) => s.val 1)
      (stdSimplex.map_comp_apply i.succAbove (fun j : Fin (k + 2) => (v j).1) q)
  · exact stdSimplex.map_comp_apply i.succAbove (fun j : Fin (k + 2) => (v j).2) q

def prismSimplex (m j : ℕ) {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin (m + 1)), X))
    (v : Fin (j + 1) → Fin 2 × Fin (m + 1)) : integralSingularSimplex j X :=
  (integralSingularSimplexEquiv j X).symm (H.comp (prismAffine m v))

theorem prismSimplex_face (m j : ℕ) {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin (m + 1)), X))
    (v : Fin (j + 2) → Fin 2 × Fin (m + 1)) (i : Fin (j + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (prismSimplex m (j + 1) H v) =
      prismSimplex m j H (fun t : Fin (j + 1) => v (i.succAbove t)) := by
  apply (integralSingularSimplexEquiv j X).injective
  apply ContinuousMap.ext
  intro q
  change (TopCat.of X).toSSetObjEquiv _ ((TopCat.toSSet.obj (TopCat.of X)).δ i
    (prismSimplex m (j + 1) H v)) q =
      (integralSingularSimplexEquiv j X)
        (prismSimplex m j H (fun t : Fin (j + 1) => v (i.succAbove t))) q
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv (j + 1) X
      ((integralSingularSimplexEquiv (j + 1) X).symm (H.comp (prismAffine m v)))
        (stdSimplex.map i.succAbove q) =
      integralSingularSimplexEquiv j X
        ((integralSingularSimplexEquiv j X).symm
          (H.comp (prismAffine m (fun t : Fin (j + 1) => v (i.succAbove t))))) q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change H ((prismAffine m v) (stdSimplex.map i.succAbove q)) =
    H ((prismAffine m (fun t : Fin (j + 1) => v (i.succAbove t))) q)
  rw [← prismAffine_face m v i]
  rfl

def triangularPrismCells : Fin 3 → Fin 4 → Fin 2 × Fin 3 :=
  ![![(0, 0), (1, 0), (1, 1), (1, 2)],
    ![(0, 0), (0, 1), (1, 1), (1, 2)],
    ![(0, 0), (0, 1), (0, 2), (1, 2)]]

def triangularPrismCellFaces : Fin 3 → Fin 4 → Fin 3 → Fin 2 × Fin 3 :=
  ![![![(1, 0), (1, 1), (1, 2)], ![(0, 0), (1, 1), (1, 2)], ![(0, 0), (1, 0), (1, 2)],
      ![(0, 0), (1, 0), (1, 1)]],
    ![![(0, 1), (1, 1), (1, 2)], ![(0, 0), (1, 1), (1, 2)], ![(0, 0), (0, 1), (1, 2)],
      ![(0, 0), (0, 1), (1, 1)]],
    ![![(0, 1), (0, 2), (1, 2)], ![(0, 0), (0, 2), (1, 2)], ![(0, 0), (0, 1), (1, 2)],
      ![(0, 0), (0, 1), (0, 2)]]]

def triangularPrismEnd : Fin 2 → Fin 3 → Fin 2 × Fin 3 :=
  ![![(0, 0), (0, 1), (0, 2)], ![(1, 0), (1, 1), (1, 2)]]

def triangularPrismSides : Fin 6 → Fin 3 → Fin 2 × Fin 3 :=
  ![![(0, 0), (1, 0), (1, 2)], ![(0, 0), (1, 0), (1, 1)], ![(0, 1), (1, 1), (1, 2)],
    ![(0, 0), (0, 1), (1, 1)], ![(0, 1), (0, 2), (1, 2)], ![(0, 0), (0, 2), (1, 2)]]

def triangularPrismSideSigns : Fin 6 → ℤ := ![1, -1, -1, 1, 1, -1]

theorem triangularPrismCells_face (k : Fin 3) (i : Fin 4) :
    (fun j => triangularPrismCells k (i.succAbove j)) = triangularPrismCellFaces k i := by
  fin_cases k <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem triangularPrism_boundary {A : Type*} [AddCommGroup A]
    (F : (Fin 3 → Fin 2 × Fin 3) → A) :
    (∑ k : Fin 3, (-1 : ℤ) ^ k.val •
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
          F (fun j => triangularPrismCells k (i.succAbove j))) =
      F (triangularPrismEnd 1) - F (triangularPrismEnd 0) +
        ∑ s : Fin 6, triangularPrismSideSigns s • F (triangularPrismSides s) := by
  simp only [triangularPrismCells_face]
  norm_num [triangularPrismCellFaces, triangularPrismEnd, triangularPrismSides,
    triangularPrismSideSigns, Fin.sum_univ_succ]
  abel

def triangularPrismChain {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 3), X)) : (integralSingularChains X).X 3 :=
  ∑ k : Fin 3, (-1 : ℤ) ^ k.val •
    integralSimplexChain 3 (prismSimplex 2 3 H (triangularPrismCells k))

theorem triangularPrismChain_boundary {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 3), X)) :
    (integralSingularChains X).d 3 2 (triangularPrismChain H) =
      integralSimplexChain 2 (prismSimplex 2 2 H (triangularPrismEnd 1)) -
        integralSimplexChain 2 (prismSimplex 2 2 H (triangularPrismEnd 0)) +
        ∑ s : Fin 6, triangularPrismSideSigns s •
          integralSimplexChain 2 (prismSimplex 2 2 H (triangularPrismSides s)) := by
  have hface : ∀ k : Fin 3,
      (integralSingularChains X).d 3 2
          (integralSimplexChain 3 (prismSimplex 2 3 H (triangularPrismCells k))) =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
          integralSimplexChain 2 (prismSimplex 2 2 H
            (fun j => triangularPrismCells k (i.succAbove j))) := by
    intro k
    rw [integralSimplexChain_boundary]
    exact Finset.sum_congr rfl (fun i _ => by rw [prismSimplex_face])
  rw [triangularPrismChain, map_sum]
  simp only [map_zsmul, hface]
  exact triangularPrism_boundary (fun w => integralSimplexChain 2 (prismSimplex 2 2 H w))

def segmentPrismCells : Fin 2 → Fin 3 → Fin 2 × Fin 2 :=
  ![![(0, 0), (1, 0), (1, 1)], ![(0, 0), (0, 1), (1, 1)]]

def segmentPrismCellFaces : Fin 2 → Fin 3 → Fin 2 → Fin 2 × Fin 2 :=
  ![![![(1, 0), (1, 1)], ![(0, 0), (1, 1)], ![(0, 0), (1, 0)]],
    ![![(0, 1), (1, 1)], ![(0, 0), (1, 1)], ![(0, 0), (0, 1)]]]

def segmentPrismEnd : Fin 2 → Fin 2 → Fin 2 × Fin 2 :=
  ![![(0, 0), (0, 1)], ![(1, 0), (1, 1)]]

def segmentPrismSides : Fin 2 → Fin 2 → Fin 2 × Fin 2 :=
  ![![(0, 0), (1, 0)], ![(0, 1), (1, 1)]]

def segmentPrismSideSigns : Fin 2 → ℤ := ![1, -1]

theorem segmentPrismCells_face (k : Fin 2) (i : Fin 3) :
    (fun j => segmentPrismCells k (i.succAbove j)) = segmentPrismCellFaces k i := by
  fin_cases k <;> fin_cases i <;> funext j <;> fin_cases j <;> rfl

theorem segmentPrism_boundary {A : Type*} [AddCommGroup A]
    (F : (Fin 2 → Fin 2 × Fin 2) → A) :
    (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
        ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
          F (fun j => segmentPrismCells k (i.succAbove j))) =
      F (segmentPrismEnd 1) - F (segmentPrismEnd 0) +
        ∑ s : Fin 2, segmentPrismSideSigns s • F (segmentPrismSides s) := by
  simp only [segmentPrismCells_face]
  norm_num [segmentPrismCellFaces, segmentPrismEnd, segmentPrismSides, segmentPrismSideSigns,
    Fin.sum_univ_succ]
  abel

def segmentPrismChain {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 2), X)) : (integralSingularChains X).X 2 :=
  ∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    integralSimplexChain 2 (prismSimplex 1 2 H (segmentPrismCells k))

theorem segmentPrismChain_boundary {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 2), X)) :
    (integralSingularChains X).d 2 1 (segmentPrismChain H) =
      integralSimplexChain 1 (prismSimplex 1 1 H (segmentPrismEnd 1)) -
        integralSimplexChain 1 (prismSimplex 1 1 H (segmentPrismEnd 0)) +
        ∑ s : Fin 2, segmentPrismSideSigns s •
          integralSimplexChain 1 (prismSimplex 1 1 H (segmentPrismSides s)) := by
  have hface : ∀ k : Fin 2,
      (integralSingularChains X).d 2 1
          (integralSimplexChain 2 (prismSimplex 1 2 H (segmentPrismCells k))) =
        ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
          integralSimplexChain 1 (prismSimplex 1 1 H
            (fun j => segmentPrismCells k (i.succAbove j))) := by
    intro k
    rw [integralSimplexChain_boundary]
    exact Finset.sum_congr rfl (fun i _ => by rw [prismSimplex_face])
  rw [segmentPrismChain, map_sum]
  simp only [map_zsmul, hface]
  exact segmentPrism_boundary (fun w => integralSimplexChain 1 (prismSimplex 1 1 H w))

def pointPrismCells : Fin 1 → Fin 2 → Fin 2 × Fin 1 :=
  fun _ j => (j, 0)

def pointPrismEnd (b : Fin 2) : Fin 1 → Fin 2 × Fin 1 :=
  fun _ => (b, 0)

def pointPrismSimplex {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 1), X)) : integralSingularSimplex 1 X :=
  prismSimplex 0 1 H (pointPrismCells 0)

theorem pointPrismCells_face_zero :
    (fun t => pointPrismCells 0 ((0 : Fin 2).succAbove t)) = pointPrismEnd 1 := by
  funext t
  fin_cases t
  rfl

theorem pointPrismCells_face_one :
    (fun t => pointPrismCells 0 ((1 : Fin 2).succAbove t)) = pointPrismEnd 0 := by
  funext t
  fin_cases t
  rfl

theorem pointPrismSimplex_boundary {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 1), X)) :
    (integralSingularChains X).d 1 0 (integralSimplexChain 1 (pointPrismSimplex H)) =
      integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 1)) -
        integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 0)) := by
  rw [integralSimplexChain_boundary_one, pointPrismSimplex]
  rw [prismSimplex_face 0 0 H (pointPrismCells 0) 0,
    prismSimplex_face 0 0 H (pointPrismCells 0) 1, pointPrismCells_face_zero,
    pointPrismCells_face_one]

theorem exists_chain_boundary_pointPrism {X : Type u} [TopologicalSpace X]
    (H : C(unitInterval × stdSimplex ℝ (Fin 1), X)) :
    ∃ z : (integralSingularChains X).X 1,
      (integralSingularChains X).d 1 0 z =
        integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 1)) -
          integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 0)) :=
  ⟨integralSimplexChain 1 (pointPrismSimplex H), pointPrismSimplex_boundary H⟩

theorem pointPrismEnd_one_ne_zero : pointPrismEnd (1 : Fin 2) ≠ pointPrismEnd (0 : Fin 2) := by
  intro h
  have h1 : ((1 : Fin 2), (0 : Fin 1)) = ((0 : Fin 2), (0 : Fin 1)) := congrFun h 0
  exact Fin.zero_ne_one (Prod.mk.inj h1).1.symm

theorem exists_chain_boundary_pointPrism_liftedSphere
    (H : C(unitInterval × stdSimplex ℝ (Fin 1), liftedHomotopySphere.{u} 1)) :
    ∃ z : (integralSingularChains (liftedHomotopySphere.{u} 1)).X 1,
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 1 0 z =
        integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 1)) -
          integralSimplexChain 0 (prismSimplex 0 0 H (pointPrismEnd 0)) :=
  exists_chain_boundary_pointPrism H

open DifferentialGeometry.Topology.SimplexDegree in
theorem simplexBoundarySphereFilling_iff_liftedSphereTopEquiv_eq :
    SimplexBoundarySphereFilling.{u} ↔
      integralLiftedSphereTopEquiv.{u} 1
          (integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
            simplexBoundaryLiftedChain_apply_boundary) =
        integralLiftedSphereTopEquiv.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [simplexBoundarySphereFilling_iff_integralHomologyClass_eq,
    ← squareSphereFundamentalClass_eq_integralHomologyClass]
  exact ⟨fun h => congrArg _ h, fun h => (integralLiftedSphereTopEquiv.{u} 1).injective h⟩

open DifferentialGeometry.Topology.SimplexDegree in
theorem simplexBoundarySphereFilling_of_isSphereHomologyGenerator_and_functional
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u})
    (φ : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) →ₗ[ℤ] ℤ)
    (hφ : φ squareSphereFundamentalClass.{u} = 1)
    (hc : φ (integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
      simplexBoundaryLiftedChain_apply_boundary) = 1) :
    SimplexBoundarySphereFilling.{u} := by
  obtain ⟨e, he⟩ := hg
  have hsymm : e.symm 1 = squareSphereFundamentalClass.{u} := by
    rw [← he, LinearEquiv.symm_apply_apply]
  have hcomp : φ.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    have h1 : (φ.comp e.symm.toLinearMap) 1 = 1 := by
      change φ (e.symm 1) = 1
      rw [hsymm, hφ]
    rw [show x = x * (1 : ℤ) from (mul_one x).symm, ← smul_eq_mul, map_zsmul, h1]
    simp
  have hval : ∀ a, φ a = e a := by
    intro a
    have h := LinearMap.congr_fun hcomp (e a)
    change φ (e.symm (e a)) = e a at h
    rwa [LinearEquiv.symm_apply_apply] at h
  refine simplexBoundarySphereFilling_iff_integralHomologyClass_eq.mpr ?_
  apply e.injective
  rw [← squareSphereFundamentalClass_eq_integralHomologyClass,
    ← hval (integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
      simplexBoundaryLiftedChain_apply_boundary), hc, he]

end DifferentialGeometry.Topology.SimplexPrism
