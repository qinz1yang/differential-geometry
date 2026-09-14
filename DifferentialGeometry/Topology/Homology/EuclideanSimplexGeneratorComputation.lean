import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Metric Set Module
open scoped Topology Simplicial

namespace DifferentialGeometry.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def liftedTetrahedronFace (i : Fin 4) : C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

theorem liftedTetrahedronFace_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    (liftedTetrahedronFace i q).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin 3 → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)

def liftedTetrahedronSimplex : C(stdSimplex ℝ (Fin 4), liftedSphereSpace.{u} 1) where
  toFun q := (ULift.up (positiveTetrahedron q) : liftedSphereSpace.{u} 1)
  continuous_toFun :=
    (Homeomorph.ulift (X := ThreeSpace) :
        liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.continuous.comp
      positiveTetrahedron.continuous

theorem liftedTetrahedronSimplex_face_ne_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    liftedTetrahedronSimplex (liftedTetrahedronFace i q) ≠ (0 : liftedSphereSpace.{u} 1) := by
  intro hh
  exact positiveTetrahedron_face_ne_zero (liftedTetrahedronFace i q) i
    (liftedTetrahedronFace_zero i q) (ULift.up_inj.mp hh)

def euclideanStandardSimplexBoundaryChain :
    integralSingularCoefficients ⟶
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).X 2 :=
  puncturedSimplexBoundary (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
    liftedTetrahedronSimplex_face_ne_zero

theorem euclideanStandardSimplexBoundaryChain_boundary :
    euclideanStandardSimplexBoundaryChain ≫
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).d 2 1 = 0 :=
  puncturedSimplexBoundary_boundary (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
    liftedTetrahedronSimplex_face_ne_zero

theorem euclideanStandardSimplexBoundaryClass_eq_classOf :
    integralHomologyClassOf 1 euclideanStandardSimplexBoundaryChain
        euclideanStandardSimplexBoundaryChain_boundary =
      euclideanStandardSimplexBoundaryClass.{u} := rfl

theorem euclideanStandardSimplexClass_eq_simplexLocalClass :
    simplexLocalClass (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
        liftedTetrahedronSimplex_face_ne_zero =
      euclideanStandardSimplexClass.{u} := rfl

def liftedSimplexBoundarySphereMap :
    C(({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)),
      liftedHomotopySphere.{u} 1) :=
  (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun.comp
    (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun

def simplexBoundaryLiftedChain :
    integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 2 :=
  euclideanStandardSimplexBoundaryChain ≫
    (integralSingularChainMap liftedSimplexBoundarySphereMap).f 2

theorem simplexBoundaryLiftedChain_boundary :
    simplexBoundaryLiftedChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [simplexBoundaryLiftedChain, Category.assoc,
    (integralSingularChainMap liftedSimplexBoundarySphereMap).comm 2 1, ← Category.assoc,
    euclideanStandardSimplexBoundaryChain_boundary, Limits.zero_comp]

theorem euclideanStandardSimplexBoundarySphereClass_eq_map :
    euclideanStandardSimplexBoundarySphereClass.{u} =
      integralSingularHomologyMap 2 liftedSimplexBoundarySphereMap
        euclideanStandardSimplexBoundaryClass.{u} := by
  unfold euclideanStandardSimplexBoundarySphereClass
  rw [show integralSingularHomologyMap 2 liftedSimplexBoundarySphereMap =
      (integralSingularHomologyMap 2
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun).comp
      (integralSingularHomologyMap 2
        (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun)
      from integralSingularHomologyMap_comp 2
        (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun]
  rfl

theorem euclideanStandardSimplexBoundarySphereClass_eq_classOf :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [euclideanStandardSimplexBoundarySphereClass_eq_map,
    ← euclideanStandardSimplexBoundaryClass_eq_classOf,
    integralSingularHomologyMap_integralHomologyClassOf]
  rfl

theorem integralChainHom_squareSphereFundamentalChain_boundary :
    integralChainHom 2 squareSphereFundamentalChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [integralChainHom_d 1 squareSphereFundamentalChain, squareSphereFundamentalChain_boundary,
    integralChainHom_zero]

theorem squareSphereFundamentalClass_eq_classOf :
    integralHomologyClassOf 1 (integralChainHom 2 squareSphereFundamentalChain)
        integralChainHom_squareSphereFundamentalChain_boundary =
      squareSphereFundamentalClass.{u} := rfl

def SimplexBoundarySphereAlignment : Prop :=
  integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      squareSphereFundamentalClass.{u} ∨
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      -squareSphereFundamentalClass.{u}

def SimplexBoundarySphereFilling : Prop :=
  ∃ z : integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 3,
    (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        simplexBoundaryLiftedChain - integralChainHom 2 squareSphereFundamentalChain) ∨
      (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        integralChainHom 2 squareSphereFundamentalChain - simplexBoundaryLiftedChain)

theorem simplexBoundarySphereAlignment_of_filling (h : SimplexBoundarySphereFilling.{u}) :
    SimplexBoundarySphereAlignment.{u} := by
  obtain ⟨z, hz | hz⟩ := h
  · left
    refine (integralHomologyClassOf_eq_of_sub_eq 1 simplexBoundaryLiftedChain
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain_boundary
      integralChainHom_squareSphereFundamentalChain_boundary z hz.symm).trans ?_
    exact squareSphereFundamentalClass_eq_classOf.symm
  · left
    exact (integralHomologyClassOf_eq_of_sub_eq 1
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain
      integralChainHom_squareSphereFundamentalChain_boundary simplexBoundaryLiftedChain_boundary
      z hz.symm).symm.trans squareSphereFundamentalClass_eq_classOf

theorem isSphereHomologyGenerator_neg (n : ℕ)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHomologyGenerator n c) : IsSphereHomologyGenerator n (-c) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.trans (LinearEquiv.neg ℤ), ?_⟩
  simp [LinearEquiv.trans_apply, he]

theorem isSphereHomologyGenerator_of_simplexBoundarySphereAlignment
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 1 euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf]
  rcases halign with h | h
  · rwa [h]
  · rw [h]
    exact isSphereHomologyGenerator_neg 1 hg

theorem euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} :=
  euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mpr
    (isSphereHomologyGenerator_of_simplexBoundarySphereAlignment halign hg)

theorem euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} :=
  euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment
    (simplexBoundarySphereAlignment_of_filling h) hg

theorem simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator
    (h : euclideanStandardSimplexClassGenerator.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    SimplexBoundarySphereAlignment.{u} := by
  have hc := euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mp h
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf] at hc
  rcases IsSphereHomologyGenerator.eq_or_eq_neg 1 hc hg with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

theorem euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} ↔ SimplexBoundarySphereAlignment.{u} :=
  ⟨fun h => simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator h hg,
    fun h => euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment h hg⟩

theorem euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexBoundarySphereClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 1
    (isSphereHomologyGenerator_of_simplexBoundarySphereAlignment
      (simplexBoundarySphereAlignment_of_filling h) hg)

theorem euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u}) :
    euclideanStandardSimplexBoundarySphereClass.{u} = 0 ↔
      squareSphereFundamentalClass.{u} = 0 := by
  have halign := simplexBoundarySphereAlignment_of_filling h
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf]
  rcases halign with h' | h'
  · rw [h']
  · rw [h', neg_eq_zero]

theorem not_simplexBoundarySphereAlignment_two_zsmul
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    ¬ (integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          (2 : ℤ) • squareSphereFundamentalClass.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -((2 : ℤ) • squareSphereFundamentalClass.{u})) := by
  obtain ⟨e, he⟩ := hg
  have h2 : e ((2 : ℤ) • squareSphereFundamentalClass.{u}) = 2 := by
    have h : e.toLinearMap ((2 : ℤ) • squareSphereFundamentalClass.{u}) =
        2 • e.toLinearMap squareSphereFundamentalClass.{u} :=
      map_zsmul e.toLinearMap (2 : ℤ) squareSphereFundamentalClass.{u}
    have hone : e.toLinearMap squareSphereFundamentalClass.{u} = 1 := he
    rw [hone] at h
    simpa using h
  have hc : e (integralHomologyClassOf 1 simplexBoundaryLiftedChain
        simplexBoundaryLiftedChain_boundary) = 1 ∨
      e (integralHomologyClassOf 1 simplexBoundaryLiftedChain
        simplexBoundaryLiftedChain_boundary) = -1 := by
    rcases halign with h | h
    · left
      rw [h, he]
    · right
      rw [h, map_neg, he]
  rintro (h | h)
  · rw [h, h2] at hc
    omega
  · rw [h, map_neg, h2] at hc
    omega

end DifferentialGeometry.Topology
