import DifferentialGeometry.Topology.SphereSeparation.SubdivisionBoundary

set_option autoImplicit false

open CategoryTheory

namespace Poincare.Topology.SphereSeparation

noncomputable def singularBarycentricSubdivision (X : TopCat) :
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X ⟶
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).obj X :=
  barycentricSubdivisionChainEndomorphism X
    (barycentricSubdivisionBoundaryCompatible X)

@[simp]
theorem singularBarycentricSubdivision_f
    (X : TopCat) (n : ℕ) :
    (singularBarycentricSubdivision X).f n =
      barycentricSubdivisionDegreeMap X n :=
  rfl

@[simp]
theorem singularBarycentricSubdivision_f_zero (X : TopCat) :
    (singularBarycentricSubdivision X).f 0 = 𝟙 _ :=
  barycentricSubdivisionDegreeMap_zero X


theorem singularBarycentricSubdivision_naturality
    {X Y : TopCat} (f : X ⟶ Y) :
    singularBarycentricSubdivision X ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        singularBarycentricSubdivision Y :=
  barycentricSubdivisionChainEndomorphism_naturality f
    (barycentricSubdivisionBoundaryCompatible X)
    (barycentricSubdivisionBoundaryCompatible Y)


noncomputable def singularBarycentricSubdivisionIterate
    (X : TopCat) : (k : ℕ) →
    End (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj X)
  | 0 => 𝟙 _
  | k + 1 => singularBarycentricSubdivisionIterate X k ≫
      singularBarycentricSubdivision X

@[simp]
theorem singularBarycentricSubdivisionIterate_zero (X : TopCat) :
    singularBarycentricSubdivisionIterate X 0 = 𝟙 _ := by
  rfl

theorem singularBarycentricSubdivisionIterate_succ
    (X : TopCat) (k : ℕ) :
    singularBarycentricSubdivisionIterate X (k + 1) =
      singularBarycentricSubdivisionIterate X k ≫
        singularBarycentricSubdivision X := by
  rfl


theorem singularBarycentricSubdivisionIterate_naturality
    {X Y : TopCat} (f : X ⟶ Y) (k : ℕ) :
    singularBarycentricSubdivisionIterate X k ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        singularBarycentricSubdivisionIterate Y k := by
  induction k with
  | zero => simp [singularBarycentricSubdivisionIterate]
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ,
        singularBarycentricSubdivisionIterate_succ,
        Category.assoc, singularBarycentricSubdivision_naturality,
        ← Category.assoc, ih, Category.assoc]

@[simp]
theorem singularBarycentricSubdivisionIterate_f_zero
    (X : TopCat) (k : ℕ) :
    (singularBarycentricSubdivisionIterate X k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp [singularBarycentricSubdivisionIterate]
  | succ k ih =>
      rw [singularBarycentricSubdivisionIterate_succ]
      simp only [HomologicalComplex.comp_f,
        singularBarycentricSubdivision_f_zero, ih, Category.comp_id]

end Poincare.Topology.SphereSeparation
