import DifferentialGeometry.Topology.Homology.SimplexPrismChain

noncomputable section

namespace DifferentialGeometry.Topology

universe u

def liftedSphereDegreeFunctional (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ :=
  (integralLiftedSphereTopEquiv n).toLinearMap

theorem liftedSphereDegreeFunctional_apply (n : ℕ)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    liftedSphereDegreeFunctional.{u} n c = integralLiftedSphereTopEquiv.{u} n c := rfl

theorem liftedSphereDegreeFunctional_generator (n : ℕ) :
    liftedSphereDegreeFunctional.{u} n (integralLiftedSphereGenerator.{u} n) = 1 :=
  integralLiftedSphereGenerator_coordinate n

theorem liftedSphereDegreeFunctional_injective (n : ℕ) :
    Function.Injective (liftedSphereDegreeFunctional.{u} n) :=
  fun _ _ h => (integralLiftedSphereTopEquiv.{u} n).injective h

def simplexBoundaryLiftedSphereClass :
    integralSingularHomology 2 (liftedHomotopySphere.{u} 1) :=
  integralHomologyClass 1 (SimplexDegree.simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
    SimplexDegree.simplexBoundaryLiftedChain_apply_boundary

theorem simplexBoundaryLiftedSphereClass_eq_classOf :
    simplexBoundaryLiftedSphereClass.{u} =
      integralHomologyClassOf 1 SimplexDegree.simplexBoundaryLiftedChain
        SimplexDegree.simplexBoundaryLiftedChain_boundary :=
  SimplexDegree.simplexBoundaryLiftedChain_class_eq_integralHomologyClass.symm

def HasSimplexBoundarySphereDegreeFunctional : Prop :=
  ∃ φ : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) →ₗ[ℤ] ℤ,
    φ squareSphereFundamentalClass.{u} = 1 ∧ φ simplexBoundaryLiftedSphereClass.{u} = 1

theorem eq_of_apply_squareSphereFundamentalClass_eq_one
    {φ ψ : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) →ₗ[ℤ] ℤ}
    (hφ : φ squareSphereFundamentalClass.{u} = 1)
    (hψ : ψ squareSphereFundamentalClass.{u} = 1) : φ = ψ := by
  have hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} :=
    (isSphereHomologyGenerator_iff_exists_functional 1 squareSphereFundamentalClass.{u}).mpr
      ⟨φ, hφ⟩
  have hdiv := (isSphereHomologyGenerator_iff_forall_exists_zsmul 1
    squareSphereFundamentalClass.{u}).mp hgen
  ext z
  obtain ⟨k, hk⟩ := hdiv z
  rw [hk, map_zsmul, map_zsmul, hφ, hψ]

theorem simplexBoundarySphereFilling_iff_liftedSphereDegreeFunctional_apply_eq :
    SimplexDegree.SimplexBoundarySphereFilling.{u} ↔
      liftedSphereDegreeFunctional.{u} 1 simplexBoundaryLiftedSphereClass.{u} =
        liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [SimplexPrism.simplexBoundarySphereFilling_iff_liftedSphereTopEquiv_eq]
  exact Iff.rfl

theorem simplexBoundarySphereFilling_of_hasSimplexBoundarySphereDegreeFunctional
    (h : HasSimplexBoundarySphereDegreeFunctional.{u}) :
    SimplexDegree.SimplexBoundarySphereFilling.{u} := by
  obtain ⟨φ, hsquare, hsimplex⟩ := h
  have hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} :=
    (isSphereHomologyGenerator_iff_exists_functional 1 squareSphereFundamentalClass.{u}).mpr
      ⟨φ, hsquare⟩
  exact SimplexPrism.simplexBoundarySphereFilling_of_isSphereHomologyGenerator_and_functional
    hgen φ hsquare hsimplex

theorem hasSimplexBoundarySphereDegreeFunctional_iff_filling_and_isSphereHomologyGenerator :
    HasSimplexBoundarySphereDegreeFunctional.{u} ↔
      SimplexDegree.SimplexBoundarySphereFilling.{u} ∧
        IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} := by
  constructor
  · intro h
    obtain ⟨φ, hsquare, hsimplex⟩ := h
    exact ⟨simplexBoundarySphereFilling_of_hasSimplexBoundarySphereDegreeFunctional
        ⟨φ, hsquare, hsimplex⟩,
      (isSphereHomologyGenerator_iff_exists_functional 1 squareSphereFundamentalClass.{u}).mpr
        ⟨φ, hsquare⟩⟩
  · rintro ⟨hfilling, hgen⟩
    obtain ⟨e, he⟩ := hgen
    refine ⟨e.toLinearMap, he, ?_⟩
    rw [simplexBoundaryLiftedSphereClass_eq_classOf,
      SimplexDegree.simplexBoundarySphereFilling_iff_class_eq.mp hfilling]
    exact he

theorem simplexBoundarySphereFilling_of_liftedSphereDegreeFunctional_apply_eq_one
    (hsquare : liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} = 1)
    (hsimplex : liftedSphereDegreeFunctional.{u} 1 simplexBoundaryLiftedSphereClass.{u} = 1) :
    SimplexDegree.SimplexBoundarySphereFilling.{u} :=
  simplexBoundarySphereFilling_of_hasSimplexBoundarySphereDegreeFunctional
    ⟨liftedSphereDegreeFunctional 1, hsquare, hsimplex⟩

theorem hasSimplexBoundarySphereDegreeFunctional_iff_liftedSphereDegreeFunctional_apply_eq :
    HasSimplexBoundarySphereDegreeFunctional.{u} ↔
      (liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} = 1 ∨
        liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} = -1) ∧
      liftedSphereDegreeFunctional.{u} 1 simplexBoundaryLiftedSphereClass.{u} =
        liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} := by
  rw [hasSimplexBoundarySphereDegreeFunctional_iff_filling_and_isSphereHomologyGenerator,
    simplexBoundarySphereFilling_iff_liftedSphereDegreeFunctional_apply_eq,
    isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate]
  simp only [liftedSphereDegreeFunctional_apply]
  exact and_comm

theorem simplexBoundarySphereFilling_iff_liftedSphereDegreeFunctional_apply_eq_one_or_eq_neg
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    SimplexDegree.SimplexBoundarySphereFilling.{u} ↔
      (liftedSphereDegreeFunctional.{u} 1 simplexBoundaryLiftedSphereClass.{u} = 1 ∧
        liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} = 1) ∨
      (liftedSphereDegreeFunctional.{u} 1 simplexBoundaryLiftedSphereClass.{u} = -1 ∧
        liftedSphereDegreeFunctional.{u} 1 squareSphereFundamentalClass.{u} = -1) := by
  rw [simplexBoundarySphereFilling_iff_liftedSphereDegreeFunctional_apply_eq]
  simp only [liftedSphereDegreeFunctional_apply]
  rcases (isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate.mp hgen) with h | h
  · constructor
    · intro hEq
      exact Or.inl ⟨hEq.trans h, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h1.trans h2.symm
      · omega
  · constructor
    · intro hEq
      exact Or.inr ⟨hEq.trans h, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · omega
      · exact h1.trans h2.symm

theorem euclideanStandardSimplexClass_generator_of_hasSimplexBoundarySphereDegreeFunctional
    (h : HasSimplexBoundarySphereDegreeFunctional.{u}) :
    Function.Bijective (fun z : ℤ => z • SimplexDegree.euclideanStandardSimplexClass.{u}) :=
  SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling
    (simplexBoundarySphereFilling_of_hasSimplexBoundarySphereDegreeFunctional h)
    ((hasSimplexBoundarySphereDegreeFunctional_iff_filling_and_isSphereHomologyGenerator.mp
      h).2)

theorem exists_functional_apply_fst_eq_one_and_apply_snd_eq_one :
    ∃ φ : ℤ × ℤ →ₗ[ℤ] ℤ, φ (1, 0) = 1 ∧ φ (0, 1) = 1 :=
  ⟨(LinearMap.fst ℤ ℤ ℤ) + (LinearMap.snd ℤ ℤ ℤ), by simp, by simp⟩

theorem not_forall_exists_functional_apply_eq_one_and_apply_eq_one_imp_eq :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module ℤ M] (x y : M),
      (∃ φ : M →ₗ[ℤ] ℤ, φ x = 1 ∧ φ y = 1) → y = x := by
  intro h
  have hxy := h (ℤ × ℤ) (1, 0) (0, 1)
    (exists_functional_apply_fst_eq_one_and_apply_snd_eq_one)
  simp at hxy

end DifferentialGeometry.Topology
