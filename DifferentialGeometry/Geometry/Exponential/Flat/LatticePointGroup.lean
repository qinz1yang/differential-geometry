import DifferentialGeometry.Geometry.Exponential.Flat.PlaneIsometry
import Mathlib.Data.Set.Finite.Powerset

/-!
# Finite point groups of full Euclidean lattices

The image of each basis vector under a lattice-preserving linear isometry lies in a bounded
finite subset of the actual integer lattice. Evaluation on the basis determines the isometry,
so the whole collection is finite. This result accepts an actual full basis; it does not prove
that the translation subgroup of a cocompact Euclidean deck group spans the ambient space.
-/

set_option autoImplicit false

noncomputable section

open Set Module Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]
  {ι : Type*} [instIota : Finite ι]

theorem finite_basisLattice_pointGroup (b : Basis ι ℝ V) :
    Set.Finite {A : V ≃ₗᵢ[ℝ] V | ∀ i, A (b i) ∈ Submodule.span ℤ (Set.range b)} := by
  let L := Submodule.span ℤ (Set.range b)
  let S : ι → Set V := fun i => Metric.closedBall 0 ‖b i‖ ∩ L
  have hS : ∀ i, (S i).Finite := fun i =>
    ZSpan.setFinite_inter b Metric.isBounded_closedBall
  have hpi : (Set.univ.pi S).Finite := Set.Finite.pi hS
  let ev : (V ≃ₗᵢ[ℝ] V) → ι → V := fun A i => A (b i)
  have hinj : Function.Injective ev := by
    intro A B hAB
    exact b.ext_linearIsometryEquiv fun i => congrFun hAB i
  refine Set.Finite.of_finite_image (hpi.subset ?_) hinj.injOn
  rintro y ⟨A, hA, rfl⟩
  intro i hi
  refine ⟨?_, hA i⟩
  exact mem_closedBall_zero_iff.mpr (le_of_eq (A.norm_map (b i)))

theorem finite_lattice_pointGroup (b : Basis ι ℝ V) :
    Set.Finite {A : V ≃ₗᵢ[ℝ] V |
      Set.MapsTo A (Submodule.span ℤ (Set.range b)) (Submodule.span ℤ (Set.range b))} := by
  refine (finite_basisLattice_pointGroup b).subset ?_
  intro A hA i
  exact hA (Submodule.subset_span (Set.mem_range_self i))

theorem finite_standard_three_pointGroup :
    Set.Finite {A : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) |
      Set.MapsTo A
        (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis))
        (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis))} :=
  finite_lattice_pointGroup (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

end DifferentialGeometry.Geometry.FlatSurface
