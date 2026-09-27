import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.PathCones

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem integralSingularConeTriangle_face (a : X) (σ : integralSingularSimplex 1 X)
    (i : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (integralSingularConeTriangle a σ) =
      ![integralPathSimplex (integralSimplexPath σ),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))),
        integralPathSimplex (PathConnectedSpace.somePath a
          (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)))] i :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose_spec i

@[simp] theorem integralSingularConeTriangle_face_zero (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle a σ) = σ := by
  rw [integralSingularConeTriangle_face]
  exact integralPathSimplex_simplexPath σ

@[simp] theorem integralSingularConeTriangle_face_one (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle a σ) =
      integralPathSimplex (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))) := by
  exact integralSingularConeTriangle_face a σ 1

@[simp] theorem integralSingularConeTriangle_face_two (a : X) (σ : integralSingularSimplex 1 X) :
    (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle a σ) =
      integralPathSimplex (PathConnectedSpace.somePath a
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))) := by
  exact integralSingularConeTriangle_face a σ 2

end DifferentialGeometry.Topology
