import DifferentialGeometry.Topology.Homology.TriangleFilling



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]



def integralSingularConeZero (a : X) :
    (integralSingularChains X).X 0 →ₗ[ℤ] (integralSingularChains X).X 1 :=
  (integralSingularChainBasis 0 X).constr (M' := (integralSingularChains X).X 1) ℕ (fun σ =>
    integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)))


theorem integralSingularConeZero_simplex (a : X) (σ : integralSingularSimplex 0 X) :
    integralSingularConeZero a (integralSimplexChain 0 σ) =
      integralPathChain (PathConnectedSpace.somePath a (TopCat.toSSetObj₀Equiv σ)) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 0 X).constr_basis ℕ _ σ



def integralSingularConeTriangle (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularSimplex 2 X :=
  (exists_integralPathTriangle (PathConnectedSpace.somePath a _)
    (integralSimplexPath σ) (PathConnectedSpace.somePath a _)).choose


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


theorem integralSingularConeTriangle_boundary (a : X) (σ : integralSingularSimplex 1 X) :
    (integralSingularChains X).d 2 1 (integralSimplexChain 2 (integralSingularConeTriangle a σ)) =
      integralSimplexChain 1 σ -
        integralSingularConeZero a (integralSimplexChain 0
          ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) +
        integralSingularConeZero a (integralSimplexChain 0
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) := by
  rw [integralSimplexChain_boundary_two, integralSingularConeTriangle_face a σ 0,
    integralSingularConeTriangle_face a σ 1, integralSingularConeTriangle_face a σ 2]
  change integralPathChain (integralSimplexPath σ) -
      integralPathChain (PathConnectedSpace.somePath a _) +
      integralPathChain (PathConnectedSpace.somePath a _) = _
  rw [integralPathChain_simplexPath, integralSingularConeZero_simplex,
    integralSingularConeZero_simplex]



def integralSingularConeOne (a : X) :
    (integralSingularChains X).X 1 →ₗ[ℤ] (integralSingularChains X).X 2 :=
  (integralSingularChainBasis 1 X).constr (M' := (integralSingularChains X).X 2) ℕ (fun σ =>
    integralSimplexChain 2 (integralSingularConeTriangle a σ))


theorem integralSingularConeOne_simplex (a : X) (σ : integralSingularSimplex 1 X) :
    integralSingularConeOne a (integralSimplexChain 1 σ) =
      integralSimplexChain 2 (integralSingularConeTriangle a σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 1 X).constr_basis ℕ _ σ



theorem integralSingularConeOne_equation (a : X) :
    ((integralSingularChains X).d 2 1).hom.comp (integralSingularConeOne a) =
      LinearMap.id - (integralSingularConeZero a).comp ((integralSingularChains X).d 1 0).hom := by
  apply (integralSingularChainBasis 1 X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    integralSingularConeOne_simplex, integralSingularConeTriangle_boundary,
    integralSimplexChain_boundary_one, map_sub]
  abel


theorem integralSingularConeOne_bounds (a : X) (c : (integralSingularChains X).X 1)
    (hc : (integralSingularChains X).d 1 0 c = 0) :
    (integralSingularChains X).d 2 1 (integralSingularConeOne a c) = c := by
  have h := LinearMap.congr_fun (integralSingularConeOne_equation a) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    hc, map_zero, sub_zero] using h



theorem integralSingularHomology_one_subsingleton :
    Subsingleton (integralSingularHomology 1 X) := by
  apply (integralSingularHomology_vanishing_iff 0 X).mpr
  intro c hc
  let a : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨integralSingularConeOne a c, integralSingularConeOne_bounds a c hc⟩

end DifferentialGeometry.Topology
