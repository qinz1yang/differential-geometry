import DifferentialGeometry.Topology.Homology.SimplexBoundary
import DifferentialGeometry.Topology.Homology.Cycles



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {x y : X}


def integralVertexChain (x : X) : (integralSingularChains X).X 0 :=
  integralSimplexChain 0 (TopCat.toSSetObj₀Equiv.symm x)


def integralPathSimplex (p : Path x y) : integralSingularSimplex 1 X :=
  TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom


def integralPathChain (p : Path x y) : (integralSingularChains X).X 1 :=
  integralSimplexChain 1 (integralPathSimplex p)


theorem integralPathChain_boundary (p : Path x y) :
    (integralSingularChains X).d 1 0 (integralPathChain p) =
      integralVertexChain y - integralVertexChain x := by
  change (integralSingularChains X).d 1 0 (integralSimplexChain 1
    (TopCat.toSSetObj₁Equiv.symm (TopCat.pathEquiv.symm p).hom)) = _
  rw [integralSimplexChain_boundary_one]
  simp only [TopCat.δ_zero_toSSetObj₁Equiv.symm, TopCat.δ_one_toSSetObj₁Equiv.symm]
  change integralVertexChain (p 1) - integralVertexChain (p 0) = _
  rw [Path.target, Path.source]


def integralSimplexPath (σ : integralSingularSimplex 1 X) :
    Path (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
      (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) where
  toFun t := TopCat.toSSetObj₁Equiv σ (TopCat.I.homeomorph.symm t)
  continuous_toFun := (TopCat.toSSetObj₁Equiv σ).hom.continuous.comp TopCat.I.homeomorph.symm.continuous
  source' := TopCat.toSSetObj₁Equiv_apply_zero σ
  target' := TopCat.toSSetObj₁Equiv_apply_one σ



theorem integralPathSimplex_simplexPath (σ : integralSingularSimplex 1 X) :
    integralPathSimplex (integralSimplexPath σ) = σ := by
  apply TopCat.toSSetObj₁Equiv.injective
  change TopCat.toSSetObj₁Equiv (TopCat.toSSetObj₁Equiv.symm
    (TopCat.pathEquiv.symm (integralSimplexPath σ)).hom) = TopCat.toSSetObj₁Equiv σ
  rw [Equiv.apply_symm_apply]
  ext t
  change TopCat.toSSetObj₁Equiv σ (TopCat.I.homeomorph.symm (TopCat.I.homeomorph t)) =
    TopCat.toSSetObj₁Equiv σ t
  rw [Homeomorph.symm_apply_apply]



theorem integralPathChain_simplexPath (σ : integralSingularSimplex 1 X) :
    integralPathChain (integralSimplexPath σ) = integralSimplexChain 1 σ := by
  unfold integralPathChain
  rw [integralPathSimplex_simplexPath]

end DifferentialGeometry.Topology
