import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary
import DifferentialGeometry.Topology.ThreeManifold.CutCap

/-!
Actual ball caps on spherical boundary components, retaining every torus collar of the core.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

local instance capBallCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance capBallSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

def closureSphereToBall (z : ClosureSphere.{u}) : ClosedCell 3 :=
  sphereToClosedCell z.down

structure RelativeSphereCapping (C Q : CompactCarrier.{u})
    (B : MixedBoundaryCertificate C) where
  core : C(C.Carrier, Q.Carrier)
  core_embedding : IsSmoothEmbedding C.model Q.model ∞ core
  cap : Fin B.sphereCount → C(ClosedCell 3, Q.Carrier)
  cap_embedding : ∀ i, IsSmoothEmbedding (𝓡∂ 3) Q.model ∞ (cap i)
  attaching : Fin B.sphereCount →
    (ClosureSphere.{u} ≃ₘ⟮𝓡 2, 𝓡 2⟯ ClosureSphere.{u})
  boundary_eq : ∀ i z, cap i (closureSphereToBall z) =
    core (B.sphere i (attaching i z, halfZero))
  covers : range core ∪ (⋃ i, range (cap i)) = univ
  core_cap_intersection : ∀ i, range core ∩ range (cap i) =
    range fun z => core (B.sphere i (z, halfZero))
  cap_disjoint : Pairwise fun i j => Disjoint (range (cap i)) (range (cap j))
  retained : BoundaryTori Q B.torusCount
  retained_collar : ∀ i p, p ∈ halfCollarSource →
    retained.collar i p = core (B.tori.collar i p)
  boundary_exhausted : Q.model.boundary Q.Carrier = retained.image
  core_positive : ∀ x : C.Carrier, C.model.IsInteriorPoint x →
    ∃ h : Function.Bijective (mfderiv C.model Q.model core x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv C.model Q.model core x).toLinearMap h)
        (C.orientation.orientation x) = Q.orientation.orientation (core x)
  cap_positive : ∀ i x, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) Q.model (cap i) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) Q.model (cap i) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          Q.orientation.orientation (cap i x)

namespace RelativeSphereCapping

variable {C Q : CompactCarrier.{u}} {B : MixedBoundaryCertificate C}
    (K : RelativeSphereCapping C Q B)

theorem retained_zero (i : Fin B.torusCount) (t : Torus) :
    K.retained.torusMap i t = K.core (B.tori.torusMap i t) := by
  apply K.retained_collar
  change (0 : ℝ) < 1
  norm_num

theorem every_point (x : Q.Carrier) :
    (∃ y : C.Carrier, K.core y = x) ∨ ∃ i y, K.cap i y = x := by
  have hx : x ∈ range K.core ∪ (⋃ i, range (K.cap i)) := K.covers ▸ mem_univ x
  rcases hx with hcore | hcap
  · exact Or.inl hcore
  · obtain ⟨i, y, hy⟩ := mem_iUnion.mp hcap
    exact Or.inr ⟨i, y, hy⟩

def boundaryCertificate : MixedBoundaryCertificate Q :=
  MixedBoundaryCertificate.ofTori K.retained K.boundary_exhausted

theorem boundaryCertificate_torusCount : K.boundaryCertificate.torusCount = B.torusCount := rfl

theorem boundaryCertificate_sphereCount : K.boundaryCertificate.sphereCount = 0 := rfl

end RelativeSphereCapping

end GC.GraphManifold
