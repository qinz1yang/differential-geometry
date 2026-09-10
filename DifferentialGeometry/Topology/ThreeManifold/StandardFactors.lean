import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import Mathlib.Topology.Covering.Basic

noncomputable section

open Manifold Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

structure SphericalSpaceFormGroup where
  group : Subgroup (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
  [finite : Finite group]
  positive : ∀ γ : group, (Geometry.sphereDiffeo (n := 3) γ.val).preservesOrientation
    (sphereOrientation 3 (by decide)) (sphereOrientation 3 (by decide))
  free : ∀ γ : group, ∀ x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
    Geometry.sphereDiffeo (n := 3) γ.val x = x → γ = 1

attribute [instance] SphericalSpaceFormGroup.finite

namespace SphericalSpaceFormGroup

variable (G : SphericalSpaceFormGroup)

def orbitSetoid : Setoid (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  r x y := ∃ γ : G.group, Geometry.sphereDiffeo (n := 3) γ.val x = y
  iseqv := {
    refl := fun x ↦ ⟨1, Subtype.ext rfl⟩
    symm := by
      rintro x y ⟨γ, rfl⟩
      refine ⟨γ⁻¹, ?_⟩
      apply Subtype.ext
      change γ.val.symm (γ.val (x : EuclideanSpace ℝ (Fin 4))) = x
      exact γ.val.symm_apply_apply x
    trans := by
      rintro x y z ⟨γ, rfl⟩ ⟨δ, rfl⟩
      exact ⟨δ * γ, Subtype.ext rfl⟩ }

abbrev Orbit := Quotient G.orbitSetoid

def projection : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → G.Orbit :=
  Quotient.mk G.orbitSetoid

theorem projection_eq_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    G.projection x = G.projection y ↔
      ∃ γ : G.group, Geometry.sphereDiffeo (n := 3) γ.val x = y :=
  Quotient.eq

theorem projection_surjective : Function.Surjective G.projection :=
  Quotient.mk_surjective

theorem projection_isQuotientMap : _root_.Topology.IsQuotientMap G.projection :=
  isQuotientMap_quotient_mk'

theorem projection_continuous : Continuous G.projection :=
  G.projection_isQuotientMap.continuous

theorem projection_invariant (γ : G.group)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    G.projection (Geometry.sphereDiffeo (n := 3) γ.val x) = G.projection x := by
  symm
  exact (G.projection_eq_iff _ _).2 ⟨γ, rfl⟩

structure SmoothQuotient where
  [charts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Orbit]
  [smooth : IsManifold (𝓡 3) ∞ G.Orbit]
  [hausdorff : T2Space G.Orbit]
  [compact : CompactSpace G.Orbit]
  [connected : ConnectedSpace G.Orbit]
  local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ G.projection
  covering : IsCoveringMap G.projection
  orientation : ManifoldOrientation (𝓡 3) G.Orbit 3
  positive : ∀ x, Orientation.map (Fin 3)
    (local_diffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    ((sphereOrientation 3 (by decide)).orientation x) = orientation.orientation (G.projection x)

theorem exists_smooth_quotient : Nonempty G.SmoothQuotient := by
  sorry

def smoothQuotient : G.SmoothQuotient := Classical.choice G.exists_smooth_quotient

instance orbitChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.Orbit :=
  G.smoothQuotient.charts

instance orbitIsManifold : IsManifold (𝓡 3) ∞ G.Orbit := G.smoothQuotient.smooth

instance orbitT2Space : T2Space G.Orbit := G.smoothQuotient.hausdorff

instance orbitCompactSpace : CompactSpace G.Orbit := G.smoothQuotient.compact

instance orbitConnectedSpace : ConnectedSpace G.Orbit := G.smoothQuotient.connected

def manifold : ConnectedClosedOrientedManifold 3 where
  Carrier := G.Orbit
  orientation := G.smoothQuotient.orientation

@[simp] theorem manifold_carrier : G.manifold.Carrier = G.Orbit := rfl

theorem projection_isLocalDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ G.projection :=
  G.smoothQuotient.local_diffeomorph

theorem projection_isCoveringMap : IsCoveringMap G.projection := G.smoothQuotient.covering

theorem projection_positive (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Orientation.map (Fin 3)
      (G.projection_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      ((sphereOrientation 3 (by decide)).orientation x) =
        G.manifold.orientation.orientation (G.projection x) :=
  G.smoothQuotient.positive x

end SphericalSpaceFormGroup

abbrev SphereTwoTimesCircle :=
  sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

def sphereTwoTimesCircleOrientation :
    ManifoldOrientation ((𝓡 2).prod (𝓡 1)) SphereTwoTimesCircle 3 :=
  productOrientation (𝓡 2) (𝓡 1) (by decide) (by decide)
    (sphereOrientation 2 (by decide)) (sphereOrientation 1 (by decide))

def isStandardFactor (M : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  (∃ G : SphericalSpaceFormGroup,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      M.toClosedOrientedManifold G.manifold.toClosedOrientedManifold)) ∨
  ∃ f : M.Carrier ≃ₘ⟮𝓡 3, (𝓡 2).prod (𝓡 1)⟯ SphereTwoTimesCircle,
    f.preservesOrientation M.orientation sphereTwoTimesCircleOrientation

theorem isStandardFactor_spherical (G : SphericalSpaceFormGroup) :
    isStandardFactor G.manifold :=
  Or.inl ⟨G, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

end DifferentialGeometry.Topology
