import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.SphereOrientation
import DifferentialGeometry.Topology.Manifold.ProductOrientation
import DifferentialGeometry.Topology.Manifold.Quotient
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

instance instMulActionSphere : MulAction G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  smul γ x := Geometry.sphereDiffeo (n := 3) γ.val x
  one_smul x := by
    apply Subtype.ext
    change (((1 : G.group) : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
      (x : EuclideanSpace ℝ (Fin 4))) = (x : EuclideanSpace ℝ (Fin 4))
    simp
  mul_smul a b x := by
    apply Subtype.ext
    change (((a * b : G.group) : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
        (x : EuclideanSpace ℝ (Fin 4))) =
      ((a : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
        (((b : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)))
          (x : EuclideanSpace ℝ (Fin 4))))
    simp

instance instContMDiffConstSMulSphere :
    ContMDiffConstSMul (𝓡 3) ∞ G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  contMDiff_const_smul γ :=
    (Geometry.sphereDiffeo (n := 3) γ.val).contMDiff

instance instContinuousConstSMulSphere :
    ContinuousConstSMul G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  continuous_const_smul γ :=
    ((Geometry.sphereDiffeo (n := 3) γ.val).contMDiff).continuous

instance instIsCancelSMulSphere : IsCancelSMul G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  right_cancel' a b c h := by
    have h1 : (b⁻¹ * a) • c = c := by
      calc (b⁻¹ * a) • c = b⁻¹ • (a • c) := mul_smul b⁻¹ a c
        _ = b⁻¹ • (b • c) := by rw [h]
        _ = c := inv_smul_smul b c
    have h2 : b⁻¹ * a = 1 := G.free (b⁻¹ * a) c h1
    calc a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
      _ = b * 1 := by rw [h2]
      _ = b := mul_one b

def orbitSetoid : Setoid (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  MulAction.orbitRel G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

abbrev Orbit := Quotient G.orbitSetoid

def projection : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → G.Orbit :=
  Quotient.mk G.orbitSetoid

theorem projection_eq_iff (x y : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    G.projection x = G.projection y ↔
      ∃ γ : G.group, Geometry.sphereDiffeo (n := 3) γ.val x = y := by
  rw [show G.projection x = G.projection y ↔
      (MulAction.orbitRel G.group (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) x y from
    Quotient.eq,
    MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨γ, hγ⟩ := h
    refine ⟨γ⁻¹, ?_⟩
    change (γ⁻¹ : G.group) • x = y
    rw [← hγ, inv_smul_smul]
  · obtain ⟨γ, hγ⟩ := h
    have hγ' : γ • x = y := hγ
    refine ⟨γ⁻¹, ?_⟩
    rw [← hγ', inv_smul_smul]

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
