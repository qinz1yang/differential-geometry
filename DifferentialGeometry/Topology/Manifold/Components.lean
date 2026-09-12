import DifferentialGeometry.Topology.Manifold.ClosedOriented
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u

variable {n : ℕ} (M : ClosedOrientedManifold.{u} n)

def componentSet (C : ConnectedComponents M.Carrier) : Set M.Carrier :=
  {x | ConnectedComponents.mk x = C}

@[simp]
theorem mem_componentSet (C : ConnectedComponents M.Carrier) (x : M.Carrier) :
    x ∈ componentSet M C ↔ ConnectedComponents.mk x = C := Iff.rfl

@[simp]
theorem componentSet_mk (x : M.Carrier) :
    componentSet M (ConnectedComponents.mk x) = connectedComponent x := by
  ext y
  exact ConnectedComponents.coe_eq_coe'

theorem componentSet_nonempty (C : ConnectedComponents M.Carrier) :
    (componentSet M C).Nonempty :=
  ConnectedComponents.surjective_coe C

theorem isOpen_componentSet (C : ConnectedComponents M.Carrier) :
    IsOpen (componentSet M C) := by
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M.Carrier
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isOpen_connectedComponent

theorem isClosed_componentSet (C : ConnectedComponents M.Carrier) :
    IsClosed (componentSet M C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isClosed_connectedComponent

theorem isCompact_componentSet (C : ConnectedComponents M.Carrier) :
    IsCompact (componentSet M C) :=
  (isClosed_componentSet M C).isCompact

theorem isConnected_componentSet (C : ConnectedComponents M.Carrier) :
    IsConnected (componentSet M C) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [componentSet_mk]
  exact isConnected_connectedComponent

theorem finite_components : Finite (ConnectedComponents M.Carrier) := by
  let := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M.Carrier
  infer_instance

theorem isEmpty_components_iff :
    IsEmpty (ConnectedComponents M.Carrier) ↔ IsEmpty M.Carrier :=
  ConnectedComponents.isEmpty_iff_isEmpty

def componentOpen (C : ConnectedComponents M.Carrier) : Opens M.Carrier :=
  ⟨componentSet M C, isOpen_componentSet M C⟩

@[simp]
theorem componentOpen_coe (C : ConnectedComponents M.Carrier) :
    (componentOpen M C : Set M.Carrier) = componentSet M C := rfl

def componentInclusion (C : ConnectedComponents M.Carrier) : componentOpen M C → M.Carrier :=
  Subtype.val

theorem componentInclusion_contMDiff (C : ConnectedComponents M.Carrier) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (componentInclusion M C) :=
  contMDiff_subtype_val

theorem componentInclusion_mfderiv_bijective (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    Function.Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x) := by
  change Function.Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Subtype.val : componentOpen M C → M.Carrier) x)
  rw [mfderiv_subtype_val]
  exact Function.bijective_id

def componentInclusionTangentEquiv (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C x) :=
  LinearEquiv.ofBijective
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x).toLinearMap
    (componentInclusion_mfderiv_bijective M C x)

@[simp]
theorem componentInclusionTangentEquiv_apply (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    componentInclusionTangentEquiv M C x v =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentInclusion M C) x v := rfl

def componentTangentOrientation (C : ConnectedComponents M.Carrier) (x : componentOpen M C) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) (Fin n) :=
  Orientation.map (Fin n) (componentInclusionTangentEquiv M C x).symm
    (M.orientation.orientation (componentInclusion M C x))

theorem componentInclusionTangentEquiv_eq_refl (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    componentInclusionTangentEquiv M C x =
      LinearEquiv.refl ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := by
  refine LinearEquiv.ext fun v => ?_
  rw [componentInclusionTangentEquiv_apply]
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (Subtype.val : componentOpen M C → M.Carrier) x v = v
  rw [DifferentialGeometry.mfderiv_subtype_val]
  rfl

@[simp]
theorem componentTangentOrientation_apply (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    componentTangentOrientation M C x = M.orientation.orientation x.1 := by
  rw [componentTangentOrientation]
  erw [componentInclusionTangentEquiv_eq_refl M C x, LinearEquiv.refl_symm,
    Orientation.map_refl]
  rfl

theorem componentTangentOrientation_locally_constant (C : ConnectedComponents M.Carrier) :
    ∀ p x : componentOpen M C,
    ∀ hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet,
    ∃ U : Set (componentOpen M C), IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) p).baseSet,
      ∀ y : componentOpen M C, ∀ hy : y ∈ U,
        Orientation.map (Fin n)
          (tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) p y (hU hy))
          (componentTangentOrientation M C y) =
        Orientation.map (Fin n)
          (tangentChartEquiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) p x hx)
          (componentTangentOrientation M C x) := by
  simpa only [ManifoldOrientation.restrictOpen_orientation, componentTangentOrientation_apply M C]
    using (M.orientation.restrictOpen (componentOpen M C)).locally_constant

def componentOrientation (C : ConnectedComponents M.Carrier) :
    ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (componentOpen M C) n where
  dimension_eq := M.orientation.dimension_eq
  orientation := componentTangentOrientation M C
  locally_constant := componentTangentOrientation_locally_constant M C

theorem componentInclusion_preservesOrientation (C : ConnectedComponents M.Carrier)
    (x : componentOpen M C) :
    Orientation.map (Fin n) (componentInclusionTangentEquiv M C x)
      ((componentOrientation M C).orientation x) =
        M.orientation.orientation (componentInclusion M C x) :=
  (Orientation.map (Fin n) (componentInclusionTangentEquiv M C x)).apply_symm_apply _

def component (C : ConnectedComponents M.Carrier) : ConnectedClosedOrientedManifold.{u} n where
  Carrier := componentOpen M C
  compact := isCompact_iff_compactSpace.mp (isCompact_componentSet M C)
  orientation := componentOrientation M C
  connected := isConnected_iff_connectedSpace.mp (isConnected_componentSet M C)

@[simp]
theorem component_carrier (C : ConnectedComponents M.Carrier) :
    (component M C).Carrier = {x : M.Carrier // ConnectedComponents.mk x = C} := rfl

@[simp]
theorem component_orientation (C : ConnectedComponents M.Carrier) :
    (component M C).orientation = componentOrientation M C := rfl

end DifferentialGeometry.Topology.ClosedOrientedManifold
