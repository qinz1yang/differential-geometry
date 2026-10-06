import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdgeModels74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdgeCross74

/-!
# Draft 74, D74-6: the edge component models transported between carriers of ANY kinds

Lane O-CROSS, G3. Same construction as `EdgeComponentModels.mapCarrier74` (lane C14-REG-CHAIN,
G20) over `EdgeBundle.mapCarrierCross74`: **`EdgeComponentModels.mapCarrierCross74 e M`**,
`EdgeComponentModels.mapCarrierCross74_circleTriv`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsEdges_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **The edge component models transported along `e`** (carriers of ANY kinds). -/
def EdgeComponentModels.mapCarrierCross74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {P : EdgeBundle W₀} (M : EdgeComponentModels P) :
    EdgeComponentModels (P.mapCarrierCross74 e) where
  intervalCount := M.intervalCount
  circleCount := M.circleCount
  componentEquiv := M.componentEquiv
  intervalBase := M.intervalBase
  intervalBase_embedding := M.intervalBase_embedding
  intervalBase_range := M.intervalBase_range
  circleBase := M.circleBase
  circleBase_embedding := M.circleBase_embedding
  circleBase_range := M.circleBase_range
  endpointEquiv := M.endpointEquiv
  endpointEquiv_apply := M.endpointEquiv_apply
  intervalTriv i := (M.intervalTriv i).mapCarrier74 e
  intervalTriv_range i := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y ∈ (M.componentEquiv (.inl i)).1 ∧ P.height y ≤ P.level)
    change range (e ∘ (M.intervalTriv i).map) = Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) ∈ (M.componentEquiv (.inl i)).1 ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, M.intervalTriv_range i]
    rfl
  intervalTriv_proj i w t := by
    obtain ⟨hx0, hp⟩ := M.intervalTriv_proj i w t
    refine ⟨mem_image_of_mem e hx0, ?_⟩
    change P.proj (e.restrictOpens74 P.source ⟨e ((M.intervalTriv i).map (w, t)), _⟩) = _
    convert hp using 2
    exact Subtype.ext (e.symm_apply_apply _)
  intervalTriv_disk i t := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y = M.intervalBase i t ∧ P.height y ≤ P.level)
    change range (e ∘ fun w => (M.intervalTriv i).map (w, t)) =
      Subtype.val '' {x : e.imageOpens74 P.source |
        P.proj (e.restrictOpens74 P.source x) = M.intervalBase i t ∧
          P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, M.intervalTriv_disk i t]
    rfl
  intervalTriv_rim i t := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y = M.intervalBase i t ∧ P.height y = P.level)
    change (e ∘ fun w => (M.intervalTriv i).map (w, t)) '' diskRim =
      Subtype.val '' {x : e.imageOpens74 P.source |
        P.proj (e.restrictOpens74 P.source x) = M.intervalBase i t ∧
          P.height (e.restrictOpens74 P.source x) = P.level}
    rw [h, image_comp, M.intervalTriv_rim i t]
    rfl
  circleTriv j := e ∘ M.circleTriv j
  circleTriv_smooth j := e.contMDiff.comp (M.circleTriv_smooth j)
  circleTriv_mfderiv j p := by
    have hd := (M.circleTriv_smooth j p).mdifferentiableAt (by simp)
    have he : MDifferentiableAt W₀.model W₁.model e (M.circleTriv j p) :=
      e.mdifferentiable (by simp) _
    rw [mfderiv_comp p he hd]
    exact (mfderiv_diffeo_bijective_R74 e _).comp (M.circleTriv_mfderiv j p)
  circleTriv_injective j := e.injective.comp (M.circleTriv_injective j)
  circleTriv_range j := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y ∈ (M.componentEquiv (.inr j)).1 ∧ P.height y ≤ P.level)
    change range (e ∘ M.circleTriv j) = Subtype.val '' {x : e.imageOpens74 P.source |
      P.proj (e.restrictOpens74 P.source x) ∈ (M.componentEquiv (.inr j)).1 ∧
        P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, M.circleTriv_range j]
    rfl
  circleTriv_proj j w z := by
    obtain ⟨hx0, hp⟩ := M.circleTriv_proj j w z
    refine ⟨mem_image_of_mem e hx0, ?_⟩
    change P.proj (e.restrictOpens74 P.source ⟨e (M.circleTriv j (w, z)), _⟩) = _
    convert hp using 2
    exact Subtype.ext (e.symm_apply_apply _)
  circleTriv_disk j z := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y = M.circleBase j z ∧ P.height y ≤ P.level)
    change range (e ∘ fun w => M.circleTriv j (w, z)) =
      Subtype.val '' {x : e.imageOpens74 P.source |
        P.proj (e.restrictOpens74 P.source x) = M.circleBase j z ∧
          P.height (e.restrictOpens74 P.source x) ≤ P.level}
    rw [h, range_comp, M.circleTriv_disk j z]
    rfl
  circleTriv_rim j z := by
    have h := e.image_restrictOpens74 P.source
      (fun y => P.proj y = M.circleBase j z ∧ P.height y = P.level)
    change (e ∘ fun w => M.circleTriv j (w, z)) '' diskRim =
      Subtype.val '' {x : e.imageOpens74 P.source |
        P.proj (e.restrictOpens74 P.source x) = M.circleBase j z ∧
          P.height (e.restrictOpens74 P.source x) = P.level}
    rw [h, image_comp, M.circleTriv_rim j z]
    rfl

/-- The transported edge-circle pieces are `e ∘ circleTriv j` and keep the counts. -/
theorem EdgeComponentModels.mapCarrierCross74_circleTriv
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) {P : EdgeBundle W₀}
    (M : EdgeComponentModels P) (j : Fin M.circleCount) :
    (M.mapCarrierCross74 e).circleTriv j = e ∘ M.circleTriv j ∧
      (M.mapCarrierCross74 e).intervalCount = M.intervalCount ∧
      (M.mapCarrierCross74 e).circleCount = M.circleCount :=
  ⟨rfl, rfl, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
