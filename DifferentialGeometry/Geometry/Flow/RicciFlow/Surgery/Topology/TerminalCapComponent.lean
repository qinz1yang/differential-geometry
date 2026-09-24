import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapSide
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCoreGeometry
import DifferentialGeometry.Topology.Embedding.CompactFrontier

noncomputable section

section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_protected_anchor_outside_of_scalar_gt
    (U : Set (H.event i).incoming.terminalRegularOpen)
    (hscalar : ∀ y ∈ U,
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
        metricScalarAt (H.event i).terminal.metric y)
    (z : (H.event i).transition.trace.tubes.core)
    (hz : z ∈ (H.event i).transition.trace.retainedCore) :
    ∃ y : (H.event i).incoming.terminalRegularOpen,
      ∃ hy : y.val ∈ (H.event i).transition.trace.tubes.core,
        ConnectedComponents.mk (⟨y.val, hy⟩ : (H.event i).transition.trace.tubes.core) =
          ConnectedComponents.mk z ∧
        metricScalarAt (H.event i).terminal.metric y ≤
          ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ ∧
        y.val ∉ (Subtype.val : (H.event i).incoming.terminalRegularOpen →
          (H.stage i.castSucc).Carrier) '' U := by
  obtain ⟨y, hy, hcomponent, hlow⟩ := G.retained_meets_protected
    (ConnectedComponents.mk z) ⟨z, rfl, hz⟩
  refine ⟨y, hy, hcomponent, hlow, ?_⟩
  rintro ⟨w, hw, heq⟩
  have hwy : w = y := Subtype.ext heq
  exact (hscalar y (hwy ▸ hw)).not_ge hlow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem exists_capCore_in_cutCore_of_terminal_cap_boundary_capture
    {U : Set E.incoming.terminalRegularOpen} (cap : CapCore U)
    (j : E.transition.trace.tubes.Index)
    (hinside : ∀ side : Bool, range (E.transition.trace.tubes.boundarySphere (j, side)) ⊆
      (Subtype.val : E.incoming.terminalRegularOpen → P.Carrier) '' interior U) :
    ∃ (b : E.transition.trace.tubes.Boundary) (K : Set P.Carrier), Nonempty (CapCore K) ∧
      K ⊆ (Subtype.val : E.incoming.terminalRegularOpen → P.Carrier) '' interior U ∧
      frontier K = range (E.transition.trace.tubes.boundarySphere b) ∧
      K ⊆ E.transition.trace.tubes.core := by
  have hsmooth : ∀ b : E.transition.trace.tubes.Boundary, IsSmoothEmbedding I2 I3 ∞
      (E.transition.trace.tubes.boundarySphere b) :=
    fun b => E.transition.trace.tubes.isSmoothEmbedding_boundarySphere
      b (E.transition.tube_smooth b.1)
  have hinterior := DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding
    E.incoming.terminalRegularOpen.isOpenEmbedding' U
  obtain ⟨b, K, hK, hKU, hfront, hcore⟩ :=
    E.transition.trace.tubes.exists_capCore_in_cutCore_of_captured_boundary_spheres j
      cap.nonempty_image_open.some hsmooth
      (fun side => hinterior ▸ hinside side)
  exact ⟨b, K, hK, hinterior.symm ▸ hKU, hfront, hcore⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

include G in
theorem exists_discarded_capCore_component_of_terminal_cap_boundary_capture
    {U : Set (H.event i).incoming.terminalRegularOpen} (cap : CapCore U)
    (hscalar : ∀ y ∈ interior U,
      ((parameters.protectedRadius (H.time i.succ)) ^ 2)⁻¹ <
        metricScalarAt (H.event i).terminal.metric y)
    (j : (H.event i).transition.trace.tubes.Index)
    (hinside : ∀ side : Bool, range ((H.event i).transition.trace.tubes.boundarySphere (j, side)) ⊆
      (Subtype.val : (H.event i).incoming.terminalRegularOpen → (H.stage i.castSucc).Carrier) ''
        interior U) :
    ∃ (b : (H.event i).transition.trace.tubes.Boundary) (K : Set (H.stage i.castSucc).Carrier), Nonempty (CapCore K) ∧
      K ⊆ (Subtype.val : (H.event i).incoming.terminalRegularOpen → (H.stage i.castSucc).Carrier) ''
        interior U ∧
      frontier K = range ((H.event i).transition.trace.tubes.boundarySphere b) ∧
      K ⊆ (H.event i).transition.trace.tubes.core ∧
      (∀ z : (H.event i).transition.trace.tubes.core, z.val ∈ K →
        connectedComponent z = (Subtype.val : (H.event i).transition.trace.tubes.core →
          (H.stage i.castSucc).Carrier) ⁻¹' K) ∧
      ∀ z : (H.event i).transition.trace.tubes.core, z.val ∈ K →
        z ∉ (H.event i).transition.trace.retainedCore := by
  obtain ⟨b, K, hK, hKU, hfront, hcore⟩ :=
    (H.event i).exists_capCore_in_cutCore_of_terminal_cap_boundary_capture cap j hinside
  have hcomponent (z : (H.event i).transition.trace.tubes.core) (hz : z.val ∈ K) :
      connectedComponent z = (Subtype.val : (H.event i).transition.trace.tubes.core →
        (H.stage i.castSucc).Carrier) ⁻¹' K :=
    (H.event i).transition.trace.tubes.connectedComponent_eq_preimage_of_capCore_of_boundarySphere
      hK.some hcore b hfront ((H.event i).transition.tube_smooth b.1) z hz
  refine ⟨b, K, hK, hKU, hfront, hcore, hcomponent, ?_⟩
  intro z hz hretained
  obtain ⟨y, hy, heq, _, hyout⟩ := G.exists_protected_anchor_outside_of_scalar_gt (interior U) hscalar z hretained
  have hyz : (⟨y.val, hy⟩ : (H.event i).transition.trace.tubes.core) ∈ connectedComponent z :=
    ConnectedComponents.coe_eq_coe'.mp heq
  have hyK : y.val ∈ K := by
    change (⟨y.val, hy⟩ : (H.event i).transition.trace.tubes.core) ∈
      (Subtype.val : (H.event i).transition.trace.tubes.core → (H.stage i.castSucc).Carrier) ⁻¹' K
    rw [← hcomponent z hz]
    exact hyz
  exact hyout (hKU hyK)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

end
