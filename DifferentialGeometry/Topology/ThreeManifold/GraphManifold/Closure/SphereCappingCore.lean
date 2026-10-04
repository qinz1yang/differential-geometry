import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RelativeCaps

/-!
Removing the actual open cap balls recovers the same cut core as a whole homeomorphism.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RelativeSphereCapping

local instance sphereCappingCoreBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

variable {C Q : CompactCarrier.{u}} {B : MixedBoundaryCertificate C}
  (K : RelativeSphereCapping C Q B)

def capInteriorImage : Set Q.Carrier :=
  ⋃ i, K.cap i '' {x : ClosedCell 3 | ‖x.val‖ < 1}

theorem core_range_eq_capInteriorImage_compl :
    range K.core = K.capInteriorImageᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ hy
    obtain ⟨i, a, ha, he⟩ := mem_iUnion.mp hy
    have hi : K.core x ∈ range K.core ∩ range (K.cap i) :=
      ⟨⟨x, rfl⟩, ⟨a, he⟩⟩
    rw [K.core_cap_intersection i] at hi
    obtain ⟨z, hz⟩ := hi
    let w := (K.attaching i).symm z
    have hw : K.cap i (closureSphereToBall w) = K.core x := by
      rw [K.boundary_eq]
      simpa only [w, Diffeomorph.apply_symm_apply] using hz
    have hae : a = closureSphereToBall w :=
      (K.cap_embedding i).isEmbedding.injective (he.trans hw.symm)
    have hn : ‖(closureSphereToBall w).val‖ = 1 := by
      simpa only [closureSphereToBall, sphereToClosedCell, Metric.mem_sphere,
        dist_zero_right] using w.down.property
    exact (not_lt_of_ge hn.ge) (hae ▸ ha)
  · intro hy
    rcases K.every_point y with hcore | ⟨i, a, rfl⟩
    · exact hcore
    · have hn : ¬‖a.val‖ < 1 := by
        intro ha
        exact hy (mem_iUnion.mpr ⟨i, a, ha, rfl⟩)
      have he : ‖a.val‖ = 1 := le_antisymm a.property (not_lt.mp hn)
      let z : ClosureSphere.{u} := ULift.up ⟨a.val, by simpa using he⟩
      have hz : closureSphereToBall z = a := Subtype.ext rfl
      refine ⟨B.sphere i (K.attaching i z, halfZero), ?_⟩
      rw [← K.boundary_eq, hz]

def corePunctureHomeomorph : C.Carrier ≃ₜ ↥K.capInteriorImageᶜ :=
  K.core_embedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr K.core_range_eq_capInteriorImage_compl)

theorem corePunctureHomeomorph_apply (x : C.Carrier) :
    (K.corePunctureHomeomorph x).val = K.core x := rfl

end GC.GraphManifold.RelativeSphereCapping
