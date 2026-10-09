import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionPortShrink

/-!
# Consumer of the port shrink: a protected neighbourhood of the new zero level

`DecompositionCertificate.exists_shrinkPorts_protectedNhds`: for a recorded shrink `E.shrink δ` of the
ports, an OPEN neighbourhood `V` of the new zero level `Z_R` of the circle region that is disjoint from
every shrunk external collar target — the set inside which the two-sided collars of the rounded
boundary tori (packet T3) are chosen. Its boundary image is unchanged (`BoundaryTori.shrink_image`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **Protected neighbourhood of `Z_R`.** -/
theorem exists_shrinkPorts_protectedNhds (D : DecompositionCertificate W E) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (V : Set W.Carrier), IsOpen V ∧
      (D.shrinkPorts hδ hδ1).circ.roundedLevel ⊆ V ∧
      (∀ i, Disjoint V ((E.shrink hδ hδ1).collar i).target) ∧
      (E.shrink hδ hδ1).image = E.image := by
  obtain ⟨δ, hδ, hδ1, hbuf⟩ := D.exists_shrinkPorts_buffer
  refine ⟨δ, hδ, hδ1, (⋃ i, closure ((E.shrink hδ hδ1).collar i).target)ᶜ,
    (isClosed_iUnion_of_finite fun i => isClosed_closure).isOpen_compl, ?_, ?_,
    BoundaryTori.shrink_image E hδ hδ1⟩
  · intro x hx hxU
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    exact (hbuf i).le_bot ⟨hi, hx⟩
  · intro i
    rw [Set.disjoint_left]
    intro x hxV hxT
    exact hxV (mem_iUnion.mpr ⟨i, subset_closure hxT⟩)

end DecompositionCertificate

end GC.GraphManifold.Assembly
