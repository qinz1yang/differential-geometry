import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecPorts

/-!
# Consumers of packet S1 (lane ASM-SPH)

* `SphereCutCapped.exists_componentPorts`: every capped component of a sphere cut carries ports
  exhausting its boundary, each of which is, on the whole collar, the core image of an old torus
  collar of the cut carrier lying over an external port of `W` — the port input of the inherited
  certificate (B4, third branch).
* `SphereCutCapped.sum_card_componentPorts`: the ports of all components together are the `n`
  external ports of `W`.
* `CircleRegion.isClopen_label_base`: the base of one label is open and closed in the projected
  set (the restriction of the circle region's base to a component).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E) (DQ : X.Q.Components)

/-- **Ports of a capped component.** -/
theorem exists_componentPorts (i : Fin DQ.count) :
    ∃ (m : ℕ) (E' : BoundaryTori (GC.Topology.componentCarrier X.Q DQ i) m),
      (GC.Topology.componentCarrier X.Q DQ i).model.boundary
          (GC.Topology.componentCarrier X.Q DQ i).Carrier = E'.image ∧
      ∀ a, ∃ a' : Fin X.B.torusCount, ∀ p ∈ halfCollarSource,
        (E'.collar a p).val = X.capping.core (X.B.tori.collar a' p) ∧
          X.fold (X.B.tori.collar a' p) = E.collar (Fin.cast X.hn a') p := by
  refine ⟨_, X.componentTori DQ i, X.componentTori_boundary DQ i, fun a => ?_⟩
  refine ⟨(PortRestriction.componentPortEquiv X.capping.retained DQ i a).1, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := X.componentTori_collar DQ i a hp
  exact ⟨h1.trans h2, X.componentTori_fold DQ i a hp⟩

/-- The ports of all capped components are the external ports of `W`. -/
theorem sum_card_componentPorts :
    ∑ i, Fintype.card (PortRestriction.ComponentPorts X.capping.retained DQ i) = n :=
  (PortRestriction.sum_card_componentPorts X.capping.retained DQ).trans X.hn

end SphereCutCapped

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W) {ι : Type*} [TopologicalSpace ι]
  [DiscreteTopology ι] {O : Set R.domain} {lab : R.domain → ι}

/-- **The base of one label is clopen in the projected set.** -/
theorem isClopen_label_base (hO : IsOpen O) (hsat : ∀ x y, R.proj x = R.proj y → x ∈ O → y ∈ O)
    (hlab : ContinuousOn lab O) (i : ι) :
    IsClopen ((Subtype.val : R.proj '' O → R.Base) ⁻¹' (R.proj '' (O ∩ lab ⁻¹' {i}))) := by
  have hopen : ∀ j, IsOpen ((Subtype.val : R.proj '' O → R.Base) ⁻¹'
      (R.proj '' (O ∩ lab ⁻¹' {j}))) := fun j =>
    (R.isOpen_proj_image_label hO hlab j).preimage continuous_subtype_val
  refine ⟨?_, hopen i⟩
  have hcompl : ((Subtype.val : R.proj '' O → R.Base) ⁻¹' (R.proj '' (O ∩ lab ⁻¹' {i})))ᶜ =
      ⋃ (j : ι) (_ : j ≠ i), (Subtype.val : R.proj '' O → R.Base) ⁻¹'
        (R.proj '' (O ∩ lab ⁻¹' {j})) := by
    ext ⟨b, hb⟩
    simp only [mem_compl_iff, mem_preimage, mem_iUnion, exists_prop]
    constructor
    · intro hni
      rw [← R.iUnion_proj_image_label (lab := lab)] at hb
      obtain ⟨j, hj⟩ := mem_iUnion.mp hb
      exact ⟨j, fun hji => hni (hji ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hi
      exact Set.disjoint_left.mp (R.disjoint_proj_image_label hsat hlab hji) hj hi
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j

end CircleRegion

end GC.GraphManifold.Assembly
