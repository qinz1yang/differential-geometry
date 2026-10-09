import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74

/-!
# Draft 74, D74-6: transport of the boundary tori (the target ports are the transported ports)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G21. D74-6: "never an arbitrary target `E₁`" — the
boundary tori of the target carrier are the TRANSPORTED ports:

* `BoundaryTori.transport74 e E`: collars `(E.collar i).trans e` (same source; the boundary point
  property is carried by `e`, `IsLocalDiffeomorphAt.isBoundaryPoint_iff`; targets stay disjoint);
* `BoundaryTori.transport74_torusMap` (`torusMap = e ∘ torusMap`),
  `BoundaryTori.transport74_image` (`image = e(image)`),
  `BoundaryTori.transport74_target` (collar targets are the images),
  `BoundaryTori.transport74_ports` (if `∂W₀ = E.image` then `∂W₁ = (E.transport74 e).image`, the
  cusp-core `ports` field; `∂` carried by `Diffeomorph.image_boundary`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- **The boundary tori transported along a carrier diffeomorphism.** -/
def BoundaryTori.transport74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (E : BoundaryTori W₀ n) : BoundaryTori W₁ n where
  collar i := (E.collar i).trans e.toPartialDiffeomorph
  source_eq i := by
    rw [← E.source_eq i]
    change (E.collar i).source ∩ (E.collar i) ⁻¹' univ = (E.collar i).source
    rw [preimage_univ, inter_univ]
  boundary_zero i t :=
    ((e.isLocalDiffeomorph (E.collar i (t, halfZero))).isBoundaryPoint_iff (by simp)).mp
      (E.boundary_zero i t)
  disjoint i j hij := by
    change Disjoint (univ ∩ e.symm ⁻¹' (E.collar i).target)
      (univ ∩ e.symm ⁻¹' (E.collar j).target)
    rw [univ_inter, univ_inter]
    exact (E.disjoint hij).preimage _

/-- The transported torus maps are `e ∘ torusMap`. -/
theorem BoundaryTori.transport74_torusMap (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (E : BoundaryTori W₀ n) (i : Fin n) : (E.transport74 e).torusMap i = e ∘ E.torusMap i :=
  rfl

/-- The transported boundary image is the image of the boundary image. -/
theorem BoundaryTori.transport74_image (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (E : BoundaryTori W₀ n) : (E.transport74 e).image = e '' E.image := by
  rw [BoundaryTori.image, BoundaryTori.image, image_iUnion]
  exact iUnion_congr fun i => range_comp e (E.torusMap i)

/-- The transported collar targets are the images of the collar targets. -/
theorem BoundaryTori.transport74_target (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (E : BoundaryTori W₀ n) (i : Fin n) :
    ((E.transport74 e).collar i).target = e '' (E.collar i).target := by
  change univ ∩ e.symm ⁻¹' (E.collar i).target = _
  rw [univ_inter]
  exact (e.toEquiv.image_eq_preimage_symm _).symm

/-- **The ports of the target are the transported ports**: `∂W₀ = E.image` gives
`∂W₁ = (E.transport74 e).image`. -/
theorem BoundaryTori.transport74_ports (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (E : BoundaryTori W₀ n) (h : W₀.model.boundary W₀.Carrier = E.image) :
    W₁.model.boundary W₁.Carrier = (E.transport74 e).image := by
  rw [E.transport74_image, ← h, e.image_boundary (by simp)]

end GC.GraphManifold
