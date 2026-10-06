import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportRows74

/-!
# Draft 74, D74-6: the closed route has no ports (cusp cores of an empty boundary)

Lane C14-REG-CHAIN (by S-REG-CHAIN), G26. On the closed route `n = 0` and the target boundary
tori are `BoundaryTori.empty W`; D74-6 forbids reading `∂W = ∅` off `BoundaryTori.empty W`, so the
`cusp.ports` field is supplied by the boundary of the carrier itself:

* **`CuspCores.ofBoundaryEmpty74 h`**: for `h : ∂W = ∅` (the model boundary of the carrier; from
  `ClosedMemberFacts.boundary_empty` or the boundary transport of `M.ψ`), the cusp cores of the
  empty port family — the closed-route `cusp` field of `FC39RowsV2` (all component fields are
  indexed by `Fin 0`).
* **`BoundaryTori.transport74_empty`**: the transported empty port family is the empty port
  family of the target carrier (`n = 0`);
* **`FC39RowsV2.transportEmpty74`**: the record transport of G24 for closed-route rows lands in
  `FC39RowsV2 W₁ (BoundaryTori.empty W₁)` (the only port family the strong-certificate consumer
  of the closed route uses).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W₀ W₁ : CompactCarrier.{u}}

/-- **The cusp cores of a carrier with empty model boundary** (closed route, `n = 0`): no cusp
core, and `ports : ∂W = ∅` is the hypothesis `h`. -/
def CuspCores.ofBoundaryEmpty74 {W : CompactCarrier.{u}}
    (h : W.model.boundary W.Carrier = ∅) : CuspCores W (BoundaryTori.empty W) where
  ports := by rw [h, BoundaryTori.empty_image]
  piece b := b.elim0
  product b := b.elim0
  external_end b := b.elim0
  collar_owned b := b.elim0
  collar_closure_off b := b.elim0
  disjoint b := b.elim0
  cuspFn b := b.elim0
  near b := b.elim0
  near_interior b := b.elim0
  fn_smooth b := b.elim0
  fn_regular b := b.elim0
  internal_eq b := b.elim0
  near_eq b := b.elim0
  internalModelFace b := b.elim0
  internalModelFace_eq b := b.elim0
  externalModelFace b := b.elim0
  externalModelFace_eq b := b.elim0
  modelFace_cases b := b.elim0

/-- The transported empty port family is the empty port family of the target. -/
theorem _root_.GC.GraphManifold.BoundaryTori.transport74_empty
    (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) :
    (BoundaryTori.empty W₀).transport74 e = BoundaryTori.empty W₁ := by
  have h : ∀ a b : Fin 0 → PartialDiffeomorph halfCollarModel W₁.model
      (Torus × EuclideanHalfSpace 1) W₁.Carrier ∞, a = b := fun a b => funext fun i => i.elim0
  unfold BoundaryTori.transport74 BoundaryTori.empty
  congr 1
  exact h _ _

/-- **Closed-route record transport**: rows on a carrier with the empty port family go to rows on
the target carrier with ITS empty port family. -/
def FC39RowsV2.transportEmpty74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) (Rw : FC39RowsV2 W₀ (BoundaryTori.empty W₀)) :
    FC39RowsV2 W₁ (BoundaryTori.empty W₁) :=
  (BoundaryTori.transport74_empty e) ▸ Rw.transport74 e hk

/-- Changing the (equal) port family does not change the port-independent fields. -/
theorem FC39RowsV2.cast_ports_fields {E₁ E₂ : BoundaryTori W₁ 0} (h : E₁ = E₂)
    (R : FC39RowsV2 W₁ E₁) :
    (h ▸ R).zero = R.zero ∧ (h ▸ R).edge = R.edge ∧ (h ▸ R).circle = R.circle := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- The closed-route transport keeps the zero domains, the edge bundle and the circle bundle of
`FC39RowsV2.transport74`. -/
theorem FC39RowsV2.transportEmpty74_fields (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) (Rw : FC39RowsV2 W₀ (BoundaryTori.empty W₀)) :
    (Rw.transportEmpty74 e hk).zero = Rw.zero.mapCarrier74 e ∧
      (Rw.transportEmpty74 e hk).edge = Rw.edge.mapCarrier74 e hk ∧
      (Rw.transportEmpty74 e hk).circle = Rw.circle.mapCarrier74 e :=
  FC39RowsV2.cast_ports_fields (BoundaryTori.transport74_empty e) (Rw.transport74 e hk)

end GC.GraphManifold.Assembly.FC39P0
