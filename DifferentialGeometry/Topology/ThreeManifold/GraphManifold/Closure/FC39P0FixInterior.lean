import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions

/-!
# FC39 producer, gate 1 (review 49, level-3 interface): `M₁`, `M₂`, `M₃` lie in the interior

External review 49 asks for derived interfaces, stated as CONCLUSIONS of the existing contract
fields (no new field, no new hypothesis). Here: the regions `M₁ = W \ int_W (Z ∪ C)`,
`M₂ = M₁ \ int_{M₁} S` and `M₃ = M₂ \ int_{M₂} P` of `FC39P0Junctions.lean` lie in the ambient
interior `W.interior`.

* `regionM1_subset_interior` — from `CuspCores.ports` (the model boundary of `W` is the union of
  the port tori) and `CuspCores.collar_owned` (the open port collar lies in the cusp core): every
  boundary point of `W` is an interior point of `⋃ Z ∪ ⋃ C`, hence not in `M₁`;
* `regionM2_subset_interior`, `regionM3_subset_interior` — `M₃ ⊆ M₂ ⊆ M₁`;
* `isClosed_regionM2` and the consumer `JunctionsV2.boundaryM2_subset_interior`: `∂M₂` (the union
  of the residual faces, `JunctionsV2.frontier_M2`) lies in the interior.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- A point that is not a model boundary point of `W` lies in the ambient interior. -/
theorem mem_interior_of_not_mem_boundary_FIX2 {x : W.Carrier}
    (hx : x ∉ W.model.boundary W.Carrier) : x ∈ (W.interior : Set W.Carrier) := by
  change W.model.IsInteriorPoint x
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  exact hx

/-- The port torus `b` lies in the interior of the union of the zero and cusp-core images: the
open port collar is a neighbourhood inside the cusp core `b`. -/
theorem torusMap_mem_interior_zeroCusp (Z : ZeroDomains W) (C : CuspCores W E) (b : Fin n)
    (t : Torus) :
    E.torusMap b t ∈ interior ((⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map) := by
  have hsrc : (t, halfZero) ∈ (E.collar b).source := by
    rw [E.source_eq b]
    change (0 : ℝ) < 1
    norm_num
  have hsub : (E.collar b).target ⊆
      (⋃ i, range (Z.piece i).map) ∪ ⋃ b, range (C.piece b).map :=
    (C.collar_owned b).trans ((subset_iUnion (fun b => range (C.piece b).map) b).trans
      subset_union_right)
  exact interior_maximal hsub (E.collar b).open_target ((E.collar b).map_source hsrc)

/-- **`M₁` lies in the ambient interior** (derived from `CuspCores.ports` and `collar_owned`). -/
theorem regionM1_subset_interior (Z : ZeroDomains W) (C : CuspCores W E) :
    regionM1 Z C ⊆ (W.interior : Set W.Carrier) := by
  intro x hx
  by_contra hxi
  have hb : x ∈ W.model.boundary W.Carrier := by
    by_contra hb
    exact hxi (mem_interior_of_not_mem_boundary_FIX2 hb)
  rw [C.ports] at hb
  obtain ⟨b, t, rfl⟩ := mem_iUnion.1 hb
  exact hx (torusMap_mem_interior_zeroCusp Z C b t)

/-- `M₂ ⊆ M₁`. -/
theorem regionM2_subset_regionM1 {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) : regionM2 S ⊆ regionM1 Z C :=
  sdiff_subset

/-- `M₃ ⊆ M₂`. -/
theorem regionM3_subset_regionM2 {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) (P : EdgeBundle W) : regionM3 S P ⊆ regionM2 S :=
  sdiff_subset

/-- **`M₂` lies in the ambient interior.** -/
theorem regionM2_subset_interior {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) : regionM2 S ⊆ (W.interior : Set W.Carrier) :=
  (regionM2_subset_regionM1 S).trans (regionM1_subset_interior Z C)

/-- **`M₃` lies in the ambient interior.** -/
theorem regionM3_subset_interior {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) (P : EdgeBundle W) : regionM3 S P ⊆ (W.interior : Set W.Carrier) :=
  (regionM3_subset_regionM2 S P).trans (regionM2_subset_interior S)

/-- `M₁` is closed. -/
theorem isClosed_regionM1 (Z : ZeroDomains W) (C : CuspCores W E) : IsClosed (regionM1 Z C) :=
  isOpen_interior.isClosed_compl

/-- `M₂` is closed: the complement in the closed set `M₁` of a relatively open set. -/
theorem isClosed_regionM2 {Z : ZeroDomains W} {C : CuspCores W E} (S : SlimPiecesV2 W Z C) :
    IsClosed (regionM2 S) := by
  have h : regionM2 S = (Subtype.val : regionM1 Z C → W.Carrier) ''
      (interior ((Subtype.val : regionM1 Z C → W.Carrier) ⁻¹' S.union))ᶜ := by
    rw [image_compl_eq_range_sdiff_image Subtype.val_injective, Subtype.range_coe]
    rfl
  rw [h]
  exact (isClosed_regionM1 Z C).isClosedMap_subtype_val _ isOpen_interior.isClosed_compl

/-- **Consumer: `∂M₂` lies in the ambient interior** (`JunctionsV2.frontier_M2`). -/
theorem JunctionsV2.boundaryM2_subset_interior {Z : ZeroDomains W} {C : CuspCores W E}
    {S : SlimPiecesV2 W Z C} {P : EdgeBundle W} {R : CircleBundle W}
    (J : JunctionsV2 W E Z C S P R) : S.boundaryM2 ⊆ (W.interior : Set W.Carrier) := by
  rw [← J.frontier_M2]
  exact (isClosed_regionM2 S).frontier_subset.trans (regionM2_subset_interior S)

end GC.GraphManifold.Assembly.FC39P0
