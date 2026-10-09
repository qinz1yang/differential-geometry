import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesCircle74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerRank74

/-!
# Draft 74, G7 (FDC03 corner model), step 1: structural lemmas

Lane S-JUNCTIONS2 (suffix `_JN74`). Two facts the corner sign model needs and that hold for ANY
rows / circle bundle, with no chain input:

* `CircleBundle.isOpenMap_proj_JN74`: the projection of a circle bundle is an open map (its local
  trivializations are homeomorphisms onto products and `fst`, `val` are open);
* `SlimPiecesV2.vertexSide_JN74`: the vertex side of the three-sided sign model,
  `x ∈ rowSet (owner F) ↔ residualFn F x ≤ 0` on the face neighbourhood `residualNear F`, from the
  structure fields
  `ZeroDomains.range_eq`, `CuspCores.near_eq` and `SlimPiecesV2.endFn_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

namespace CircleBundle

variable (R : CircleBundle W)

/-- **The projection of a circle bundle is an open map.** -/
theorem isOpenMap_proj_JN74 : IsOpenMap R.proj := by
  intro O hO
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  let c := R.proj x
  let N := R.neighborhood c
  have hxT : x ∈ TopologicalSpace.Opens.comap R.proj N := R.mem_neighborhood c
  let O' : Set (TopologicalSpace.Opens.comap R.proj N) := Subtype.val ⁻¹' O
  have hO' : IsOpen O' := hO.preimage continuous_subtype_val
  have h1 : IsOpen (R.trivialization c '' O') :=
    (R.trivialization c).toHomeomorph.isOpenMap O' hO'
  have h2 : IsOpen (Prod.fst '' (R.trivialization c '' O')) := isOpenMap_fst _ h1
  have h3 : IsOpen (Subtype.val '' (Prod.fst '' (R.trivialization c '' O')) : Set R.Base) :=
    N.isOpen.isOpenMap_subtype_val _ h2
  refine ⟨Subtype.val '' (Prod.fst '' (R.trivialization c '' O')), ?_, h3, ?_⟩
  · rintro _ ⟨a, ⟨p, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨y.val, hy, ?_⟩
    exact (R.projection_trivialization c y).symm
  · exact ⟨(R.trivialization c ⟨x, hxT⟩).1, ⟨_, ⟨⟨x, hxT⟩, hx, rfl⟩, rfl⟩,
      R.projection_trivialization c ⟨x, hxT⟩⟩

end CircleBundle

namespace SlimPiecesV2

variable {Z : ZeroDomains W} {C : CuspCores W E} {S : SlimPiecesV2 W Z C}

/-- **The vertex side of the sign model** on the face neighbourhood: a point of the neighbourhood
of a residual face lies in the vertex owner of the face iff the face function is `≤ 0`. -/
theorem vertexSide_JN74 {F : S.ResidualFace} {x : W.Carrier} (hx : x ∈ S.residualNear F) :
    x ∈ S.rowSet (S.residualOwner F) ↔ S.residualFn F x ≤ 0 := by
  rcases F with ⟨F', hF'⟩ | e
  · rcases F' with F'' | F''
    · change x ∈ range (Z.piece F''.1).map ↔ Z.ratio F''.1 x ≤ 0
      rw [Z.range_eq]
      rfl
    · change x ∈ range (C.piece F''.1).map ↔ C.cuspFn F''.1 x ≤ 0
      have hx' : x ∈ C.near F''.1 := hx
      have h := Set.ext_iff.1 (C.near_eq F''.1) x
      exact ⟨fun hr => (h.1 ⟨hr, hx'⟩).2, fun hc => (h.2 ⟨hx', hc⟩).1⟩
  · change x ∈ range (S.piece e.1.1.1).map ↔ S.endFn e x ≤ 0
    have hx' : x ∈ S.endNear e := hx
    have h := Set.ext_iff.1 (S.endFn_eq e) x
    exact ⟨fun hr => (h.1 ⟨hr, hx'⟩).2, fun hc => (h.2 ⟨hx', hc⟩).1⟩

end SlimPiecesV2

end GC.GraphManifold.Assembly.FC39P0
