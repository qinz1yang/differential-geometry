import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Faces

/-!
# FC39 GROUP G, targets `stub_exists_vertexLayer` and `stub_exists_portLayer` (lane FC39-G1)

The frozen targets `T:302–304` and `T:307–310`
(`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`), proved as general theorems
on the contract (external review 56, D56-1):

* `exists_vertexLayer_G1` — the vertex layer of the rows: the row indices
  `Fin Z.count ⊕ Fin n ⊕ Fin S.count` enumerated by `rowIndexEquiv_G1` (a finite enumeration, no
  choice), vertex `k` the row vertex of its index, so the link keeps `vertex_eq` (equality in
  `Vertex W`: the row piece AND the row model, not only the ambient image);
* `exists_portLayer_G1` — the port layer over a GIVEN vertex layer and link: the owner of the port
  `i` is read through the same vertex index, `vlink.index⁻¹ (inr (inl i))` (the cusp core `i`);
  boundary exhaustion from `CuspCores.ports`, ownership of the collar from `CuspCores.collar_owned`
  through `vertex_eq` and `rowVertex_image`.
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

/-! ## The vertex layer -/

/-- The finite enumeration of the row indices `Fin Z.count ⊕ Fin n ⊕ Fin S.count`. -/
def rowIndexEquiv_G1 (Rw : FC39RowsV2 W E) :
    Fin (Rw.zero.count + (n + Rw.slim.count)) ≃ Rw.slim.RowIndex :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)

/-- The vertex layer of the rows: vertex `k` is the row vertex (row piece with the row model) of
the row index `rowIndexEquiv_G1 Rw k`. -/
def vertexLayer_G1 (Rw : FC39RowsV2 W E) : VertexLayer W where
  vertexCount := Rw.zero.count + (n + Rw.slim.count)
  vertex k := Rw.rowVertex (rowIndexEquiv_G1 Rw k)

theorem vertexLayer_G1_vertexCount (Rw : FC39RowsV2 W E) :
    (vertexLayer_G1 Rw).vertexCount = Rw.zero.count + (n + Rw.slim.count) :=
  rfl

/-- The vertex link of `vertexLayer_G1`: the index is the enumeration, `vertex_eq` holds by
definition. -/
def vertexModelLink_G1 (Rw : FC39RowsV2 W E) : VertexModelLink Rw (vertexLayer_G1 Rw) where
  index := rowIndexEquiv_G1 Rw
  vertex_eq _ := rfl

theorem vertexModelLink_G1_index (Rw : FC39RowsV2 W E)
    (k : Fin (vertexLayer_G1 Rw).vertexCount) :
    (vertexModelLink_G1 Rw).index k = rowIndexEquiv_G1 Rw k :=
  rfl

/-- **GROUP G, `stub_exists_vertexLayer` (frozen statement `T:302–304`).** -/
theorem exists_vertexLayer_G1 (Rw : FC39RowsV2 W E) :
    ∃ V : VertexLayer W, Nonempty (VertexModelLink Rw V) :=
  ⟨vertexLayer_G1 Rw, ⟨vertexModelLink_G1 Rw⟩⟩

/-- Any vertex link fixes the vertex count: the number of row indices. -/
theorem VertexModelLink.vertexCount_eq_G1 {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    (vlink : VertexModelLink Rw V) : V.vertexCount = Rw.zero.count + (n + Rw.slim.count) := by
  simpa using Fintype.card_congr vlink.index

/-- Under a vertex link, the vertex image is the row set of its index. -/
theorem VertexModelLink.image_eq_G1 {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    (vlink : VertexModelLink Rw V) (k : Fin V.vertexCount) :
    (V.vertex k).image = Rw.slim.rowSet (vlink.index k) := by
  rw [vlink.vertex_eq k, Rw.rowVertex_image]

/-! ## The port layer -/

/-- The port layer over a given vertex layer and link: the port `i` is owned by the vertex of the
cusp core `i`, read through the SAME vertex index. -/
def portLayer_G1 (Rw : FC39RowsV2 W E) (V : VertexLayer W) (vlink : VertexModelLink Rw V) :
    PortLayer W E V where
  external_exhausted := Rw.cusp.ports
  externalOwner i := vlink.index.symm (.inr (.inl i))
  external_owned i := by
    rw [vlink.image_eq_G1, Equiv.apply_symm_apply]
    exact Rw.cusp.collar_owned i

theorem portLayer_G1_externalOwner (Rw : FC39RowsV2 W E) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) (i : Fin n) :
    (portLayer_G1 Rw V vlink).externalOwner i = vlink.index.symm (.inr (.inl i)) :=
  rfl

/-- The port link of `portLayer_G1`. -/
theorem portModelLink_G1 (Rw : FC39RowsV2 W E) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) : PortModelLink Rw vlink (portLayer_G1 Rw V vlink) :=
  ⟨fun i => vlink.index.apply_symm_apply (.inr (.inl i))⟩

/-- **GROUP G, `stub_exists_portLayer` (frozen statement `T:307–310`).** -/
theorem exists_portLayer_G1 (Rw : FC39RowsV2 W E) (V : VertexLayer W)
    (vlink : VertexModelLink Rw V) :
    ∃ O : PortLayer W E V, PortModelLink Rw vlink O :=
  ⟨portLayer_G1 Rw V vlink, portModelLink_G1 Rw V vlink⟩

/-- A port link determines the owners: the owner of the port `i` is the vertex of the cusp core
`i` under the vertex index (uniqueness of the port layer's owner function). -/
theorem PortModelLink.externalOwner_eq_G1 {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    {vlink : VertexModelLink Rw V} {O : PortLayer W E V} (olink : PortModelLink Rw vlink O)
    (i : Fin n) : O.externalOwner i = vlink.index.symm (.inr (.inl i)) := by
  rw [← olink.owner_index i, Equiv.symm_apply_apply]

/-- The owner of a port under a port link is the cusp core `i`, as a vertex of `Vertex W`. -/
theorem PortModelLink.owner_vertex_G1 {Rw : FC39RowsV2 W E} {V : VertexLayer W}
    {vlink : VertexModelLink Rw V} {O : PortLayer W E V} (olink : PortModelLink Rw vlink O)
    (i : Fin n) :
    V.vertex (O.externalOwner i) = .cuspCore (Rw.cusp.piece i) (Rw.cusp.product i) := by
  rw [vlink.vertex_eq, olink.owner_index i]
  rfl

/-! ## The chain vertex → port on one `Rw` -/

/-- The vertex layer and the port layer of the rows, the port owners read through the vertex
link of the same output (the first step of the GROUP G order, D56 lane plan). -/
theorem exists_vertexLayer_portLayer_G1 (Rw : FC39RowsV2 W E) :
    ∃ V : VertexLayer W, ∃ vlink : VertexModelLink Rw V, ∃ O : PortLayer W E V,
      PortModelLink Rw vlink O := by
  obtain ⟨V, ⟨vlink⟩⟩ := exists_vertexLayer_G1 Rw
  obtain ⟨O, olink⟩ := exists_portLayer_G1 Rw V vlink
  exact ⟨V, vlink, O, olink⟩

end GC.GraphManifold.Assembly.FC39P0
