import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Geometry.Manifold.ChartedSpace

open Set
namespace DifferentialGeometry.Topology.Covering

theorem t2Space_of_isCoveringMap {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [T2Space B] {p : E → B} (hp : IsCoveringMap p) : T2Space E := by
  constructor
  intro x y hxy
  by_cases hbase : p x = p y
  · exact hp.isSeparatedMap x y hbase hxy
  · obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation hbase
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      hx, hy, hd.preimage p⟩

theorem secondCountableTopology_totalSpace {J B F : Type*} [TopologicalSpace B]
    [TopologicalSpace F] [SecondCountableTopology B] [SecondCountableTopology F]
    (Z : FiberBundleCore J B F) : SecondCountableTopology Z.TotalSpace := by
  obtain ⟨c, hc, hcover⟩ := isLindelof_univ.elim_countable_subcover Z.baseSet Z.isOpen_baseSet
    (show (univ : Set B) ⊆ ⋃ i, Z.baseSet i from
      fun b _ => mem_iUnion.mpr ⟨Z.indexAt b, Z.mem_baseSet_at b⟩)
  let : Countable c := hc.to_subtype
  let : ∀ i : c, SecondCountableTopology (Z.localTriv i.val).source :=
    fun i => (Z.localTriv i.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (fun i : c => (Z.localTriv i.val).open_source)
  apply eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_univ z.1))
  obtain ⟨hic, hz⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨⟨i, hic⟩, hz⟩

end DifferentialGeometry.Topology.Covering
