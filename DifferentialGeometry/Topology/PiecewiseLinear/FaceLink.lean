import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import DifferentialGeometry.Topology.SimplicialComplex.GeometricLink

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : Geometry.SimplicialComplex ℝ E)

theorem mem_geometricLink_faces_iff {s t : Finset E} :
    t ∈ (SimplicialComplex.geometricLink K s).faces ↔
      t.Nonempty ∧ Disjoint s t ∧ s ∪ t ∈ K.faces := Iff.rfl

theorem geometricLink_faces_subset (s : Finset E) :
    (SimplicialComplex.geometricLink K s).faces ⊆ K.faces :=
  SimplicialComplex.geometricLink_le K s

theorem geometricLink_empty : SimplicialComplex.geometricLink K ∅ = K := by
  ext t
  rw [mem_geometricLink_faces_iff, Finset.empty_union]
  exact ⟨fun h => h.2.2, fun h => ⟨K.nonempty_of_mem_faces h, Finset.disjoint_empty_left t, h⟩⟩

theorem geometricLink_insert {v : E} {s : Finset E} (hv : v ∉ s) :
    SimplicialComplex.geometricLink K (insert v s) =
      SimplicialComplex.geometricLink (SimplicialComplex.geometricLink K {v}) s := by
  ext t
  rw [mem_geometricLink_faces_iff, mem_geometricLink_faces_iff,
    SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hdisj, hmem⟩
    have hvt : v ∉ t := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self v s)
    refine ⟨hne, hdisj.mono_left (Finset.subset_insert v s), hne.mono Finset.subset_union_right,
      ?_, ?_⟩
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact hv h
      · exact hvt h
    · rwa [Finset.insert_union] at hmem
  · rintro ⟨hne, hdisj, -, hvst, hmem⟩
    refine ⟨hne, ?_, ?_⟩
    · rw [Finset.disjoint_insert_left]
      exact ⟨fun h => hvst (Finset.mem_union_right s h), hdisj⟩
    · rwa [Finset.insert_union]

theorem mem_geometricLink_of_subset_of_mem {s t : Finset E} (hst : Disjoint s t)
    (hne : t.Nonempty) (h : s ∪ t ∈ K.faces) :
    t ∈ (SimplicialComplex.geometricLink K s).faces := ⟨hne, hst, h⟩

theorem union_mem_of_mem_geometricLink {s t : Finset E}
    (h : t ∈ (SimplicialComplex.geometricLink K s).faces) : s ∪ t ∈ K.faces := h.2.2

theorem mem_faces_of_mem_geometricLink {s t : Finset E} (hs : s.Nonempty)
    (h : t ∈ (SimplicialComplex.geometricLink K s).faces) : s ∈ K.faces :=
  K.down_closed h.2.2 Finset.subset_union_left hs

end DifferentialGeometry.Topology.PiecewiseLinear
