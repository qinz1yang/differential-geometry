import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

open Set

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {𝕜 V : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup V] [Module 𝕜 V]

open Classical in
def edgeGraph (K : Geometry.SimplicialComplex 𝕜 V) : SimpleGraph K.vertices where
  Adj v w := v ≠ w ∧ {(v : V), (w : V)} ∈ K.faces
  symm := ⟨fun v w h => ⟨h.1.symm, by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Classical in
@[simp]
theorem edgeGraph_adj (K : Geometry.SimplicialComplex 𝕜 V) (v w : K.vertices) :
    (edgeGraph K).Adj v w ↔ v ≠ w ∧ {(v : V), (w : V)} ∈ K.faces := Iff.rfl

theorem finite_vertices (K : Geometry.SimplicialComplex 𝕜 V) [Finite K.faces] :
    K.vertices.Finite :=
  Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)

open Classical in
theorem coe_image_neighborSet_edgeGraph (K : Geometry.SimplicialComplex 𝕜 V) (v : K.vertices) :
    ((↑) : K.vertices → V) '' (edgeGraph K).neighborSet v =
      {w : V | w ≠ (v : V) ∧ {(v : V), w} ∈ K.faces} := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun h => hu.1 (Subtype.ext h.symm), hu.2⟩
  · rintro ⟨hwv, hw⟩
    have hwK : w ∈ K.vertices :=
      (K.isRelLowerSet_faces hw).2 (by simp) (Finset.singleton_nonempty w)
    exact ⟨⟨w, hwK⟩, ⟨fun h => hwv (congrArg Subtype.val h).symm, hw⟩, rfl⟩

open Classical in
theorem ncard_neighborSet_edgeGraph (K : Geometry.SimplicialComplex 𝕜 V) (v : K.vertices) :
    ((edgeGraph K).neighborSet v).ncard =
      {w : V | w ≠ (v : V) ∧ {(v : V), w} ∈ K.faces}.ncard := by
  rw [← coe_image_neighborSet_edgeGraph]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

end DifferentialGeometry.Topology.SimplicialComplex
