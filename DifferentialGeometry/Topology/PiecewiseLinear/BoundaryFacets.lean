import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface
    [dE : DecidableEq E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hcard : s.card = n + 1) :
    s ∈ (boundaryComplex (n + 1) K).faces ↔
      ∃ a, {w | w ∉ s ∧ insert w s ∈ K.faces} = {a} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  constructor
  · intro hs
    have hlink := ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.2
    rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hlink
    exact isPLBall_zero_iff.mp hlink
  · rintro ⟨a, ha⟩
    have hamem : a ∉ s ∧ insert a s ∈ K.faces := by
      change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
      rw [ha]
      exact mem_singleton a
    have hs : s ∈ K.faces := K.down_closed hamem.2 (Finset.subset_insert a s)
      (Finset.card_pos.mp (by omega))
    apply (hK.mem_boundaryComplex_faces_iff K).mpr
    refine ⟨hs, hcard.le, ?_⟩
    rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hbound]
    exact isPLBall_zero_iff.mpr ⟨a, ha⟩

theorem boundaryComplex_eq_subcomplexGeneratedBy_facets [DecidableEq E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall (n + 1) K.space) :
    boundaryComplex (n + 1) K = subcomplexGeneratedBy (boundaryComplex (n + 1) K)
      {s | s.card = n + 1} := by
  have hfin : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  have hB := isPLSphere_boundaryComplex_space_of_isPLBall (n := n) K hK
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, hst, hcard⟩ :=
      exists_face_superset_card_eq_of_isPLSphere (boundaryComplex (n + 1) K) hB hs
    exact ⟨t, ⟨ht, hcard⟩, hst, (boundaryComplex (n + 1) K).nonempty_of_mem_faces hs⟩
  · intro hs
    exact subcomplexGeneratedBy_faces_subset (boundaryComplex (n + 1) K) {t | t.card = n + 1} hs

end DifferentialGeometry.Topology.PiecewiseLinear
