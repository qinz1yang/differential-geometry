import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.SimplicialComplex.BoundaryCounting

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]

open Classical in
theorem eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary {n k : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hs : s ∈ K.faces) (hc : s.card = k + 1) (hk : k ≤ n) :
    eulerChar (SimplicialComplex.geometricLink K s) =
      if s ∈ (boundaryComplex (n + 1) K).faces then 1 else 1 + (-1 : ℤ) ^ (n - k) := by
  by_cases hb : s ∈ (boundaryComplex (n + 1) K).faces
  · rw [if_pos hb]
    exact eulerChar_of_isPLBall _ ((hK.mem_boundaryComplex_faces_iff K).mp hb).2.2
  · rw [if_neg hb]
    rcases hK.isPLSphere_or_isPLBall_geometricLink K hs hc hk with hS | hB
    · exact eulerChar_of_isPLSphere _ hS
    · exfalso
      apply hb
      apply (hK.mem_boundaryComplex_faces_iff K).mpr
      refine ⟨hs, by omega, ?_⟩
      simpa only [hc, Nat.add_sub_add_right] using hB

open Classical in
theorem eulerChar_boundaryComplex_eq_two_mul
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    eulerChar (boundaryComplex 3 K) = 2 * eulerChar K := by
  apply SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts
    K.toPreAbstractSimplicialComplex (boundaryComplex 3 K).toPreAbstractSimplicialComplex
  · exact boundaryComplex_faces_subset 3 K
  · exact fun _ hs => hK.card_le K hs
  · exact fun _ hs => ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.1
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    change (faceCofaces K s 4).card = if s ∈ (boundaryComplex 3 K).faces then 1 else 2
    by_cases hb : s ∈ (boundaryComplex 3 K).faces
    · rw [if_pos hb]
      exact (hK.mem_boundaryComplex_iff_card_cofaces_eq_one K hsK hc).mp hb
    · rw [if_neg hb]
      exact (hK.card_faceCofaces_eq_one_or_two K hsK hc).resolve_left fun h =>
        hb ((hK.mem_boundaryComplex_iff_card_cofaces_eq_one K hsK hc).mpr h)
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    have h := eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary K hK hsK hc (by decide)
    change SimplicialComplex.faceEulerChar (SimplicialComplex.link K.toPreAbstractSimplicialComplex s) = _ at h
    norm_num at h
    exact h
  · intro s hs
    obtain ⟨hsK, hc⟩ := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    have h := eulerChar_geometricLink_of_isCombinatorialManifoldWithBoundary K hK hsK hc (by decide)
    change SimplicialComplex.faceEulerChar (SimplicialComplex.link K.toPreAbstractSimplicialComplex s) = _ at h
    norm_num at h
    exact h

end DifferentialGeometry.Topology.PiecewiseLinear
