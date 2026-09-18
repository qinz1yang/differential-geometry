import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.of_geometricLink_pair [DecidableEq E]
    (K K' M M' : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite K'.faces]
    (hM : M.faces ⊆ K.faces) (hM' : M'.faces ⊆ K'.faces) {p q : E}
    (hp : {p} ∈ K.faces) (hpM : {p} ∈ M.faces) (hq : {q} ∈ K'.faces) (hqM' : {q} ∈ M'.faces)
    (hK : K.space ∈ 𝓝 p) {f : E → E}
    (hf : IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {p}).space
      (SimplicialComplex.geometricLink K' {q}).space)
    (hfM : f '' (SimplicialComplex.geometricLink M {p}).space =
      (SimplicialComplex.geometricLink M' {q}).space)
    {B B' : Set E}
    (hB : closedStar K p ∩ B = coneSet p ((SimplicialComplex.geometricLink K {p}).space ∩ B))
    (hB' : closedStar K' q ∩ B' = coneSet q ((SimplicialComplex.geometricLink K' {q}).space ∩ B'))
    (hfB : f '' ((SimplicialComplex.geometricLink K {p}).space ∩ B) =
      (SimplicialComplex.geometricLink K' {q}).space ∩ B')
    (hcross : HasPLCrossingAt M'.space B' q) : HasPLCrossingAt M.space B p := by
  obtain ⟨g, hg, -, hgp, hpair⟩ := exists_isPLHomeomorphOn_closedStar_pair hp hq hf
  refine HasPLCrossingAt.of_closedStar_pair K K' M M' hM hM' hK hg hgp ?_ ?_ hcross
  · rw [closedStar_eq_coneSet M hpM, closedStar_eq_coneSet M' hqM',
      hpair _ (geometricLink_singleton_space_subset hM p), hfM]
  · rw [hB, hB', hpair _ inter_subset_left, hfB]

end DifferentialGeometry.Topology.PiecewiseLinear
