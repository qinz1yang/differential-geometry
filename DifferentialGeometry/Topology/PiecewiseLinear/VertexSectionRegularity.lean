import DifferentialGeometry.Topology.PiecewiseLinear.CircleHeightSection
import DifferentialGeometry.Topology.PiecewiseLinear.VertexCrossingLevel
import DifferentialGeometry.Topology.PiecewiseLinear.VertexIsolation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem notMem_heightSingularPoints_of_geometricLink_section_encard_le_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces) (hK : K.space ∈ 𝓝 p)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    (havoid : ∀ v ∈ (SimplicialComplex.geometricLink M {p}).vertices, ℓ v ≠ ℓ p)
    (hcard : ((SimplicialComplex.geometricLink M {p}).space ∩
      {x | ℓ x = ℓ p}).encard ≤ 2) :
    p ∉ heightSingularPoints M.space ℓ := by
  have hfiber : ℓ ⁻¹' ({ℓ p} : Set ℝ) = {x | ℓ x = ℓ p} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  have hsection := height_section_eq_empty_or_pair_of_encard_le_two
    (SimplicialComplex.geometricLink M {p}) hlink ℓ (ℓ p) havoid (by rwa [hfiber])
  rcases hsection with hzero | ⟨a, b, hab, hpair⟩
  · apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty M hp ℓ.toLinearMap
    rwa [hfiber] at hzero
  · have ha : a ∈ (SimplicialComplex.geometricLink M {p}).space ∩
        ℓ ⁻¹' ({ℓ p} : Set ℝ) := by
      rw [hpair]
      exact Set.mem_insert a {b}
    obtain ⟨hneg, hpos⟩ :=
      exists_lt_and_gt_of_mem_height_section_of_avoids_vertices
        (SimplicialComplex.geometricLink M {p}) ℓ (ℓ p) havoid ha
    apply notMem_heightSingularPoints_of_hasPLCrossingAt
    exact hasPLCrossingAt_fiber_of_geometricLink_section_at hdimE K M hM hp hK ℓ hℓ
      hside hlink hab (by rwa [hfiber] at hpair) hpos hneg

end DifferentialGeometry.Topology.PiecewiseLinear
