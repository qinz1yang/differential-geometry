import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_lt_and_gt_of_mem_height_section_of_avoids_vertices
    (L : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) (r : ℝ)
    (havoid : ∀ v ∈ L.vertices, ℓ v ≠ r) {z : E}
    (hz : z ∈ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ)) :
    (∃ x ∈ L.space, ℓ x < r) ∧ ∃ x ∈ L.space, r < ℓ x := by
  classical
  have hzlevel : ℓ z = r := hz.2
  obtain ⟨s, hs, hzs⟩ := exists_face_mem_openSimplex L hz.1
  have hvertices : ∀ v ∈ s, v ∈ L.vertices := fun v hv =>
    L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hbelow : ∃ v ∈ s, ℓ v < r := by
    by_contra h
    push Not at h
    have hall := (affineMap_eq_iff_of_mem_openSimplex_of_ge ℓ.toLinearMap.toAffineMap hzs
      (fun v hv => h v hv)).mp hzlevel
    obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
    exact havoid v (hvertices v hv) (hall v hv)
  have habove : ∃ v ∈ s, r < ℓ v := by
    by_contra h
    push Not at h
    have hall := (affineMap_eq_iff_of_mem_openSimplex_of_le ℓ.toLinearMap.toAffineMap hzs
      (fun v hv => h v hv)).mp hzlevel
    obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
    exact havoid v (hvertices v hv) (hall v hv)
  obtain ⟨a, ha, halt⟩ := hbelow
  obtain ⟨b, hb, hblt⟩ := habove
  exact ⟨⟨a, L.vertices_subset_space (hvertices a ha), halt⟩,
    ⟨b, L.vertices_subset_space (hvertices b hb), hblt⟩⟩

theorem isPLSphere_one_height_section_ne_singleton
    (L : Geometry.SimplicialComplex ℝ E) (hL : IsPLSphere 1 L.space)
    (ℓ : E →L[ℝ] ℝ) (r : ℝ) (havoid : ∀ v ∈ L.vertices, ℓ v ≠ r) (z : E) :
    L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) ≠ {z} := by
  intro hsingle
  have hz : z ∈ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) := hsingle.symm.subset (mem_singleton z)
  obtain ⟨⟨a, haL, ha⟩, b, hbL, hb⟩ :=
    exists_lt_and_gt_of_mem_height_section_of_avoids_vertices L ℓ r havoid hz
  have haz : a ≠ z := fun h => ha.ne (h ▸ hz.2)
  have hbz : b ≠ z := fun h => hb.ne' (h ▸ hz.2)
  obtain ⟨y, hy, hylevel⟩ := (hL.isConnected_sdiff_singleton_one z).isPreconnected.intermediate_value
    ⟨haL, haz⟩ ⟨hbL, hbz⟩ ℓ.continuous.continuousOn ⟨ha.le, hb.le⟩
  have hysection : y ∈ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) := ⟨hy.1, hylevel⟩
  have hyz : y = z := by simpa only [mem_singleton_iff] using hsingle.subset hysection
  exact hy.2 hyz

theorem height_section_eq_empty_or_pair_of_encard_le_two
    (L : Geometry.SimplicialComplex ℝ E) (hL : IsPLSphere 1 L.space)
    (ℓ : E →L[ℝ] ℝ) (r : ℝ) (havoid : ∀ v ∈ L.vertices, ℓ v ≠ r)
    (hcard : (L.space ∩ ℓ ⁻¹' ({r} : Set ℝ)).encard ≤ 2) :
    L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) = ∅ ∨
      ∃ a b : E, a ≠ b ∧ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) = {a, b} := by
  classical
  let Z := L.space ∩ ℓ ⁻¹' ({r} : Set ℝ)
  by_cases hZ : Z = ∅
  · exact Or.inl hZ
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hZ
  by_cases hZa : Z ⊆ {a}
  · have hsingle : Z = {a} := Subset.antisymm hZa (singleton_subset_iff.mpr ha)
    exact (isPLSphere_one_height_section_ne_singleton L hL ℓ r havoid a hsingle).elim
  obtain ⟨b, hb, hba⟩ := Set.not_subset.mp hZa
  have hab : a ≠ b := fun h => hba (h ▸ mem_singleton a)
  refine Or.inr ⟨a, b, hab, ?_⟩
  exact fiber_eq_pair_of_encard_le_two ℓ L.space ha.1 hb.1 hab ha.2 hb.2 hcard

end DifferentialGeometry.Topology.PiecewiseLinear
