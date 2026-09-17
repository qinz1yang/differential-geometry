import DifferentialGeometry.Topology.PiecewiseLinear.ConeBase
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsConeBase.of_faces_subset {p : E} {K L : Geometry.SimplicialComplex ℝ E}
    (hK : IsConeBase p K) (hLK : L.faces ⊆ K.faces) : IsConeBase p L where
  notMem_space hp := hK.notMem_space (space_mono_of_faces_subset hLK hp)
  indep s hs := hK.indep s (hLK hs)
  radial x hx y hy := hK.radial x (space_mono_of_faces_subset hLK hx)
    y (space_mono_of_faces_subset hLK hy)

open Classical in
theorem coneComplex_space_inter_fiber {p : E} {K L : Geometry.SimplicialComplex ℝ E}
    (hK : IsConeBase p K) (hL : IsConeBase p L) (ℓ : E →ₗ[ℝ] ℝ)
    (hspace : L.space = K.space ∩ {x | ℓ x = ℓ p}) :
    (coneComplex hL).space = (coneComplex hK).space ∩ {x | ℓ x = ℓ p} := by
  ext x
  constructor
  · intro hx
    rcases (mem_coneComplex_space_iff hL).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact ⟨apex_mem_coneComplex_space hK, rfl⟩
    · have hz' := hspace.subset hz
      refine ⟨(mem_coneComplex_space_iff hK).mpr (Or.inr ⟨z, hz'.1, t, ht, ht1, rfl⟩), ?_⟩
      have hzheight : ℓ z = ℓ p := hz'.2
      change ℓ (p + t • (z - p)) = ℓ p
      simp only [map_add, map_smul, map_sub, hzheight, sub_self, smul_zero, add_zero]
  · rintro ⟨hx, hheight⟩
    rcases (mem_coneComplex_space_iff hK).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact apex_mem_coneComplex_space hL
    · have hzt : ℓ z = ℓ p := by
        change ℓ (p + t • (z - p)) = ℓ p at hheight
        simp only [map_add, map_smul, map_sub, smul_eq_mul] at hheight
        have hmul : t * (ℓ z - ℓ p) = 0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ht.ne')
      exact (mem_coneComplex_space_iff hL).mpr
        (Or.inr ⟨z, hspace.symm.subset ⟨hz, hzt⟩, t, ht, ht1, rfl⟩)

open Classical in
theorem IsConeBase.exists_coneComplex_inter_fiber [FiniteDimensional ℝ E]
    {p : E} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsConeBase p K) (ℓ : E →ₗ[ℝ] ℝ)
    (hpoly : IsPolyhedron (K.space ∩ {x | ℓ x = ℓ p})) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (hL : IsConeBase p L), L.faces.Finite ∧
      L.space = K.space ∩ {x | ℓ x = ℓ p} ∧
      (coneComplex hL).space = (coneComplex hK).space ∩ {x | ℓ x = ℓ p} := by
  classical
  obtain ⟨R, hR, hRfin, hspace⟩ := exists_isSubdivision_restrict_space K hpoly inter_subset_left
  let _ : Finite R.faces := hRfin.to_subtype
  let L := restrict R (K.space ∩ {x | ℓ x = ℓ p})
  have hL : IsConeBase p L :=
    (hK.of_isSubdivision hR).of_faces_subset (restrict_faces_subset R _)
  exact ⟨L, hL, restrict_faces_finite R _, hspace, coneComplex_space_inter_fiber hK hL ℓ hspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
