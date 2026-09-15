import DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem eraseTriangleComplex_space_eq_closure_sdiff_convexHull
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hpure : ∀ s ∈ K.faces, ∃ u ∈ K.faces, s ⊆ u ∧ u.card = 3)
    {t : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3) :
    (eraseTriangleComplex K t).space = closure (K.space \ convexHull ℝ (t : Set E)) := by
  classical
  rw [closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy K K (Subset.refl _) ht]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨u, hu, hucard, hut, hsu, hs⟩, hxs⟩ :=
      (eraseTriangleComplex K t).mem_space_iff.mp hx
    have hut' : ¬u ⊆ t := fun h => hut (Finset.eq_of_subset_of_card_le h (by omega))
    exact (subcomplexGeneratedBy K {r | ¬r ⊆ t}).convexHull_subset_space
      ⟨u, ⟨hu, hut'⟩, hsu, hs⟩ hxs
  · intro x hx
    obtain ⟨s, ⟨r, hr, hsr, hs⟩, hxs⟩ :=
      (subcomplexGeneratedBy K {r | ¬r ⊆ t}).mem_space_iff.mp hx
    obtain ⟨u, hu, hru, hucard⟩ := hpure r hr.1
    have hut : u ≠ t := fun h => hr.2 (h ▸ hru)
    exact (eraseTriangleComplex K t).convexHull_subset_space
      ⟨u, hu, hucard, hut, hsr.trans hru, hs⟩ hxs

theorem isPLBall_eraseTriangleComplex_of_isPLSphere_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    {t : Finset E} (ht : t ∈ K.faces) (htcard : t.card = 3) :
    IsPLBall 2 (eraseTriangleComplex K t).space := by
  rw [eraseTriangleComplex_space_eq_closure_sdiff_convexHull K
    (fun s hs => exists_face_superset_card_eq_of_isPLSphere K hK hs) ht htcard]
  exact hK.isPLBall_closure_sdiff (isPLBall_convexHull_of_affineIndependent t (K.indep ht) htcard)
    (K.convexHull_subset_space ht)

end DifferentialGeometry.Topology.PiecewiseLinear
