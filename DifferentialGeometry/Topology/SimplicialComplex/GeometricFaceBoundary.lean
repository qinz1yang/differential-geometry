import DifferentialGeometry.Topology.Simplex.VertexFaces
import DifferentialGeometry.Topology.SimplicialComplex.MaximalFace

set_option autoImplicit false
noncomputable section
open Set Finset
namespace Poincare.Topology.SimplicialComplex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem image_face_inter (t : Finset E) :
    (fun i : s => (i : E)) '' {i | (i : E) ∈ t} = (s : Set E) ∩ t := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.prop, hi⟩
  · rintro ⟨has, hat⟩
    exact ⟨⟨a, has⟩, hat, rfl⟩

theorem vertexMap_mem_geometricFaceCostar_iff (hs : s ∈ K.faces) (x : stdSimplex ℝ s) :
    Poincare.Simplex.vertexMap (fun i : s => (i : E)) x ∈ (geometricFaceCostar K s).space ↔
      x ∈ Poincare.Simplex.boundary s := by
  classical
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hxs : Poincare.Simplex.vertexMap (fun i : s => (i : E)) x ∈ convexHull ℝ (s : Set E) := by
      have hr : Set.range (fun i : s => (i : E)) = (s : Set E) := by
        ext a
        simp
      rw [← hr]
      exact Poincare.Simplex.vertexMap_mem_convexHull (fun i : s => (i : E)) x
    have hinter := K.inter_subset_convexHull hs ht.1 ⟨hxs, hxt⟩
    rw [← image_face_inter (s := s) t] at hinter
    have hw := (Poincare.Simplex.vertexMap_mem_convexHull_image_iff (K.indep hs) _ x).mp hinter
    have hnt : ∃ a ∈ s, a ∉ t := Finset.not_subset.mp ht.2
    obtain ⟨a, has, hat⟩ := hnt
    exact ⟨⟨a, has⟩, hw ⟨a, has⟩ hat⟩
  · rintro ⟨i, hi⟩
    have hw : ∀ j : s, (j : E) ∉ s.erase i.val → x.val j = 0 := by
      intro j hj
      have hji : j = i := by
        apply Subtype.ext
        simpa only [mem_erase, j.prop, and_true, not_not] using hj
      simpa only [hji] using hi
    have hh := (Poincare.Simplex.vertexMap_mem_convexHull_image_iff (K.indep hs)
      {j : s | (j : E) ∈ s.erase i.val} x).mpr hw
    rw [image_face_inter] at hh
    rw [Set.inter_eq_right.mpr (show (s.erase i.val : Set E) ⊆ s from erase_subset _ _)] at hh
    have hne : (s.erase i.val).Nonempty := by
      exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hh⟩)
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨s.erase i.val, ⟨K.down_closed hs (erase_subset _ _) hne, ?_⟩, hh⟩
    intro hsub
    exact notMem_erase i.val s (hsub i.prop)

end Poincare.Topology.SimplicialComplex
