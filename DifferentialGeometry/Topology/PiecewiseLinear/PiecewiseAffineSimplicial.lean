import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Star

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineOn.exists_isSubdivision_affineOn_faces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {f : E → F}
    (hf : IsPiecewiseAffineOn f K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      ∀ s ∈ K'.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
  classical
  choose! ι hι C A hCA hnhds using hf
  choose! u hu using fun x (hx : x ∈ K.space) => mem_nhdsWithin.mp (hnhds x hx)
  have hcomp : IsCompact K.space := (isPolyhedron_space K).isCompact
  obtain ⟨t, ht, hcover⟩ := hcomp.elim_nhds_subcover u
    fun x hx => (hu x hx).1.mem_nhds (hu x hx).2.1
  have hfin : ∀ x : t, Finite (ι x) := fun x => hι x (ht x x.2)
  let Q : (Σ x : t, ι x) → Set E := fun p => C p.1 p.2
  have hQ : ∀ p, IsPolyhedron (Q p) := fun p => (hCA p.1 (ht p.1 p.1.2) p.2).1.isPolyhedron
  have hQK : ∀ p, Q p ⊆ K.space := fun p => (hCA p.1 (ht p.1 p.1.2) p.2).2.1
  obtain ⟨K', hK', hfin', hunion⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  refine ⟨K', hK', hfin', fun s hs => ?_⟩
  have hx₀ : s.centroid ℝ id ∈ openSimplex s :=
    centroid_mem_openSimplex (K'.nonempty_of_mem_faces hs)
  have hx₀K : s.centroid ℝ id ∈ K.space :=
    hK'.space_eq ▸ K'.convexHull_subset_space hs (openSimplex_subset_convexHull s hx₀)
  obtain ⟨x, hxt, hx₀u⟩ := mem_iUnion₂.mp (hcover hx₀K)
  have hxK : x ∈ K.space := ht x hxt
  obtain ⟨i, hx₀i⟩ := mem_iUnion.mp ((hu x hxK).2.2 ⟨hx₀u, hx₀K⟩)
  have hx₀Q : s.centroid ℝ id ∈ Q ⟨⟨x, hxt⟩, i⟩ := hx₀i
  rw [hunion ⟨⟨x, hxt⟩, i⟩] at hx₀Q
  obtain ⟨s', ⟨hs', hs'Q⟩, hx₀s'⟩ := mem_iUnion₂.mp hx₀Q
  have hss' : s ⊆ s' := face_subset_of_mem_openSimplex_of_mem_convexHull K' hs hs' hx₀ hx₀s'
  refine ⟨A x i, fun y hy => (hCA x hxK i).2.2 ?_⟩
  exact hs'Q (convexHull_mono (Finset.coe_subset.mpr hss') hy)

end DifferentialGeometry.Topology.PiecewiseLinear
