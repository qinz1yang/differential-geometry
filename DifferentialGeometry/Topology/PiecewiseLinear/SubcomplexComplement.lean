import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem closure_space_sdiff_space_eq_subcomplexGeneratedBy
    (K A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces]
    (hA : A.faces ⊆ K.faces) (hB : B.faces ⊆ K.faces) :
    closure (A.space \ B.space) = (subcomplexGeneratedBy A B.facesᶜ).space := by
  let R := subcomplexGeneratedBy A B.facesᶜ
  have : Finite R.faces := (subcomplexGeneratedBy_faces_finite A B.facesᶜ).to_subtype
  apply Subset.antisymm
  · apply closure_minimal ?_ (isPolyhedron_space R).isCompact.isClosed
    rintro x ⟨hxA, hxB⟩
    obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hxA
    have hsB : s ∉ B.faces := fun h => hxB (B.convexHull_subset_space h hxs)
    exact R.convexHull_subset_space
      ⟨s, ⟨hs, hsB⟩, Finset.Subset.rfl, A.nonempty_of_mem_faces hs⟩ hxs
  · intro x hx
    obtain ⟨s, ⟨t, ht, hst, -⟩, hxs⟩ := R.mem_space_iff.mp hx
    have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono (Finset.coe_subset.mpr hst) hxs
    apply closure_mono (s := openSimplex t) ?_
      (convexHull_subset_closure_openSimplex (A.nonempty_of_mem_faces ht.1) hxt)
    intro y hy
    exact ⟨A.convexHull_subset_space ht.1 (openSimplex_subset_convexHull t hy),
      notMem_space_of_notMem_faces hB (hA ht.1) ht.2 hy⟩

theorem closure_space_sdiff_convexHull_eq_subcomplexGeneratedBy
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : A.faces ⊆ K.faces)
    {t : Finset E} (ht : t ∈ K.faces) :
    closure (A.space \ convexHull ℝ (t : Set E)) =
      (subcomplexGeneratedBy A {s | ¬s ⊆ t}).space := by
  let R := subcomplexGeneratedBy A {s | ¬s ⊆ t}
  have : Finite R.faces := (subcomplexGeneratedBy_faces_finite A {s | ¬s ⊆ t}).to_subtype
  apply Subset.antisymm
  · apply closure_minimal ?_ (isPolyhedron_space R).isCompact.isClosed
    rintro x ⟨hxA, hxt⟩
    obtain ⟨s, hs, hxs⟩ := A.mem_space_iff.mp hxA
    have hst : ¬s ⊆ t := fun h => hxt (convexHull_mono (Finset.coe_subset.mpr h) hxs)
    exact R.convexHull_subset_space
      ⟨s, ⟨hs, hst⟩, Finset.Subset.rfl, A.nonempty_of_mem_faces hs⟩ hxs
  · intro x hx
    obtain ⟨s, ⟨u, hu, hsu, -⟩, hxs⟩ := R.mem_space_iff.mp hx
    have hxu : x ∈ convexHull ℝ (u : Set E) := convexHull_mono (Finset.coe_subset.mpr hsu) hxs
    apply closure_mono (s := openSimplex u) ?_
      (convexHull_subset_closure_openSimplex (A.nonempty_of_mem_faces hu.1) hxu)
    intro y hy
    exact ⟨A.convexHull_subset_space hu.1 (openSimplex_subset_convexHull u hy),
      fun hyt => hu.2 (face_subset_of_mem_openSimplex_of_mem_convexHull K (hA hu.1) ht hy hyt)⟩

theorem IsPolyhedron.closure_sdiff {P Q : Set E} (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) : IsPolyhedron (closure (P \ Q)) := by
  classical
  obtain ⟨K, hKfin, hK⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hR, hRfin, hRQ⟩ := exists_isSubdivision_restrict_space K (hP.inter hQ)
    (inter_subset_left.trans hK.ge)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRspace : R.space = P := hR.space_eq.trans hK
  have hdiff : R.space \ (restrict R (P ∩ Q)).space = P \ Q := by
    rw [hRspace, hRQ]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [← hdiff, closure_space_sdiff_space_eq_subcomplexGeneratedBy R R
    (restrict R (P ∩ Q)) subset_rfl (restrict_faces_subset R _)]
  let _ : Finite (subcomplexGeneratedBy R (restrict R (P ∩ Q)).facesᶜ).faces :=
    (subcomplexGeneratedBy_faces_finite R _).to_subtype
  exact isPolyhedron_space _

theorem closure_space_sdiff_closure_sdiff_space_eq
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hAK : A.faces ⊆ K.faces) (hK : ∀ t ∈ K.faces, t.card ≤ n)
    (hA : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = n) :
    closure (K.space \ closure (K.space \ A.space)) = A.space := by
  rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K K A Subset.rfl hAK,
    closure_space_sdiff_space_eq_subcomplexGeneratedBy K K (subcomplexGeneratedBy K A.facesᶜ)
      Subset.rfl (subcomplexGeneratedBy_faces_subset K A.facesᶜ),
    subcomplexGeneratedBy_compl_compl K A hAK hK hA]

end DifferentialGeometry.Topology.PiecewiseLinear
