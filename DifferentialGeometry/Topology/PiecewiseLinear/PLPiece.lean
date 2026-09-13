import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPiecewiseAffineWithinAt.union {f : E → F} {s t : Set E} {x : E}
    (hs : IsPiecewiseAffineWithinAt f s x) (ht : IsPiecewiseAffineWithinAt f t x) :
    IsPiecewiseAffineWithinAt f (s ∪ t) x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hs
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := ht
  have := hι
  have := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim C D, Sum.elim A B, ?_, ?_⟩
  · rintro (i | j)
    · exact ⟨(hC i).1, (hC i).2.1.trans subset_union_left, (hC i).2.2⟩
    · exact ⟨(hD j).1, (hD j).2.1.trans subset_union_right, (hD j).2.2⟩
  · rw [iUnion_sum, nhdsWithin_union, Filter.mem_sup]
    exact ⟨Filter.mem_of_superset hCx subset_union_left,
      Filter.mem_of_superset hDx subset_union_right⟩

theorem IsPiecewiseAffineOn.union_of_isClosed [FiniteDimensional ℝ E] {f : E → F} {s t : Set E}
    (hs : IsPiecewiseAffineOn f s) (ht : IsPiecewiseAffineOn f t) (hsc : IsClosed s)
    (htc : IsClosed t) : IsPiecewiseAffineOn f (s ∪ t) := by
  intro x hx
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t
  · exact (hs x hxs).union (ht x hxt)
  · have h := (hs x hxs).inter_of_mem_nhds (htc.isOpen_compl.mem_nhds hxt)
    have heq : s ∩ tᶜ = (s ∪ t) ∩ tᶜ := by
      rw [union_inter_distrib_right, inter_compl_self, union_empty]
    rw [heq] at h
    exact h.of_inter_of_mem_nhds (htc.isOpen_compl.mem_nhds hxt)
  · have h := (ht x hxt).inter_of_mem_nhds (hsc.isOpen_compl.mem_nhds hxs)
    have heq : t ∩ sᶜ = (s ∪ t) ∩ sᶜ := by
      rw [union_inter_distrib_right, inter_compl_self, empty_union]
    rw [heq] at h
    exact h.of_inter_of_mem_nhds (hsc.isOpen_compl.mem_nhds hxs)
  · exact absurd hx (by simp [hxs, hxt])

theorem isPolyhedron_inter_preimage_of_isCompact [FiniteDimensional ℝ E] {f : E → F} {S : Set E}
    (hf : IsPiecewiseAffineOn f S) {C : Set F} (hC : IsHPolytope C)
    (hcomp : IsCompact (S ∩ f ⁻¹' C)) : IsPolyhedron (S ∩ f ⁻¹' C) := by
  classical
  choose! ι hι Cs A hCA hnhds using hf
  choose! u hu using fun x (hx : x ∈ S) => mem_nhdsWithin.mp (hnhds x hx)
  obtain ⟨t, ht, hcover⟩ := hcomp.elim_nhds_subcover u
    fun x hx => (hu x hx.1).1.mem_nhds (hu x hx.1).2.1
  have hfin : ∀ x : t, Finite (ι x) := fun x => hι x (ht x x.2).1
  have heq : S ∩ f ⁻¹' C = ⋃ p : (Σ x : t, ι x), Cs p.1 p.2 ∩ A p.1 p.2 ⁻¹' C := by
    apply Subset.antisymm
    · rintro y ⟨hyS, hyC⟩
      obtain ⟨x, hxt, hyu⟩ := mem_iUnion₂.mp (hcover ⟨hyS, hyC⟩)
      obtain ⟨i, hyi⟩ := mem_iUnion.mp ((hu x (ht x hxt).1).2.2 ⟨hyu, hyS⟩)
      refine mem_iUnion.mpr ⟨⟨⟨x, hxt⟩, i⟩, hyi, ?_⟩
      rw [mem_preimage, ← (hCA x (ht x hxt).1 i).2.2 hyi]
      exact hyC
    · refine iUnion_subset fun p => ?_
      rintro y ⟨hyC, hyA⟩
      refine ⟨(hCA p.1 (ht p.1 p.1.2).1 p.2).2.1 hyC, ?_⟩
      rw [mem_preimage, (hCA p.1 (ht p.1 p.1.2).1 p.2).2.2 hyC]
      exact hyA
  rw [heq]
  exact IsPolyhedron.iUnion fun p =>
    ((hCA p.1 (ht p.1 p.1.2).1 p.2).1.inter_preimage hC _).isPolyhedron

universe u

structure PLPiece (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (Y : Set X) where
  ambientDim : ℕ
  complex : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDim))
  finite_faces : complex.faces.Finite
  map : EuclideanSpace ℝ (Fin ambientDim) → X
  bijOn : BijOn map complex.space Y
  continuousOn : ContinuousOn map complex.space
  isPiecewiseAffineOn_chart : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (e ∘ map) (complex.space ∩ map ⁻¹' e.source)
  isPiecewiseAffineOn_chart_symm : ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) X,
    IsPiecewiseAffineOn (Function.invFunOn map complex.space ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' Y)

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

def PLPiece.toPLTriangulation (T : PLPiece n X univ) : PLTriangulation n X where
  ambientDim := T.ambientDim
  complex := T.complex
  finite_faces := T.finite_faces.to_subtype
  map := T.map
  bijOn := T.bijOn
  continuousOn := T.continuousOn
  isPiecewiseAffineOn_chart := T.isPiecewiseAffineOn_chart
  isPiecewiseAffineOn_chart_symm := fun e he => by
    have := T.isPiecewiseAffineOn_chart_symm e he
    rwa [preimage_univ, inter_univ] at this

theorem PLPiece.isCompact {Y : Set X} (T : PLPiece n X Y) : IsCompact Y := by
  rw [← T.bijOn.image_eq]
  have := T.finite_faces.to_subtype
  exact (isPolyhedron_space T.complex).isCompact.image_of_continuousOn T.continuousOn

end DifferentialGeometry.Topology.PiecewiseLinear
