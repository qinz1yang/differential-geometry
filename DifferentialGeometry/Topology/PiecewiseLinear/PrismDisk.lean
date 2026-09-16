import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.DiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ArcDecomposition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLBall_prism_bottom_union_side (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 2 K.space) {a b : ℝ} (hab : a < b) :
    IsPLBall 2 (K.space ×ˢ {a} ∪ (boundaryComplex 2 K).space ×ˢ Icc a b) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hprod := isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨A, hAfin, hAspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hA : IsPLBall 3 A.space := hAspace.symm ▸ hprod
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall A hA
  have htop : IsPLBall 2 (K.space ×ˢ {b}) :=
    hK.of_isPLHomeomorphOn (hK.isPolyhedron.isPLHomeomorphOn_prod_const b)
  have hboundary := boundaryComplex_space_prism K hK hab A hAspace
  have htopS : K.space ×ˢ {b} ⊆ (boundaryComplex 3 A).space := by
    rw [hboundary]
    rintro x ⟨hx, hxb⟩
    exact Or.inl ⟨hx, Or.inr hxb⟩
  have hdiff : (boundaryComplex 3 A).space \ (K.space ×ˢ {b}) =
      K.space ×ˢ {a} ∪ (boundaryComplex 2 K).space ×ˢ Ico a b := by
    rw [hboundary]
    ext x
    simp only [mem_sdiff, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨hx, hxa | hxb⟩ | ⟨hxB, hxa, hxb⟩, hxnot⟩
      · exact Or.inl ⟨hx, hxa⟩
      · exact (hxnot ⟨hx, hxb⟩).elim
      · exact Or.inr ⟨hxB, hxa, lt_of_le_of_ne hxb
          (fun heq => hxnot ⟨boundaryComplex_space_subset 2 K hxB, heq⟩)⟩
    · rintro (⟨hx, hxa⟩ | ⟨hxB, hxa, hxb⟩)
      · exact ⟨Or.inl ⟨hx, Or.inl hxa⟩, fun hx => hab.ne (hxa.symm.trans hx.2)⟩
      · exact ⟨Or.inr ⟨hxB, hxa, hxb.le⟩, fun hx => hxb.ne hx.2⟩
  have h := hS.isPLBall_closure_sdiff htop htopS
  rw [hdiff, closure_union, closure_prod_eq, closure_prod_eq,
    (isPolyhedron_space K).isClosed.closure_eq, isClosed_singleton.closure_eq,
    (isPolyhedron_space (boundaryComplex 2 K)).isClosed.closure_eq, closure_Ico hab.ne] at h
  exact h

open Classical in
private theorem isPLBall_prism_bottom_union_strips_of_pairwiseDisjoint {ι : Type*}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {a b : ℝ} (hab : a < b) (d : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ d, IsPLBall 1 (A i))
    (hAB : ∀ i ∈ d, A i ⊆ (boundaryComplex 2 K).space)
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (A i) (A j)) :
    IsPLBall 2 (K.space ×ˢ {a} ∪ (⋃ i ∈ d, A i) ×ˢ Icc a b) := by
  have hB := isPLBall_prism_bottom_union_side K hK hab
  have hC : IsPLBall 2 (K.space ×ˢ {a}) :=
    hK.of_isPLHomeomorphOn (hK.isPolyhedron.isPLHomeomorphOn_prod_const a)
  have hI : ∀ i ∈ d, IsPLBall 1 ((K.space ×ˢ {a}) ∩ (A i ×ˢ Icc a b)) := by
    intro i hi
    have heq : (K.space ×ˢ {a}) ∩ (A i ×ˢ Icc a b) = A i ×ˢ {a} := by
      ext x
      constructor
      · rintro ⟨hx, hxi⟩
        exact ⟨hxi.1, hx.2⟩
      · rintro ⟨hxi, hxa⟩
        exact ⟨⟨boundaryComplex_space_subset 2 K (hAB i hi hxi), hxa⟩,
          hxi, hxa.symm ▸ ⟨le_rfl, hab.le⟩⟩
    rw [heq]
    exact (hA i hi).of_isPLHomeomorphOn ((hA i hi).isPolyhedron.isPLHomeomorphOn_prod_const a)
  have h := isPLBall_union_iUnion_of_pairwiseDisjoint_in_ball hB hC subset_union_left d
    (fun i => A i ×ˢ Icc a b)
    (fun i hi => isPLBall_two_prod (hA i hi) (isPLBall_Icc hab))
    (fun i hi => (prod_mono (hAB i hi) Subset.rfl).trans subset_union_right) hI
    (fun i hi j hj hij => disjoint_left.mpr fun _ hxi hxj =>
      disjoint_left.mp (hdis i hi j hj hij) hxi.1 hxj.1)
  have heq : (⋃ i ∈ d, A i ×ˢ Icc a b) = (⋃ i ∈ d, A i) ×ˢ Icc a b := by
    ext x
    simp only [mem_iUnion, mem_prod]
    aesop
  rwa [heq] at h

open Classical in
theorem isPLBall_prism_bottom_union_strips {ι : Type*}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {a b : ℝ} (hab : a < b) (d : Finset ι) (A : ι → Set E)
    (hA : ∀ i ∈ d, IsPLBall 1 (A i))
    (hAB : ∀ i ∈ d, A i ⊆ (boundaryComplex 2 K).space) :
    IsPLBall 2 (K.space ×ˢ {a} ∪ (⋃ i ∈ d, A i) ×ˢ Icc a b) := by
  have hS := isPLSphere_boundaryComplex_space_of_isPLBall K hK
  rcases hS.eq_or_exists_disjoint_arc_cover d A hA hAB with hfull | ⟨c, hC, hCB, hdis, hcover⟩
  · rw [hfull]
    exact isPLBall_prism_bottom_union_side K hK hab
  · rw [← hcover]
    exact isPLBall_prism_bottom_union_strips_of_pairwiseDisjoint K hK hab c id hC hCB hdis
end DifferentialGeometry.Topology.PiecewiseLinear
