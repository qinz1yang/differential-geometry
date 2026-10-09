import DifferentialGeometry.Topology.LocallyFinite.Frontier
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.DenselyOrdered
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] (T : TubeSystem M)

theorem isCompact_closedBand (a : T.Index) :
    IsCompact (T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) := by
  apply IsCompact.image _ (T.tube a).continuous
  apply IsClosed.isCompact
  exact (isClosed_le continuous_const continuous_snd.subtype_val).inter
    (isClosed_le continuous_snd.subtype_val continuous_const)

theorem isCompact_iUnion_closedBand :
    IsCompact (⋃ a, T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) :=
  isCompact_iUnion T.isCompact_closedBand

private theorem closedBand_eq_image_slab (a : T.Index) (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    (hmap : ∀ q : TubeDomain, (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1 →
      T.tube a q = e (q.1, q.2.val)) :
    T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1} =
      e '' (univ ×ˢ Icc (-1 : ℝ) 1) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(q.1, q.2.val), ⟨mem_univ _, hq⟩, (hmap q hq).symm⟩
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    refine ⟨(q, ⟨t, ?_⟩), ht, hmap _ ht⟩
    constructor <;> linarith [ht.1, ht.2]

theorem boundarySphere_mem_iUnion_closedBand (b : T.Boundary) (z : Sphere 2) :
    T.boundarySphere b z ∈ ⋃ a, T.tube a ''
      {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1} := by
  refine mem_iUnion.mpr ⟨b.1, (z, boundaryLevel b.2), ?_, rfl⟩
  cases b with
  | mk a side => cases side <;> norm_num [boundaryLevel]

theorem iUnion_closedBand_inter_core :
    (⋃ a, T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) ∩ T.core =
      ⋃ b : T.Boundary, range (T.boundarySphere b) := by
  ext x
  constructor
  · rintro ⟨hx, hxcore⟩
    obtain ⟨a, q, hq, rfl⟩ := mem_iUnion.mp hx
    have hnot : ¬ ((-1 : ℝ) < q.2.val ∧ q.2.val < 1) := by
      intro h
      exact hxcore (mem_iUnion.mpr ⟨a, q, h, rfl⟩)
    have hends : q.2.val = -1 ∨ q.2.val = 1 := by
      rcases le_or_gt q.2.val (-1) with h | h
      · exact Or.inl (le_antisymm h hq.1)
      · exact Or.inr (le_antisymm hq.2 (not_lt.mp (fun hh => hnot ⟨h,hh⟩)))
    rcases hends with h | h
    · refine mem_iUnion.mpr ⟨(a, false), q.1, ?_⟩
      apply congrArg (T.tube a)
      exact Prod.ext rfl (Subtype.ext (by simpa [boundaryLevel] using h.symm))
    · refine mem_iUnion.mpr ⟨(a, true), q.1, ?_⟩
      apply congrArg (T.tube a)
      exact Prod.ext rfl (Subtype.ext (by simpa [boundaryLevel] using h.symm))
  · intro hx
    obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hx
    exact ⟨T.boundarySphere_mem_iUnion_closedBand b z, T.boundarySphere_mem_core b z⟩

variable [T2Space M]

theorem closure_interior_closedBand_of_openPartialHomeomorph (a : T.Index) (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    (hsource : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ e.source)
    (hmap : ∀ q : TubeDomain, (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1 →
      T.tube a q = e (q.1, q.2.val)) :
    closure (interior (T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1})) =
      T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1} := by
  rw [T.closedBand_eq_image_slab a e hmap]
  apply e.closure_interior_image_of_subset_source hsource
  · rw [interior_prod_eq, interior_univ, interior_Icc, closure_prod_eq,
      closure_univ, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  · rw [← T.closedBand_eq_image_slab a e hmap]
    exact (T.isCompact_closedBand a).isClosed

theorem frontier_closedBand_of_openPartialHomeomorph (a : T.Index) (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    (hsource : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ e.source)
    (hmap : ∀ q : TubeDomain, (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1 →
      T.tube a q = e (q.1, q.2.val)) :
    frontier (T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) =
      range (T.boundarySphere (a, false)) ∪ range (T.boundarySphere (a, true)) := by
  have hc : IsClosed (e '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
    rw [← T.closedBand_eq_image_slab a e hmap]
    exact (T.isCompact_closedBand a).isClosed
  have hf := e.image_frontier_of_subset_source hsource (isClosed_univ.prod isClosed_Icc) hc
  rw [frontier_univ_prod_eq, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hf
  rw [T.closedBand_eq_image_slab a e hmap, ← hf]
  have heq (q : Sphere 2) (b : Bool) :
      T.boundarySphere (a, b) q = e (q, (boundaryLevel b).val) := by
    apply hmap
    cases b <;> norm_num [boundaryLevel]
  ext y
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with rfl | rfl
    · exact Or.inl ⟨q, heq q false⟩
    · exact Or.inr ⟨q, heq q true⟩
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨(q, -1), ⟨mem_univ _, Or.inl rfl⟩, (heq q false).symm⟩
    · exact ⟨(q, 1), ⟨mem_univ _, Or.inr rfl⟩, (heq q true).symm⟩

theorem closure_interior_iUnion_closedBand_of_openPartialHomeomorph
    (e : T.Index → OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    (hsource : ∀ a, univ ×ˢ Icc (-1 : ℝ) 1 ⊆ (e a).source)
    (hmap : ∀ a (q : TubeDomain), (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1 →
      T.tube a q = e a (q.1, q.2.val)) :
    closure (interior (⋃ a, T.tube a ''
      {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1})) =
      ⋃ a, T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1} :=
  T.isCompact_iUnion_closedBand.isClosed.closure_interior_iUnion
    (fun a => T.closure_interior_closedBand_of_openPartialHomeomorph a (e a) (hsource a) (hmap a))

theorem frontier_iUnion_closedBand_of_openPartialHomeomorph
    (e : T.Index → OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    (hsource : ∀ a, univ ×ˢ Icc (-1 : ℝ) 1 ⊆ (e a).source)
    (hmap : ∀ a (q : TubeDomain), (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1 →
      T.tube a q = e a (q.1, q.2.val)) :
    frontier (⋃ a, T.tube a '' {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}) =
      ⋃ b : T.Boundary, range (T.boundarySphere b) := by
  let K : T.Index → Set M := fun a => T.tube a ''
    {q : TubeDomain | (-1 : ℝ) ≤ q.2.val ∧ q.2.val ≤ 1}
  have hc (a : T.Index) : IsClosed (K a) := (T.isCompact_closedBand a).isClosed
  have hd : Pairwise (fun a b => Disjoint (closure (K a)) (closure (K b))) := by
    intro a b hab
    rw [(hc a).closure_eq, (hc b).closure_eq]
    exact (T.disjoint hab).mono (image_subset_range _ _) (image_subset_range _ _)
  change frontier (⋃ a, K a) = _
  rw [(locallyFinite_of_finite K).frontier_iUnion_of_disjoint_closure hd]
  have hf (a : T.Index) : frontier (K a) =
      range (T.boundarySphere (a, false)) ∪ range (T.boundarySphere (a, true)) :=
    T.frontier_closedBand_of_openPartialHomeomorph a (e a) (hsource a) (hmap a)
  simp only [hf]
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := mem_iUnion.mp hy
    rcases ha with ha | ha
    · exact mem_iUnion.mpr ⟨(a, false), ha⟩
    · exact mem_iUnion.mpr ⟨(a, true), ha⟩
  · intro hy
    obtain ⟨⟨a, b⟩, ha⟩ := mem_iUnion.mp hy
    apply mem_iUnion.mpr
    cases b
    · exact ⟨a, Or.inl ha⟩
    · exact ⟨a, Or.inr ha⟩

omit [T2Space M] in
theorem boundarySphere_eq_iff (b c : T.Boundary) (z w : Sphere 2) :
    T.boundarySphere b z = T.boundarySphere c w ↔ b = c ∧ z = w := by
  constructor
  · intro h
    have hi : b.1 = c.1 := by
      by_contra hn
      exact (disjoint_left.mp (T.disjoint hn))
        (mem_range_self (z,boundaryLevel b.2)) ⟨(w,boundaryLevel c.2),h.symm⟩
    have he : T.tube c.1 (z,boundaryLevel b.2) = T.tube c.1 (w,boundaryLevel c.2) := by
      change T.tube b.1 (z,boundaryLevel b.2) = _ at h
      rwa [hi] at h
    have hzw := (T.embedding c.1).injective he
    have ht := congrArg (fun p : TubeDomain => p.2.val) hzw
    have hs : b.2 = c.2 := by
      cases hb : b.2 <;> cases hc : c.2
      · rfl
      · norm_num [boundaryLevel,hb,hc] at ht
      · norm_num [boundaryLevel,hb,hc] at ht
      · rfl
    exact ⟨Prod.ext hi hs,congrArg Prod.fst hzw⟩
  · rintro ⟨rfl,rfl⟩
    rfl

omit [T2Space M] in
theorem pairwise_disjoint_range_boundarySphere :
    Pairwise (fun b c : T.Boundary => Disjoint (range (T.boundarySphere b))
      (range (T.boundarySphere c))) := by
  intro b c hbc
  rw [disjoint_left]
  rintro x ⟨z,hz⟩ ⟨w,hw⟩
  exact hbc ((T.boundarySphere_eq_iff b c z w).mp (hz.trans hw.symm)).1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem
