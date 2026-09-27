import DifferentialGeometry.Topology.CylinderBoundarySide
import DifferentialGeometry.Topology.Compactness.ProductChartThickening
import Mathlib.Topology.OpenPartialHomeomorph.Composition

open Set

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [PreconnectedSpace X] [TopologicalSpace Y]

theorem exists_cylinder_orientation_of_frontier_eq_union
    (T : OpenPartialHomeomorph (X × ℝ) Y)
    (hsource : ∀ q : X, (q, 0) ∈ T.source) {W S : Set Y}
    (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = range (fun q : X => T (q, 0)) ∪ S)
    (hdisjoint : Disjoint (range (fun q : X => T (q, 0))) S) :
    ∃ r > 0,
      (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, s) ∉ W ∧ T (q, -s) ∈ interior W) ∨
        (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r, T (q, -s) ∉ W ∧ T (q, s) ∈ interior W) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
    let _ := h
    exact ⟨1, zero_lt_one, Or.inl (fun q => isEmptyElim q)⟩
  | inr h =>
    let _ := h
    have hzero : univ ×ˢ Icc (0 : ℝ) 0 ⊆ T.source := by
      rintro ⟨q, t⟩ ⟨_, ht⟩
      have he : t = 0 := le_antisymm ht.2 ht.1
      subst t
      exact hsource q
    have hzeroS : T '' (univ ×ˢ Icc (0 : ℝ) 0) ⊆ Sᶜ := by
      rintro y ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ hyS
      have he : t = 0 := le_antisymm ht.2 ht.1
      subst t
      exact disjoint_left.mp hdisjoint (mem_range_self q) hyS
    obtain ⟨a, b, ha, hb, hbigSource, hbigAvoid⟩ :=
      Compactness.exists_larger_product_chart_band T le_rfl hzero hS.isOpen_compl hzeroS
    let r : ℝ := min (-a) b
    have hr : 0 < r := lt_min (neg_pos.mpr ha) hb
    have hsmall : (univ : Set X) ×ˢ Ioo (-r) r ⊆ univ ×ˢ Ioo a b := by
      rintro ⟨q, t⟩ ⟨hq, ht⟩
      refine ⟨hq, ?_, ?_⟩
      · have hle : r ≤ -a := min_le_left _ _
        linarith [ht.1]
      · exact ht.2.trans_le (min_le_right _ _)
    have hsrc : univ ×ˢ Ioo (-r) r ⊆ T.source := hsmall.trans hbigSource
    have hav : T '' (univ ×ˢ Ioo (-r) r) ⊆ Sᶜ := (image_mono hsmall).trans hbigAvoid
    refine ⟨r, hr, exists_cylinder_orientation_of_frontier_inter_image_eq T hr hsrc hregular ?_⟩
    apply subset_antisymm
    · intro y hy
      rw [hfront] at hy
      exact hy.1.resolve_right (hav hy.2)
    · rintro y ⟨q, rfl⟩
      exact ⟨hfront.symm ▸ Or.inl (mem_range_self q),
        ⟨(q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩⟩

theorem exists_graph_collar_orientation_of_frontier_eq_union
    (A : OpenPartialHomeomorph (X × ℝ) Y) {f : X → ℝ} (hf : Continuous f)
    (hsource : ∀ q : X, (q, f q) ∈ A.source) {W S : Set Y}
    (hregular : closure (interior W) = W) (hS : IsClosed S)
    (hfront : frontier W = range (fun q : X => A (q, f q)) ∪ S)
    (hdisjoint : Disjoint (range (fun q : X => A (q, f q))) S) :
    ∃ r > 0,
      (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r,
        A (q, f q + s) ∉ W ∧ A (q, f q - s) ∈ interior W) ∨
      (∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r,
        A (q, f q - s) ∉ W ∧ A (q, f q + s) ∈ interior W) := by
  let H : X × ℝ ≃ₜ X × ℝ :=
    { toFun := fun z => (z.1, f z.1 + z.2)
      invFun := fun z => (z.1, z.2 - f z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk ((hf.comp continuous_fst).add continuous_snd)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst)) }
  let T := H.transOpenPartialHomeomorph A
  have hzero (q : X) : T (q, 0) = A (q, f q) := by change A (q, f q + 0) = _; rw [add_zero]
  have hsrc (q : X) : (q, 0) ∈ T.source := by
    change (q, f q + 0) ∈ A.source
    simpa only [add_zero] using hsource q
  obtain ⟨r, hr, hor⟩ := exists_cylinder_orientation_of_frontier_eq_union T hsrc hregular hS
    (by simpa only [hzero] using hfront) (by simpa only [hzero] using hdisjoint)
  refine ⟨r, hr, ?_⟩
  have happ (q : X) (t : ℝ) : T (q, t) = A (q, f q + t) := rfl
  simpa only [happ, sub_eq_add_neg] using hor

end DifferentialGeometry.Topology
