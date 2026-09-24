import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation
import DifferentialGeometry.Topology.Manifold.GraphBand

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y]

theorem exists_outward_closed_graph_band
    (T : OpenPartialHomeomorph (X × ℝ) Y) (f : X → ℝ) (hf : Continuous f)
    {l u : ℝ} (hlo : ∀ q, l < f q) (hhi : ∀ q, f q < u)
    (hsource : univ ×ˢ Icc l u ⊆ T.source) {K : Set Y}
    (hregular : closure (interior K) = K)
    (hfront : frontier K = range (fun q : X => T (q, f q))) :
    ∃ b : ℝ, (b = l ∨ b = u) ∧
      ∀ q : X, f q ≠ b ∧
        ∀ t ∈ Ioc (0 : ℝ) 1, T (q, f q + (b - f q) * t) ∉ K := by
  have hsrc (q : X) : (q, f q) ∈ T.source := hsource ⟨mem_univ _, (hlo q).le, (hhi q).le⟩
  obtain ⟨r, hr, hor⟩ := exists_graph_collar_orientation_of_frontier_eq_union T hf hsrc
    hregular isClosed_empty (by simpa using hfront) (disjoint_empty _)
  let q0 : X := Classical.choice inferInstance
  have hK : IsClosed K := hregular ▸ isClosed_closure
  have upper (hout : ∀ q : X, ∀ s ∈ Ioo (0 : ℝ) r,
      T (q, f q + s) ∉ K ∧ T (q, f q - s) ∈ interior K) :
      ∀ q : X, f q ≠ u ∧ ∀ t ∈ Ioc (0 : ℝ) 1, T (q, f q + (u - f q) * t) ∉ K := by
    let A := T '' {z : X × ℝ | f z.1 < z.2 ∧ z.2 ≤ u}
    have hAs : {z : X × ℝ | f z.1 < z.2 ∧ z.2 ≤ u} ⊆ T.source :=
      fun z hz => hsource ⟨mem_univ _, (hlo z.1).le.trans hz.1.le, hz.2⟩
    have hconn : IsPreconnected A := by
      have hh : IsPreconnected {z : X × ℝ | f z.1 < z.2 ∧ z.2 ≤ u} := by
        apply (isPreconnected_openGraphBand f (fun _ => u) hf continuous_const hhi).subset_closure
        · exact fun z hz => ⟨hz.1, hz.2.le⟩
        · rw [closure_openGraphBand f (fun _ => u) hf continuous_const hhi]
          exact fun z hz => ⟨hz.1.le, hz.2⟩
      exact hh.image T (T.continuousOn.mono hAs)
    have hdis : Disjoint A (frontier Kᶜ) := by
      rw [frontier_compl, hfront, disjoint_left]
      rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
      have he := T.injOn (hsrc q) (hAs hz) hq
      have hqz : q = z.1 := congrArg Prod.fst he
      have ht : f q = z.2 := congrArg Prod.snd he
      rw [hqz] at ht
      exact hz.1.ne ht
    let s := min r (u - f q0) / 2
    have hs : 0 < s := half_pos (lt_min hr (sub_pos.mpr (hhi q0)))
    have hsr : s < r := (half_lt_self (lt_min hr (sub_pos.mpr (hhi q0)))).trans_le (min_le_left _ _)
    have hsu : s < u - f q0 :=
      (half_lt_self (lt_min hr (sub_pos.mpr (hhi q0)))).trans_le (min_le_right _ _)
    have houtside : A ⊆ Kᶜ :=
      (subset_interior_of_isPreconnected_of_disjoint_frontier hconn hdis
        ⟨T (q0, f q0 + s), ⟨(q0, f q0 + s), ⟨by linarith, by linarith⟩, rfl⟩,
          hK.isOpen_compl.interior_eq.symm ▸ (hout q0 s ⟨hs, hsr⟩).1⟩).trans interior_subset
    intro q
    refine ⟨(hhi q).ne, ?_⟩
    intro t ht
    apply houtside
    refine ⟨(q, f q + (u - f q) * t), ?_, rfl⟩
    constructor <;> nlinarith [hhi q, ht.1, ht.2]
  rcases hor with hpos | hneg
  · exact ⟨u, Or.inr rfl, upper hpos⟩
  · have hnegconn : IsPreconnected (T '' {z : X × ℝ | l ≤ z.2 ∧ z.2 < f z.1}) := by
      have hh : IsPreconnected {z : X × ℝ | l ≤ z.2 ∧ z.2 < f z.1} := by
        apply (isPreconnected_openGraphBand (fun _ => l) f continuous_const hf hlo).subset_closure
        · exact fun z hz => ⟨hz.1.le, hz.2⟩
        · rw [closure_openGraphBand (fun _ => l) f continuous_const hf hlo]
          exact fun z hz => ⟨hz.1, hz.2.le⟩
      exact hh.image T (T.continuousOn.mono (fun z hz =>
        hsource ⟨mem_univ _, hz.1, hz.2.le.trans (hhi z.1).le⟩))
    have hnegs : {z : X × ℝ | l ≤ z.2 ∧ z.2 < f z.1} ⊆ T.source :=
      fun z hz => hsource ⟨mem_univ _, hz.1, hz.2.le.trans (hhi z.1).le⟩
    have hnegdis : Disjoint (T '' {z : X × ℝ | l ≤ z.2 ∧ z.2 < f z.1}) (frontier Kᶜ) := by
      rw [frontier_compl, hfront, disjoint_left]
      rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
      have he := T.injOn (hsrc q) (hnegs hz) hq
      have hqz : q = z.1 := congrArg Prod.fst he
      have ht : f q = z.2 := congrArg Prod.snd he
      rw [hqz] at ht
      exact hz.2.ne ht.symm
    let s := min r (f q0 - l) / 2
    have hs : 0 < s := half_pos (lt_min hr (sub_pos.mpr (hlo q0)))
    have hsr : s < r := (half_lt_self (lt_min hr (sub_pos.mpr (hlo q0)))).trans_le (min_le_left _ _)
    have hsl : s < f q0 - l :=
      (half_lt_self (lt_min hr (sub_pos.mpr (hlo q0)))).trans_le (min_le_right _ _)
    have houtside : T '' {z : X × ℝ | l ≤ z.2 ∧ z.2 < f z.1} ⊆ Kᶜ :=
      (subset_interior_of_isPreconnected_of_disjoint_frontier hnegconn hnegdis
        ⟨T (q0, f q0 - s), ⟨(q0, f q0 - s), ⟨by linarith, by linarith⟩, rfl⟩,
          hK.isOpen_compl.interior_eq.symm ▸ (hneg q0 s ⟨hs, hsr⟩).1⟩).trans interior_subset
    refine ⟨l, Or.inl rfl, ?_⟩
    intro q
    refine ⟨(hlo q).ne.symm, ?_⟩
    intro t ht
    apply houtside
    refine ⟨(q, f q + (l - f q) * t), ?_, rfl⟩
    constructor <;> nlinarith [hlo q, ht.1, ht.2]

end DifferentialGeometry.Topology
