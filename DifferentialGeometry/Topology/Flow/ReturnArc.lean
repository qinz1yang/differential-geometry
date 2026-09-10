import DifferentialGeometry.Topology.Flow.TransverseReturns

open Set

namespace Poincare.Topology.Flow

theorem disjoint_returnArc_flowBox_strip
    {X : Type*} [TopologicalSpace X] (φ : _root_.Flow ℝ X)
    {σ : ℝ → X} {ε a b T : ℝ} (e : OpenPartialHomeomorph (ℝ × ℝ) X)
    (hsource : e.source = Ioo (-ε) ε ×ˢ Ioo (-ε) ε)
    (he : ∀ p, e p = φ p.2 (σ p.1))
    (ha : a ∈ Ioo (-ε) ε) (hb : b ∈ Ioo (-ε) ε)
    (hreturn : φ T (σ a) = σ b)
    (havoid : ∀ t ∈ Ioo 0 T, φ t (σ a) ∉ σ '' uIcc a b) :
    Disjoint (e '' (Ioo (min a b) (max a b) ×ˢ Ioo (-ε) ε))
      ((fun t ↦ φ t (σ a)) '' Icc 0 T) := by
  apply disjoint_left.mpr
  rintro z ⟨⟨u, r⟩, ⟨hu, hr⟩, rfl⟩ ⟨t, ht, hte⟩
  change φ t (σ a) = e (u, r) at hte
  have huε : u ∈ Ioo (-ε) ε :=
    ⟨(lt_min ha.1 hb.1).trans hu.1, hu.2.trans (max_lt ha.2 hb.2)⟩
  have hua : u ≠ a := by
    rcases le_total a b with hab | hba
    · exact (show a < u by simpa only [min_eq_left hab] using hu.1).ne'
    · exact (show u < a by simpa only [max_eq_left hba] using hu.2).ne
  have hub : u ≠ b := by
    rcases le_total a b with hab | hba
    · exact (show u < b by simpa only [max_eq_right hab] using hu.2).ne
    · exact (show b < u by simpa only [min_eq_right hba] using hu.1).ne'
  have hpair {v s : ℝ} (hv : v ∈ Ioo (-ε) ε) (hs : s ∈ Ioo (-ε) ε) :
      (v, s) ∈ e.source := by rw [hsource]; exact ⟨hv, hs⟩
  have hε : 0 < ε := by linarith [ha.1, ha.2]
  have hhit : φ (t - r) (σ a) = σ u := by
    calc
      φ (t - r) (σ a) = φ (-r) (φ t (σ a)) := by
        rw [← φ.map_add]; congr 1; ring
      _ = φ (-r) (φ r (σ u)) := by rw [hte, he]
      _ = σ u := by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  by_cases hleft : t - r ≤ 0
  · have htε : t ∈ Ioo (-ε) ε := by constructor <;> linarith [ht.1, hr.2]
    have hp := e.injOn (hpair ha htε) (hpair huε hr)
      ((he (a, t)).trans hte)
    exact hua (congrArg Prod.fst hp).symm
  by_cases hright : T ≤ t - r
  · have htε : t - T ∈ Ioo (-ε) ε := by
      constructor <;> linarith [ht.2, hr.1]
    have hbe : e (b, t - T) = e (u, r) := by
      rw [he, ← hreturn, ← φ.map_add, sub_add_cancel]
      exact hte
    have hp := e.injOn (hpair hb htε) (hpair huε hr) hbe
    exact hub (congrArg Prod.fst hp).symm
  apply havoid (t - r) ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
  exact ⟨u, ⟨hu.1.le, hu.2.le⟩, hhit.symm⟩

end Poincare.Topology.Flow
