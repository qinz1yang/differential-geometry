import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.Real

open Set Topology

namespace Poincare.Topology

private theorem frontier_subset_inter_of_closed_cover
    {W : Type*} [TopologicalSpace W] {L R : Set W}
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = univ) :
    frontier L ⊆ L ∩ R := by
  intro x hx
  refine ⟨hL.frontier_subset hx, ?_⟩
  by_contra hxR
  have hsub : Rᶜ ⊆ L := by
    intro y hy
    have hmem : y ∈ L ∪ R := hcover.symm ▸ mem_univ y
    exact hmem.resolve_right hy
  have hnb : L ∈ 𝓝 x := Filter.mem_of_superset (hR.isOpen_compl.mem_nhds hxR) hsub
  exact hx.2 (mem_interior_iff_mem_nhds.mpr hnb)

theorem closed_sides_of_embedded_collar
    {N W : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace W] [T2Space W]
    (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (e : N × Icc a b → W) (he : Continuous e) (hinj : Function.Injective e)
    (P Q : Set W) (hP : IsClosed P) (hQ : IsClosed Q) (hPQ : Disjoint P Q)
    (hcover : P ∪ range e ∪ Q = univ)
    (hleft : P ∩ range e ⊆ range (fun p : N ↦ e (p, ⟨a, le_rfl, (hac.trans hcb).le⟩)))
    (hright : Q ∩ range e ⊆ range (fun p : N ↦ e (p, ⟨b, (hac.trans hcb).le, le_rfl⟩))) :
    let L := P ∪ e '' {x | (x.2 : ℝ) ≤ c}
    let R := e '' {x | c ≤ (x.2 : ℝ)} ∪ Q
    let S := range (fun p : N ↦ e (p, ⟨c, hac.le, hcb.le⟩))
    IsClosed L ∧ IsClosed R ∧ L ∪ R = univ ∧ L ∩ R = S ∧
      frontier L ⊆ S ∧ frontier R ⊆ S ∧
      e ⁻¹' L = {x | (x.2 : ℝ) ≤ c} ∧ e ⁻¹' R = {x | c ≤ (x.2 : ℝ)} := by
  dsimp only
  let L := P ∪ e '' {x | (x.2 : ℝ) ≤ c}
  let R := e '' {x | c ≤ (x.2 : ℝ)} ∪ Q
  let S := range (fun p : N ↦ e (p, ⟨c, hac.le, hcb.le⟩))
  have hL : IsClosed L := hP.union
    (((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image he).isClosed
  have hR : IsClosed R :=
    (((isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).isCompact).image he).isClosed.union hQ
  have heP (x : N × Icc a b) (hx : e x ∈ P) : (x.2 : ℝ) = a := by
    obtain ⟨p, hp⟩ := hleft ⟨hx, mem_range_self x⟩
    have heq := hinj hp
    have ht := congrArg (fun y : N × Icc a b ↦ (y.2 : ℝ)) heq
    exact ht.symm
  have heQ (x : N × Icc a b) (hx : e x ∈ Q) : (x.2 : ℝ) = b := by
    obtain ⟨p, hp⟩ := hright ⟨hx, mem_range_self x⟩
    have heq := hinj hp
    have ht := congrArg (fun y : N × Icc a b ↦ (y.2 : ℝ)) heq
    exact ht.symm
  have hpreL : e ⁻¹' L = {x | (x.2 : ℝ) ≤ c} := by
    ext x
    change (e x ∈ P ∨ e x ∈ e '' {y | (y.2 : ℝ) ≤ c}) ↔ (x.2 : ℝ) ≤ c
    constructor
    · rintro (hx | ⟨y, hy, hyx⟩)
      · rw [heP x hx]
        exact hac.le
      · exact (hinj hyx) ▸ hy
    · intro hx
      exact Or.inr ⟨x, hx, rfl⟩
  have hpreR : e ⁻¹' R = {x | c ≤ (x.2 : ℝ)} := by
    ext x
    change (e x ∈ e '' {y | c ≤ (y.2 : ℝ)} ∨ e x ∈ Q) ↔ c ≤ (x.2 : ℝ)
    constructor
    · rintro (⟨y, hy, hyx⟩ | hx)
      · exact (hinj hyx) ▸ hy
      · rw [heQ x hx]
        exact hcb.le
    · intro hx
      exact Or.inl ⟨x, hx, rfl⟩
  have hLR : L ∪ R = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ P ∪ range e ∪ Q := hcover.symm ▸ mem_univ x
    rcases hx with (hp | ⟨y, rfl⟩) | hq
    · exact Or.inl (Or.inl hp)
    · rcases le_total (y.2 : ℝ) c with h | h
      · exact Or.inl (Or.inr ⟨y, h, rfl⟩)
      · exact Or.inr (Or.inl ⟨y, h, rfl⟩)
    · exact Or.inr (Or.inr hq)
  have hinter : L ∩ R = S := by
    ext x
    constructor
    · rintro ⟨hxL, hxR⟩
      have hxrange : x ∈ range e := by
        rcases hxL with hp | ⟨y, _, hy⟩
        · rcases hxR with ⟨y, _, hy⟩ | hq
          · exact ⟨y, hy⟩
          · exact False.elim (Set.disjoint_left.mp hPQ hp hq)
        · exact ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hxrange
      have hlo : y ∈ e ⁻¹' L := hxL
      rw [hpreL] at hlo
      have hhi : y ∈ e ⁻¹' R := hxR
      rw [hpreR] at hhi
      refine ⟨y.1, congrArg e (Prod.ext rfl ?_)⟩
      exact Subtype.ext (le_antisymm hlo hhi).symm
    · rintro ⟨p, rfl⟩
      refine ⟨Or.inr ⟨(p, ⟨c, hac.le, hcb.le⟩), ?_, rfl⟩,
        Or.inl ⟨(p, ⟨c, hac.le, hcb.le⟩), ?_, rfl⟩⟩ <;>
        exact (show c ≤ c from le_rfl)
  refine ⟨hL, hR, hLR, hinter, ?_, ?_, hpreL, hpreR⟩
  · exact (frontier_subset_inter_of_closed_cover hL hR hLR).trans_eq hinter
  · exact (frontier_subset_inter_of_closed_cover hR hL (union_comm L R ▸ hLR)).trans_eq
      ((inter_comm R L).trans hinter)

end Poincare.Topology
