import DifferentialGeometry.Topology.Connected.Frontier
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Set Topology

namespace DifferentialGeometry.Topology

private theorem isConnected_cylinder_interval_image
    {Y X : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [TopologicalSpace X]
    {f : Y × Icc (0 : ℝ) 1 → X} (hf : Continuous f) {I : Set ℝ}
    (hI : IsConnected I) (hI01 : I ⊆ Icc (0 : ℝ) 1) :
    IsConnected (f '' {p | (p.2 : ℝ) ∈ I}) := by
  have : ConnectedSpace I := isConnected_iff_connectedSpace.mp hI
  let g : Y × I → X := fun p => f (p.1, ⟨p.2, hI01 p.2.2⟩)
  have hg : Continuous g := by fun_prop
  have he : range g = f '' {p | (p.2 : ℝ) ∈ I} := by
    apply Subset.antisymm
    · rintro x ⟨p, rfl⟩
      exact ⟨(p.1, ⟨p.2, hI01 p.2.2⟩), p.2.2, rfl⟩
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨(p.1, ⟨p.2, hp⟩), rfl⟩
  exact he ▸ isConnected_range hg

theorem continuous_cylinder_frontier_sides
    {Y X : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [TopologicalSpace X]
    {f : Y × Icc (0 : ℝ) 1 → X} (hf : Continuous f) {D : Set X} (hD : IsClosed D)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hfront : ∀ p, f p ∈ frontier D ↔ (p.2 : ℝ) = t)
    (hin : ∃ p, f p ∈ interior D) (hout : ∃ p, f p ∉ D) :
    ((∀ p, f p ∈ interior D ↔ (p.2 : ℝ) < t) ∧
      (∀ p, f p ∈ D ↔ (p.2 : ℝ) ≤ t)) ∨
    ((∀ p, f p ∈ interior D ↔ t < (p.2 : ℝ)) ∧
      ∀ p, f p ∈ D ↔ t ≤ (p.2 : ℝ)) := by
  let L := f '' {p | (p.2 : ℝ) < t}
  let R := f '' {p | t < (p.2 : ℝ)}
  have hL : IsConnected L := by
    change IsConnected (f '' {p | (p.2 : ℝ) < t})
    convert isConnected_cylinder_interval_image hf (isConnected_Ico ht.1)
      (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.le)) using 1
    congr 1
    ext p
    exact ⟨fun hp => ⟨p.2.2.1, hp⟩, fun hp => hp.2⟩
  have hR : IsConnected R := by
    change IsConnected (f '' {p | t < (p.2 : ℝ)})
    convert isConnected_cylinder_interval_image hf (isConnected_Ioc ht.2)
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1.le le_rfl)) using 1
    congr 1
    ext p
    exact ⟨fun hp => ⟨hp, p.2.2.2⟩, fun hp => hp.1⟩
  have hLf : Disjoint L (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ hpf
    exact hp.ne ((hfront p).mp hpf)
  have hRf : Disjoint R (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ hpf
    exact hp.ne' ((hfront p).mp hpf)
  have hside (B : Set X) (hB : IsPreconnected B) (hBf : Disjoint B (frontier D)) :
      B ⊆ interior D ∨ B ⊆ Dᶜ := by
    by_cases hmeet : (B ∩ interior D).Nonempty
    · exact Or.inl (subset_interior_of_isPreconnected_of_disjoint_frontier hB hBf hmeet)
    · right
      intro x hxB hxD
      apply disjoint_left.mp hBf hxB
      rw [hD.frontier_eq]
      exact ⟨hxD, fun hxI => hmeet ⟨x, hxB, hxI⟩⟩
  have hlower (hLI : L ⊆ interior D) (hRO : R ⊆ Dᶜ) (p) :
      (f p ∈ interior D ↔ (p.2 : ℝ) < t) ∧ (f p ∈ D ↔ (p.2 : ℝ) ≤ t) := by
    rcases lt_trichotomy (p.2 : ℝ) t with hp | hp | hp
    · have hi := hLI ⟨p, hp, rfl⟩
      exact ⟨iff_of_true hi hp, iff_of_true (interior_subset hi) hp.le⟩
    · have hb := (hfront p).mpr hp
      exact ⟨iff_of_false hb.2 (not_lt.mpr hp.ge), iff_of_true (hD.frontier_subset hb) hp.le⟩
    · have ho := hRO ⟨p, hp, rfl⟩
      exact ⟨iff_of_false (fun hi => ho (interior_subset hi)) (not_lt.mpr hp.le),
        iff_of_false ho (not_le.mpr hp)⟩
  have hupper (hLO : L ⊆ Dᶜ) (hRI : R ⊆ interior D) (p) :
      (f p ∈ interior D ↔ t < (p.2 : ℝ)) ∧ (f p ∈ D ↔ t ≤ (p.2 : ℝ)) := by
    rcases lt_trichotomy (p.2 : ℝ) t with hp | hp | hp
    · have ho := hLO ⟨p, hp, rfl⟩
      exact ⟨iff_of_false (fun hi => ho (interior_subset hi)) (not_lt.mpr hp.le),
        iff_of_false ho (not_le.mpr hp)⟩
    · have hb := (hfront p).mpr hp
      exact ⟨iff_of_false hb.2 (not_lt.mpr hp.le), iff_of_true (hD.frontier_subset hb) hp.ge⟩
    · have hi := hRI ⟨p, hp, rfl⟩
      exact ⟨iff_of_true hi hp, iff_of_true (interior_subset hi) hp.le⟩
  rcases hside L hL.isPreconnected hLf with hLI | hLO <;>
    rcases hside R hR.isPreconnected hRf with hRI | hRO
  · obtain ⟨p, hp⟩ := hout
    apply False.elim
    apply hp
    rcases lt_trichotomy (p.2 : ℝ) t with hl | he | hr
    · exact interior_subset (hLI ⟨p, hl, rfl⟩)
    · exact hD.frontier_subset ((hfront p).mpr he)
    · exact interior_subset (hRI ⟨p, hr, rfl⟩)
  · exact Or.inl ⟨fun p => (hlower hLI hRO p).1, fun p => (hlower hLI hRO p).2⟩
  · exact Or.inr ⟨fun p => (hupper hLO hRI p).1, fun p => (hupper hLO hRI p).2⟩
  · obtain ⟨p, hp⟩ := hin
    apply False.elim
    rcases lt_trichotomy (p.2 : ℝ) t with hl | he | hr
    · exact hLO ⟨p, hl, rfl⟩ (interior_subset hp)
    · exact ((hfront p).mpr he).2 hp
    · exact hRO ⟨p, hr, rfl⟩ (interior_subset hp)

theorem isConnected_range_inter_and_sdiff_of_frontier_level
    {Y X : Type*} [TopologicalSpace Y] [ConnectedSpace Y] [TopologicalSpace X]
    {f : Y × Icc (0 : ℝ) 1 → X} (hf : Continuous f) {D : Set X} (hD : IsClosed D)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hfront : ∀ p, f p ∈ frontier D ↔ (p.2 : ℝ) = t)
    (hin : ∃ p, f p ∈ interior D) (hout : ∃ p, f p ∉ D) :
    IsConnected (range f ∩ D) ∧ IsConnected (range f \ D) := by
  have he (Q : Set X) (I : Set ℝ) (hQI : ∀ p, f p ∈ Q ↔ (p.2 : ℝ) ∈ I) :
      range f ∩ Q = f '' {p | (p.2 : ℝ) ∈ I} := by
    apply Subset.antisymm
    · rintro x ⟨⟨p, rfl⟩, hp⟩
      exact ⟨p, (hQI p).mp hp, rfl⟩
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨mem_range_self p, (hQI p).mpr hp⟩
  rcases continuous_cylinder_frontier_sides hf hD ht hfront hin hout with ⟨-, hlow⟩ | ⟨-, hupp⟩
  · have hDI (p) : f p ∈ D ↔ (p.2 : ℝ) ∈ Icc (0 : ℝ) t := by
      rw [hlow p, mem_Icc, and_iff_right p.2.2.1]
    have hDO (p) : f p ∈ Dᶜ ↔ (p.2 : ℝ) ∈ Ioc t 1 := by
      rw [mem_compl_iff, hlow p, not_le, mem_Ioc, and_iff_left p.2.2.2]
    change IsConnected (range f ∩ D) ∧ IsConnected (range f ∩ Dᶜ)
    rw [he D _ hDI, he Dᶜ _ hDO]
    exact ⟨isConnected_cylinder_interval_image hf (isConnected_Icc ht.1.le)
      (Icc_subset_Icc le_rfl ht.2.le),
      isConnected_cylinder_interval_image hf (isConnected_Ioc ht.2)
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.1.le le_rfl))⟩
  · have hDI (p) : f p ∈ D ↔ (p.2 : ℝ) ∈ Icc t (1 : ℝ) := by
      rw [hupp p, mem_Icc, and_iff_left p.2.2.2]
    have hDO (p) : f p ∈ Dᶜ ↔ (p.2 : ℝ) ∈ Ico 0 t := by
      rw [mem_compl_iff, hupp p, not_le, mem_Ico, and_iff_right p.2.2.1]
    change IsConnected (range f ∩ D) ∧ IsConnected (range f ∩ Dᶜ)
    rw [he D _ hDI, he Dᶜ _ hDO]
    exact ⟨isConnected_cylinder_interval_image hf (isConnected_Icc ht.2.le)
      (Icc_subset_Icc ht.1.le le_rfl),
      isConnected_cylinder_interval_image hf (isConnected_Ico ht.1)
        (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.le))⟩

end DifferentialGeometry.Topology
