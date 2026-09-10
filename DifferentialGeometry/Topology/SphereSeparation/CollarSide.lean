import DifferentialGeometry.Topology.SphereSeparation.LocalSides
import DifferentialGeometry.Topology.VanKampen.TwoSidedCollarSeparation

noncomputable section
open Set Topology

namespace Poincare.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type*} [TopologicalSpace B] [ConnectedSpace B] [TopologicalSpace X]
  {e : B → X}

theorem range_subset_domain_union_compactSide
    (c : TwoSidedCollar e) (d : Poincare.Topology.SphereSeparation.SphereSides (Set.range e))
    {K : Set X} (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hinterior : interior K ⊆ d.endSide) : c.range ⊆ K ∪ d.compactSide := by
  let N := c.toFun '' ((univ : Set B) ×ˢ Iio (0 : ℝ))
  let P := c.toFun '' ((univ : Set B) ×ˢ Ioi (0 : ℝ))
  have hN : IsConnected N :=
    (isConnected_univ.prod isConnected_Iio).image _ c.isOpenEmbedding_toFun.continuous.continuousOn
  have hP : IsConnected P :=
    (isConnected_univ.prod isConnected_Ioi).image _ c.isOpenEmbedding_toFun.continuous.continuousOn
  have hNopen : IsOpen N := c.isOpenEmbedding_toFun.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
  have hNK : N ⊆ K := by
    rintro x ⟨p, hp, rfl⟩
    exact (hside p).mpr hp.2.le
  have hNE : N ⊆ d.endSide := by
    apply Set.Subset.trans _ hinterior
    simpa only [hNopen.interior_eq] using interior_mono hNK
  have havoid (p : B × ℝ) (hp : p.2 ≠ 0) : c.toFun p ∉ Set.range e := by
    rintro ⟨b, hb⟩
    have heq := c.isOpenEmbedding_toFun.injective (hb.symm.trans (c.zero_eq b).symm)
    exact hp (congrArg Prod.snd heq)
  have hNS : N ⊆ (Set.range e)ᶜ := by
    rintro x ⟨p, hp, rfl⟩
    exact havoid p hp.2.ne
  have hPS : P ⊆ (Set.range e)ᶜ := by
    rintro x ⟨p, hp, rfl⟩
    exact havoid p hp.2.ne'
  have hSrange : Set.range e ⊆ c.range := by
    rintro x ⟨b, rfl⟩
    exact ⟨(b, 0), c.zero_eq b⟩
  have hcover : c.range ⊆ (N ∪ Set.range e) ∪ P := by
    rintro x ⟨⟨b, t⟩, rfl⟩
    rcases lt_trichotomy t 0 with ht | ht | ht
    · exact Or.inl (Or.inl ⟨(b, t), ⟨mem_univ _, ht⟩, rfl⟩)
    · subst t
      exact Or.inl (Or.inr ⟨b, (c.zero_eq b).symm⟩)
    · exact Or.inr ⟨(b, t), ⟨mem_univ _, ht⟩, rfl⟩
  have hS : (Set.range e).Nonempty := Set.range_nonempty e
  have hPC : P ⊆ d.compactSide := by
    rcases d.neighborhood_halves_opposite hS hN hP hNS hPS c.isOpen_range hSrange hcover with h | h
    · obtain ⟨x, hx⟩ := hN.nonempty
      exact False.elim (d.disjoint.le_bot ⟨h.1.1 hx, hNE hx⟩)
    · exact h.1.2
  rintro x ⟨p, rfl⟩
  by_cases hp : p.2 ≤ 0
  · exact Or.inl ((hside p).mpr hp)
  · exact Or.inr (hPC ⟨p, ⟨mem_univ _, lt_of_not_ge hp⟩, rfl⟩)

end Poincare.Topology.ThreeManifold.TwoSidedCollar
