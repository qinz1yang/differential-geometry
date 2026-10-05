import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic

open Set

namespace Homeomorph

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]

theorem exists_gluing_of_pairwise_disjoint (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j)) :
    ∃ g : X ≃ₜ X, (∀ i, EqOn g (f i) (U i)) ∧ EqOn g id (⋃ i, U i)ᶜ := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hmaps (i : ι) : MapsTo (f i) (U i) (U i) := by
    intro x hx
    by_contra hnot
    have heq : f i x = x := (f i).injective (hfix i hnot)
    exact hnot (heq.symm ▸ hx)
  have hfinite (d : Finset ι) : ∃ g : X ≃ₜ X,
      (∀ i ∈ d, EqOn g (f i) (U i)) ∧ EqOn g id (⋃ i ∈ d, U i)ᶜ := by
    induction d using Finset.induction_on with
    | empty => exact ⟨Homeomorph.refl X, by simp, fun _ _ => rfl⟩
    | @insert i d hid ih =>
      obtain ⟨g, hg, hgfix⟩ := ih
      refine ⟨g.trans (f i), ?_, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          have hxout : x ∉ ⋃ j ∈ d, U j := by
            intro hxunion
            obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxunion
            have hij : i ≠ j := fun heq => hid (heq.symm ▸ hj)
            exact disjoint_left.mp (hdis hij) hx hxj
          change f i (g x) = f i x
          rw [hgfix hxout]
          rfl
        · have hji : j ≠ i := fun heq => hid (heq ▸ hj)
          have hfx : f j x ∉ U i :=
            fun hi => disjoint_left.mp (hdis hji) (hmaps j hx) hi
          change f i (g x) = f j x
          rw [hg j hj hx, hfix i hfx]
          rfl
      · intro x hx
        have hxold : x ∉ ⋃ j ∈ d, U j := by
          intro hxold
          obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxold
          exact hx (mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hj, hxj⟩)
        have hxnew : x ∉ U i := fun hi => hx (mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self _ _, hi⟩)
        change f i (g x) = x
        rw [hgfix hxold, id_eq, hfix i hxnew]
        rfl
  obtain ⟨g, hg, hgfix⟩ := hfinite Finset.univ
  exact ⟨g, fun i => hg i (Finset.mem_univ i), by simpa using hgfix⟩

end Homeomorph

namespace Homeomorph

variable {X ι : Type*} [PseudoMetricSpace X] [Finite ι]

theorem exists_gluing_dist_lt (f : ι → X ≃ₜ X) (U : ι → Set X)
    (hfix : ∀ i, EqOn (f i) id (U i)ᶜ) (hdis : Pairwise fun i j => Disjoint (U i) (U j))
    {ε : X → ℝ} (hε : ∀ x, 0 < ε x) (hdist : ∀ i, ∀ x ∈ U i, dist (f i x) x < ε x) :
    ∃ g : X ≃ₜ X, (∀ i, EqOn g (f i) (U i)) ∧ EqOn g id (⋃ i, U i)ᶜ ∧
      ∀ x, dist (g x) x < ε x := by
  obtain ⟨g, hg, hgfix⟩ := exists_gluing_of_pairwise_disjoint f U hfix hdis
  refine ⟨g, hg, hgfix, ?_⟩
  intro x
  by_cases hx : x ∈ ⋃ i, U i
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hg i hi]
    exact hdist i x hi
  · rw [hgfix hx, id_eq, dist_self]
    exact hε x

end Homeomorph
