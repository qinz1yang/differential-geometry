import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Topology.Compactness.Compact

open scoped ContDiff Manifold

namespace Diffeomorph

theorem exists_isotopy_of_finite_disjoint_support
    {ι : Type*} {E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ι → Set E) (H : ι → ℝ → (E ≃ₘ[ℝ] E))
    (hH : ∀ i, ContDiff ℝ ∞ (fun z : ℝ × E => H i z.1 z.2))
    (hi : ∀ i, ContDiff ℝ ∞ (fun z : ℝ × E => (H i z.1).symm z.2))
    (hzero : ∀ i, H i 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞)
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j))
    (hfix : ∀ i t, Set.EqOn (H i t) id (K i)ᶜ) :
    ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t, Set.EqOn (Φ t) id (⋃ i, K i)ᶜ ∧
        Set.EqOn (Φ t).symm id (⋃ i, K i)ᶜ) ∧
      ∀ i t, Set.EqOn (Φ t) (H i t) (K i) ∧
        Set.EqOn (Φ t).symm (H i t).symm (K i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      (∀ t, Set.EqOn (Φ t) id (⋃ i ∈ s, K i)ᶜ) ∧
      ∀ i ∈ s, ∀ t, Set.EqOn (Φ t) (H i t) (K i) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, E) E ∞,
        contDiff_snd, contDiff_snd, rfl, fun _ _ _ => rfl, ?_⟩
      intro i hi
      exact False.elim (Finset.notMem_empty i hi)
    | @insert i s his ih =>
      obtain ⟨G, hG, hGi, hGzero, hGfix, hGeq⟩ := ih
      have hKiS {x : E} (hx : x ∈ K i) : x ∉ ⋃ j ∈ s, K j := by
        intro hxs
        obtain ⟨j, hjs, hxj⟩ := Set.mem_iUnion₂.mp hxs
        have hij : i ≠ j := by
          intro hij
          subst j
          exact his hjs
        exact Set.disjoint_left.mp (hdisj hij) hx hxj
      have hdis (t : ℝ) : Equiv.Perm.Disjoint (H i t).toEquiv (G t).toEquiv := by
        intro x
        by_cases hx : x ∈ K i
        · exact Or.inr (hGfix t (hKiS hx))
        · exact Or.inl (hfix i t hx)
      have hcomm (t : ℝ) (x : E) : G t (H i t x) = H i t (G t x) :=
        congrArg (fun f : Equiv.Perm E => f x) ((hdis t).commute.eq.symm)
      let Φ : ℝ → (E ≃ₘ[ℝ] E) := fun t => (H i t).trans (G t)
      have hΦ : ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) :=
        hG.comp (contDiff_fst.prodMk (hH i))
      have hΦi : ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) :=
        (hi i).comp (contDiff_fst.prodMk hGi)
      refine ⟨Φ, hΦ, hΦi, ?_, ?_, ?_⟩
      · change (H i 0).trans (G 0) = Diffeomorph.refl 𝓘(ℝ, E) E ∞
        rw [hzero i, hGzero, Diffeomorph.refl_trans]
      · intro t x hx
        have hxi : x ∉ K i := fun h => hx
          (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_self i s, h⟩)
        have hxs : x ∉ ⋃ j ∈ s, K j := by
          intro h
          obtain ⟨j, hjs, hxj⟩ := Set.mem_iUnion₂.mp h
          exact hx (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_insert_of_mem hjs, hxj⟩)
        change G t (H i t x) = x
        rw [hfix i t hxi, id_eq]
        exact hGfix t hxs
      · intro j hjs t x hx
        rcases Finset.mem_insert.mp hjs with hji | hjs
        · subst j
          change G t (H i t x) = H i t x
          rw [hcomm t x, hGfix t (hKiS hx), id_eq]
        · have hji : j ≠ i := by
            intro hji
            subst j
            exact his hjs
          have hxi : x ∉ K i := fun h =>
            Set.disjoint_left.mp (hdisj hji) hx h
          change G t (H i t x) = H j t x
          rw [hfix i t hxi, id_eq]
          exact hGeq j hjs t hx
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦfix, hΦeq⟩ := aux Finset.univ
  have hfixall (t : ℝ) : Set.EqOn (Φ t) id (⋃ i, K i)ᶜ := by
    intro x hx
    apply hΦfix t
    intro h
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp h
    exact hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
  have heqall (i : ι) (t : ℝ) : Set.EqOn (Φ t) (H i t) (K i) :=
    hΦeq i (Finset.mem_univ i) t
  refine ⟨Φ, hΦ, hΦi, hΦzero, ?_, ?_⟩
  · intro t
    refine ⟨hfixall t, ?_⟩
    intro x hx
    have h := congrArg (Φ t).symm (hfixall t hx)
    simpa only [Diffeomorph.symm_apply_apply, id_eq] using h.symm
  · intro i t
    refine ⟨heqall i t, ?_⟩
    intro x hx
    have hxi : (H i t).symm x ∈ K i := by
      by_contra hn
      have h : x = (H i t).symm x := by
        simpa only [Diffeomorph.apply_symm_apply, id_eq] using hfix i t hn
      exact hn (h ▸ hx)
    apply (Φ t).injective
    change Φ t ((Φ t).symm x) = Φ t ((H i t).symm x)
    rw [(Φ t).apply_symm_apply]
    exact ((heqall i t hxi).trans ((H i t).apply_symm_apply x)).symm

theorem exists_isotopy_of_finite_disjoint_compact_support
    {ι : Type*} {E : Type*} [Finite ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C K : ι → Set E) (H : ι → ℝ → (E ≃ₘ[ℝ] E))
    (hC : ∀ i, IsCompact (C i)) (hCK : ∀ i, C i ⊆ K i)
    (hH : ∀ i, ContDiff ℝ ∞ (fun z : ℝ × E => H i z.1 z.2))
    (hi : ∀ i, ContDiff ℝ ∞ (fun z : ℝ × E => (H i z.1).symm z.2))
    (hzero : ∀ i, H i 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞)
    (hdisj : Pairwise fun i j => Disjoint (K i) (K j))
    (hfix : ∀ i t, Set.EqOn (H i t) id (C i)ᶜ) :
    ∃ Φ : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun z : ℝ × E => Φ z.1 z.2) ∧
      ContDiff ℝ ∞ (fun z : ℝ × E => (Φ z.1).symm z.2) ∧
      Φ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧ IsCompact (⋃ i, C i) ∧
      (∀ t, Set.EqOn (Φ t) id (⋃ i, C i)ᶜ ∧
        Set.EqOn (Φ t).symm id (⋃ i, C i)ᶜ) ∧
      ∀ i t, Set.EqOn (Φ t) (H i t) (K i) ∧
        Set.EqOn (Φ t).symm (H i t).symm (K i) := by
  classical
  have hfixK (i : ι) (t : ℝ) : Set.EqOn (H i t) id (K i)ᶜ :=
    fun _ hx => hfix i t (fun hc => hx (hCK i hc))
  obtain ⟨Φ, hΦ, hΦi, hΦzero, hΦfix, hΦeq⟩ :=
    exists_isotopy_of_finite_disjoint_support K H hH hi hzero hdisj hfixK
  have hfixC (t : ℝ) : Set.EqOn (Φ t) id (⋃ i, C i)ᶜ := by
    intro x hx
    by_cases hK : x ∈ ⋃ i, K i
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hK
      calc
        Φ t x = H i t x := (hΦeq i t).1 hxi
        _ = x := hfix i t (fun hc => hx (Set.mem_iUnion.mpr ⟨i, hc⟩))
    · exact (hΦfix t).1 hK
  refine ⟨Φ, hΦ, hΦi, hΦzero, isCompact_iUnion hC, ?_, hΦeq⟩
  intro t
  refine ⟨hfixC t, ?_⟩
  intro x hx
  have h := congrArg (Φ t).symm (hfixC t hx)
  simpa only [Diffeomorph.symm_apply_apply, id_eq] using h.symm

end Diffeomorph
