import DifferentialGeometry.Topology.PlanarJordan.BoundaryArc
import DifferentialGeometry.Topology.PlanarJordan.CrosscutExtension

open Set

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem exists_homeomorph_image_boundary_fan {ι : Type*} (s : Finset ι)
    {C : Set Plane} {v : Plane} {p : ι → Plane} {A B : ι → Set Plane}
    (hC : IsJordanCurve C) (hv : v ∈ C) (hp : ∀ i ∈ s, p i ∈ C)
    (hA : ∀ i ∈ s, IsArcBetween (A i) v (p i))
    (hB : ∀ i ∈ s, IsArcBetween (B i) v (p i))
    (hAI : ∀ i ∈ s, A i \ {v, p i} ⊆ inside C)
    (hBI : ∀ i ∈ s, B i \ {v, p i} ⊆ inside C)
    (hAA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i ∩ A j = {v})
    (hBB : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → B i ∩ B j = {v}) :
    ∃ e : Plane ≃ₜ Plane, (∀ i ∈ s, e '' A i = B i) ∧ EqOn e id (inside C)ᶜ := by
  classical
  induction s using Finset.strongInductionOn generalizing C v p A B with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨Homeomorph.refl Plane, by simp, fun _ _ => rfl⟩
    have hpv : ∀ i ∈ s, p i ≠ v := by
      intro i hi hpi
      obtain ⟨f, _, hfi, _, hf0, hf1⟩ := hA i hi
      exact zero_ne_one (hfi zero_mem_I one_mem_I (hf0.trans (hpi.symm.trans hf1.symm)))
    have hpinj : InjOn p (s : Set ι) := by
      intro i hi j hj hpij
      by_contra hij
      have hpiv : p i = v := (hAA i hi j hj hij).subset
        ⟨(hA i hi).right_mem, hpij.symm ▸ (hA j hj).right_mem⟩
      exact hpv i hi hpiv
    let F := p '' (s : Set ι)
    have hF : IsClosed F := (s.finite_toSet.image p).isClosed
    have hCF : (C ∩ F).Nonempty := by
      obtain ⟨i, hi⟩ := hs
      exact ⟨p i, hp i hi, i, hi, rfl⟩
    have hvF : v ∉ F := by
      rintro ⟨i, hi, hpi⟩
      exact hpv i hi hpi
    obtain ⟨q, hq, L, R, hcut, hLF⟩ :=
      exists_isCutPair_inter_closed_eq_singleton hC hF hCF hv hvF
    obtain ⟨i, hi, rfl⟩ := hq
    have hpR : ∀ j ∈ s.erase i, p j ∈ R \ {v, p i} := by
      intro j hj
      obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
      have hpji : p j ≠ p i := fun heq => hji (hpinj hjs hi heq)
      have hpL : p j ∉ L := by
        intro hpL
        exact hpji (hLF.subset ⟨hpL, j, hjs, rfl⟩)
      have hpLR : p j ∈ L ∪ R := hcut.union_eq.symm ▸ hp j hjs
      refine ⟨hpLR.resolve_left hpL, ?_⟩
      rintro (heq | heq)
      · exact hpv j hjs heq
      · exact hpji heq
    obtain ⟨f⟩ := exists_arcHomeo (hA i hi) (hB i hi)
    obtain ⟨e₀, he₀, hfix₀, _⟩ := exists_homeomorph_extending_crosscut
      hC (hA i hi) (hB i hi) hv (hp i hi) (hAI i hi) (hBI i hi) f
    have he₀A : e₀ '' A i = B i := he₀.image_eq.trans f.image_eq
    have he₀v : e₀ v = v := (he₀ (hA i hi).left_mem).trans f.map_left
    have he₀p : ∀ j ∈ s, e₀ (p j) = p j :=
      fun j hj => hfix₀ (fun hx => hx.1 (hp j hj))
    have he₀C : e₀ '' C = C := by
      have heq : EqOn e₀ id C := fun x hx => hfix₀ (fun hinside => hinside.1 hx)
      exact heq.image_eq.trans (image_id C)
    have hA₀ : ∀ j ∈ s, IsArcBetween (e₀ '' A j) v (p j) := by
      intro j hj
      simpa only [he₀v, he₀p j hj] using isArcBetween_image e₀ (hA j hj)
    have hAA₀ : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → (e₀ '' A j) ∩ (e₀ '' A k) = {v} := by
      intro j hj k hk hjk
      rw [← image_inter e₀.injective, hAA j hj k hk hjk, image_singleton, he₀v]
    have hA₀I : ∀ j ∈ s, (e₀ '' A j) \ {v, p j} ⊆ inside C := by
      intro j hj x hx
      obtain ⟨y, hy, rfl⟩ := hx.1
      have hyends : y ∉ ({v, p j} : Set Plane) := by
        rintro (rfl | rfl)
        · exact hx.2 (Or.inl he₀v)
        · exact hx.2 (Or.inr (he₀p j hj))
      have hmem : e₀ y ∈ e₀ '' inside C := ⟨y, hAI j hj ⟨hy, hyends⟩, rfl⟩
      rwa [image_inside, he₀C] at hmem
    have hnewA : ∀ j ∈ s.erase i, (e₀ '' A j) \ {v, p j} ⊆ inside (R ∪ B i) := by
      intro j hj
      have hjs := (Finset.mem_erase.mp hj).2
      apply arc_diff_subset_crosscut_side hC (hB i hi) hcut.symm (hBI i hi)
        (hA₀ j hjs) ?_ (hpR j hj)
      intro x hx
      refine ⟨hA₀I j hjs hx, ?_⟩
      intro hxi
      have hxv : x = v := (hAA₀ j hjs i hi (Finset.mem_erase.mp hj).1).subset
        ⟨hx.1, he₀A.symm ▸ hxi⟩
      exact hx.2 (Or.inl hxv)
    have hnewB : ∀ j ∈ s.erase i, B j \ {v, p j} ⊆ inside (R ∪ B i) := by
      intro j hj
      have hjs := (Finset.mem_erase.mp hj).2
      apply arc_diff_subset_crosscut_side hC (hB i hi) hcut.symm (hBI i hi)
        (hB j hjs) ?_ (hpR j hj)
      intro x hx
      refine ⟨hBI j hjs hx, ?_⟩
      intro hxi
      have hxv : x = v := (hBB j hjs i hi (Finset.mem_erase.mp hj).1).subset ⟨hx.1, hxi⟩
      exact hx.2 (Or.inl hxv)
    have hnewC := isJordanCurve_cut_arc_union (hB i hi) hcut.symm (hBI i hi)
    obtain ⟨e₁, he₁, hfix₁⟩ := ih (s.erase i) (Finset.erase_ssubset hi)
      hnewC (Or.inr (hB i hi).left_mem) (fun j hj => Or.inl (hpR j hj).1)
      (fun j hj => hA₀ j (Finset.mem_erase.mp hj).2)
      (fun j hj => hB j (Finset.mem_erase.mp hj).2) hnewA hnewB
      (fun j hj k hk hjk => hAA₀ j (Finset.mem_erase.mp hj).2 k (Finset.mem_erase.mp hk).2 hjk)
      (fun j hj k hk hjk => hBB j (Finset.mem_erase.mp hj).2 k (Finset.mem_erase.mp hk).2 hjk)
    have hcover := (crosscut_regions hC (hB i hi) hcut.symm (hBI i hi)).1
    have hsmall : inside (R ∪ B i) ⊆ inside C \ B i :=
      fun _ hx => hcover.symm.subset (Or.inl hx)
    refine ⟨e₀.trans e₁, ?_, ?_⟩
    · intro j hj
      change (e₁ ∘ e₀) '' A j = B j
      rw [image_comp]
      by_cases hji : j = i
      · subst j
        rw [he₀A]
        have heq : EqOn e₁ id (B i) := fun _ hx => hfix₁ (fun hy => (hsmall hy).2 hx)
        exact heq.image_eq.trans (image_id (B i))
      · exact he₁ j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    · intro x hx
      change e₁ (e₀ x) = x
      rw [hfix₀ hx, id_eq]
      exact hfix₁ (fun hy => hx (hsmall hy).1)

end DifferentialGeometry.Topology.PlanarJordan
