/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Homeomorph.DisjointGluing

open Set

namespace Homeomorph

theorem exists_gluing_family_of_pairwise_disjoint
    {P X ι : Type*} [TopologicalSpace P] [TopologicalSpace X] [Finite ι]
    (f : ι → P → X ≃ₜ X) (U : ι → Set X)
    (hf : ∀ i, Continuous (fun q : P × X => f i q.1 q.2))
    (hfi : ∀ i, Continuous (fun q : P × X => (f i q.1).symm q.2))
    (hfix : ∀ i p, EqOn (f i p) id (U i)ᶜ)
    (hdis : Pairwise fun i j => Disjoint (U i) (U j)) :
    ∃ g : P → X ≃ₜ X,
      Continuous (fun q : P × X => g q.1 q.2) ∧
      Continuous (fun q : P × X => (g q.1).symm q.2) ∧
      (∀ i p, EqOn (g p) (f i p) (U i)) ∧
      (∀ p, EqOn (g p) id (⋃ i, U i)ᶜ ∧ EqOn (g p).symm id (⋃ i, U i)ᶜ) ∧
      ∀ p, (∀ i, f i p = Homeomorph.refl X) → g p = Homeomorph.refl X := by
  let e (i : ι) : (P × X) ≃ₜ (P × X) :=
    { toFun := fun q => (q.1, f i q.1 q.2)
      invFun := fun q => (q.1, (f i q.1).symm q.2)
      left_inv := fun q => by simp only [symm_apply_apply]
      right_inv := fun q => by simp only [apply_symm_apply]
      continuous_toFun := continuous_fst.prodMk (hf i)
      continuous_invFun := continuous_fst.prodMk (hfi i) }
  have hefix (i : ι) : EqOn (e i) id (univ ×ˢ U i)ᶜ := by
    intro q hq
    have hx : q.2 ∉ U i := fun hx => hq ⟨mem_univ _, hx⟩
    change (q.1, f i q.1 q.2) = q
    rw [hfix i q.1 hx]
    rfl
  have hedis : Pairwise fun i j => Disjoint (univ ×ˢ U i : Set (P × X))
      (univ ×ˢ U j) := by
    intro i j hij
    exact disjoint_left.mpr fun _ hi hj => disjoint_left.mp (hdis hij) hi.2 hj.2
  obtain ⟨F, hF, hFfix⟩ := exists_gluing_of_pairwise_disjoint e _ hefix hedis
  have hout (q : P × X) (hq : q.2 ∉ ⋃ i, U i) : q ∉ ⋃ i, univ ×ˢ U i := by
    rintro ⟨_, ⟨i, rfl⟩, hi⟩
    exact hq (mem_iUnion.mpr ⟨i, hi.2⟩)
  have hfst (q : P × X) : (F q).1 = q.1 := by
    by_cases hq : q.2 ∈ ⋃ i, U i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      rw [hF i ⟨mem_univ _, hi⟩]
      rfl
    · rw [hFfix (hout q hq)]
      rfl
  have hifst (q : P × X) : (F.symm q).1 = q.1 := by
    have h := hfst (F.symm q)
    rw [F.apply_symm_apply] at h
    exact h.symm
  let g (p : P) : X ≃ₜ X :=
    { toFun := fun x => (F (p, x)).2
      invFun := fun x => (F.symm (p, x)).2
      left_inv := fun x => by
        have h : (p, (F (p, x)).2) = F (p, x) := Prod.ext (hfst (p, x)).symm rfl
        change (F.symm (p, (F (p, x)).2)).2 = x
        rw [h, F.symm_apply_apply]
      right_inv := fun x => by
        have h : (p, (F.symm (p, x)).2) = F.symm (p, x) :=
          Prod.ext (hifst (p, x)).symm rfl
        change (F (p, (F.symm (p, x)).2)).2 = x
        rw [h, F.apply_symm_apply]
      continuous_toFun := F.continuous.snd.comp (continuous_const.prodMk continuous_id)
      continuous_invFun := F.symm.continuous.snd.comp (continuous_const.prodMk continuous_id) }
  have hgf (i : ι) (p : P) : EqOn (g p) (f i p) (U i) := by
    intro x hx
    exact congrArg Prod.snd (hF i ⟨mem_univ p, hx⟩)
  have hgfix (p : P) : EqOn (g p) id (⋃ i, U i)ᶜ := by
    intro x hx
    exact congrArg Prod.snd (hFfix (hout (p, x) hx))
  refine ⟨g, F.continuous.snd, F.symm.continuous.snd, hgf, ?_, ?_⟩
  · intro p
    refine ⟨hgfix p, fun x hx => ?_⟩
    apply (g p).injective
    rw [(g p).apply_symm_apply, id_eq, hgfix p hx]
    rfl
  · intro p hp
    apply Homeomorph.ext
    intro x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [hgf i p hi, hp i]
    · exact hgfix p hx

end Homeomorph
