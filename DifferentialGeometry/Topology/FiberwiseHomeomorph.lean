import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set

namespace Poincare.Topology

def fiberwiseHomeomorph
    {N P T : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [T2Space P]
    [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (f : N × T → P) (hf : Continuous f)
    (hbij : ∀ t, Function.Bijective (fun p ↦ f (p, t))) : N × T ≃ₜ P × T := by
  let F : N × T → P × T := fun x ↦ (f x, x.2)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨p, t⟩ ⟨q, s⟩ h
      have ht : t = s := congrArg Prod.snd h
      subst s
      exact Prod.ext ((hbij t).injective (congrArg Prod.fst h)) rfl
    · rintro ⟨p, t⟩
      obtain ⟨q, hq⟩ := (hbij t).surjective p
      exact ⟨(q, t), Prod.ext hq rfl⟩
  exact (show Continuous (Equiv.ofBijective F hF) from
    hf.prodMk continuous_snd).homeoOfEquivCompactToT2

@[simp] theorem fiberwiseHomeomorph_apply
    {N P T : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [T2Space P]
    [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (f : N × T → P) (hf : Continuous f)
    (hbij : ∀ t, Function.Bijective (fun p ↦ f (p, t))) (x : N × T) :
    fiberwiseHomeomorph f hf hbij x = (f x, x.2) := rfl

@[simp] theorem fiberwiseHomeomorph_symm_snd
    {N P T : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [T2Space P]
    [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (f : N × T → P) (hf : Continuous f)
    (hbij : ∀ t, Function.Bijective (fun p ↦ f (p, t))) (x : P × T) :
    ((fiberwiseHomeomorph f hf hbij).symm x).2 = x.2 :=
  congrArg Prod.snd ((fiberwiseHomeomorph f hf hbij).apply_symm_apply x)

theorem prod_Icc_subset_range_of_fiberwise_bijective
    {N P T L : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [T2Space P]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [PreconnectedSpace T]
    [LinearOrder L] [TopologicalSpace L] [OrderClosedTopology L]
    (e : N × T → P × L) (he : Continuous e)
    (hbij : ∀ t, Function.Bijective (fun p ↦ (e (p, t)).1))
    (t₀ t₁ : T) (a b : L)
    (hlower : ∀ p, (e (p, t₀)).2 ≤ a) (hupper : ∀ p, b ≤ (e (p, t₁)).2) :
    (univ : Set P) ×ˢ Icc a b ⊆ range e := by
  let Φ := fiberwiseHomeomorph (fun x ↦ (e x).1) he.fst hbij
  have hparam (x : P × T) : (Φ.symm x).2 = x.2 :=
    fiberwiseHomeomorph_symm_snd _ _ _ x
  have hfirst (x : P × T) : (e (Φ.symm x)).1 = x.1 :=
    congrArg Prod.fst (Φ.apply_symm_apply x)
  rintro ⟨p, z⟩ ⟨-, hz⟩
  let H : T → L := fun t ↦ (e (Φ.symm (p, t))).2
  have hH : Continuous H := he.snd.comp
    (Φ.symm.continuous.comp (continuous_const.prodMk continuous_id))
  have h₀ : H t₀ ≤ a := by
    have h := hlower (Φ.symm (p, t₀)).1
    change (e (Φ.symm (p, t₀))).2 ≤ a
    have hx : ((Φ.symm (p, t₀)).1, t₀) = Φ.symm (p, t₀) :=
      Prod.ext rfl (hparam (p, t₀)).symm
    rw [hx] at h
    exact h
  have h₁ : b ≤ H t₁ := by
    have h := hupper (Φ.symm (p, t₁)).1
    change b ≤ (e (Φ.symm (p, t₁))).2
    have hx : ((Φ.symm (p, t₁)).1, t₁) = Φ.symm (p, t₁) :=
      Prod.ext rfl (hparam (p, t₁)).symm
    rw [hx] at h
    exact h
  obtain ⟨t, ht⟩ := intermediate_value_univ t₀ t₁ hH
    ⟨h₀.trans hz.1, hz.2.trans h₁⟩
  exact ⟨Φ.symm (p, t), Prod.ext (hfirst (p, t)) ht⟩

end Poincare.Topology
