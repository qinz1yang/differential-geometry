import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set

namespace DifferentialGeometry.Topology

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

end DifferentialGeometry.Topology

namespace Homeomorph

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

theorem snd_symm_eq_of_snd_eq (Φ : (M × P) ≃ₜ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (q : N × P) : (Φ.symm q).2 = q.2 :=
  (hΦ (Φ.symm q)).symm.trans (congrArg Prod.snd (Φ.apply_symm_apply q))

def restrictFiber (Φ : (M × P) ≃ₜ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) : M ≃ₜ N where
  toFun x := (Φ (x, p)).1
  invFun y := (Φ.symm (y, p)).1
  left_inv x := by
    have h : ((Φ (x, p)).1, p) = Φ (x, p) := Prod.ext rfl (hΦ (x, p)).symm
    change (Φ.symm ((Φ (x, p)).1, p)).1 = x
    rw [h, Φ.symm_apply_apply]
  right_inv y := by
    have h : ((Φ.symm (y, p)).1, p) = Φ.symm (y, p) :=
      Prod.ext rfl (Φ.snd_symm_eq_of_snd_eq hΦ (y, p)).symm
    change (Φ ((Φ.symm (y, p)).1, p)).1 = y
    rw [h, Φ.apply_symm_apply]
  continuous_toFun := (Φ.continuous.comp (continuous_id.prodMk continuous_const)).fst
  continuous_invFun := (Φ.symm.continuous.comp (continuous_id.prodMk continuous_const)).fst

@[simp] theorem restrictFiber_apply (Φ : (M × P) ≃ₜ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) (x : M) : Φ.restrictFiber hΦ p x = (Φ (x, p)).1 := rfl

@[simp] theorem restrictFiber_symm_apply (Φ : (M × P) ≃ₜ (N × P))
    (hΦ : ∀ q, (Φ q).2 = q.2) (p : P) (y : N) :
    (Φ.restrictFiber hΦ p).symm y = (Φ.symm (y, p)).1 := rfl

theorem continuous_restrictFiber (Φ : (M × P) ≃ₜ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) :
    Continuous (fun q : P × M => Φ.restrictFiber hΦ q.1 q.2) :=
  (Φ.continuous.comp (continuous_snd.prodMk continuous_fst)).fst

theorem continuous_restrictFiber_symm (Φ : (M × P) ≃ₜ (N × P)) (hΦ : ∀ q, (Φ q).2 = q.2) :
    Continuous (fun q : P × N => (Φ.restrictFiber hΦ q.1).symm q.2) :=
  (Φ.symm.continuous.comp (continuous_snd.prodMk continuous_fst)).fst

end Homeomorph

namespace Set

theorem image_prod_inter_range {M E F P : Type*}
    (f : M → F × P) (H : P → E → F) {K L : Set E} {J : Set P}
    (hlevels : ∀ t ∈ J,
      (H t '' K) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) = H t '' L) :
    ((fun q : E × P => (H q.2 q.1, q.2)) '' (K ×ˢ J)) ∩ range f =
      (fun q : E × P => (H q.2 q.1, q.2)) '' (L ×ˢ J) := by
  apply Subset.antisymm
  · rintro z ⟨⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩, x, hx⟩
    have hmem : H t y ∈ (H t '' K) ∩ ((fun x => (f x).1) '' {x | (f x).2 = t}) :=
      ⟨mem_image_of_mem _ hy, x, congrArg Prod.snd hx, congrArg Prod.fst hx⟩
    obtain ⟨w, hw, hwy⟩ := (hlevels t ht).subset hmem
    exact ⟨(w, t), ⟨hw, ht⟩, Prod.ext hwy rfl⟩
  · rintro z ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    have hmem := (hlevels t ht).symm.subset (mem_image_of_mem (H t) hy)
    obtain ⟨w, hw, hwy⟩ := hmem.1
    obtain ⟨x, hx, hxy⟩ := hmem.2
    exact ⟨⟨(w, t), ⟨hw, ht⟩, Prod.ext hwy rfl⟩, x, Prod.ext hxy hx⟩

end Set
