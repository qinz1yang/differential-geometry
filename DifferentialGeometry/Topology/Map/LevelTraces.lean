import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Data.Set.Prod
import Mathlib.Order.SetNotation
import Mathlib.Tactic.NormNum

open Set

namespace DifferentialGeometry.Topology

theorem image_union_inter_eq_of_fiber_traces
    {E M T ι : Type*} {u : E → M} {ρ : E × T → E}
    {R W S : Set E} {A F : Set M} {B : ι → T → Set M} {I : Set T} {t₀ : T}
    (hSR : S ⊆ R) (hW : ρ '' (S ×ˢ I) = W)
    (hzero : t₀ ∈ I → ∀ x ∈ S, ρ (x, t₀) = x)
    (htrace : u '' R ∩ A = F) (hcore : t₀ ∈ I → ∀ k, B k t₀ ⊆ F)
    (hlevels : ∀ t ∈ I \ {t₀}, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A = ⋃ k, B k t) :
    u '' (R ∪ W) ∩ A = F ∪ ⋃ k, ⋃ t ∈ I, B k t := by
  classical
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hxA⟩
    rcases hx with hx | hx
    · exact Or.inl (htrace.subset ⟨mem_image_of_mem u hx, hxA⟩)
    · obtain ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩ := hW.symm.subset hx
      by_cases ht0 : t = t₀
      · have ht₀ : t₀ ∈ I := ht0 ▸ ht
        rw [ht0, hzero ht₀ p hp] at hxA ⊢
        exact Or.inl (htrace.subset ⟨mem_image_of_mem u (hSR hp), hxA⟩)
      · have htp : t ∈ I \ {t₀} := ⟨ht, ht0⟩
        have hm := (hlevels t htp).subset
          ⟨⟨(p, t), ⟨hp, rfl⟩, rfl⟩, hxA⟩
        obtain ⟨k, hyB⟩ := mem_iUnion.mp hm
        exact Or.inr (mem_iUnion.mpr ⟨k,
          mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hyB⟩⟩⟩)
  · rintro y (hyF | hy)
    · obtain ⟨hyR, hyA⟩ := htrace.symm.subset hyF
      exact ⟨image_mono subset_union_left hyR, hyA⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      obtain ⟨t, ht⟩ := mem_iUnion.mp hk
      obtain ⟨htI, hyB⟩ := mem_iUnion.mp ht
      by_cases ht0 : t = t₀
      · subst t
        obtain ⟨hyR, hyA⟩ := htrace.symm.subset (hcore htI k hyB)
        exact ⟨image_mono subset_union_left hyR, hyA⟩
      · have htp : t ∈ I \ {t₀} := ⟨htI, ht0⟩
        have hm := (hlevels t htp).symm.subset (mem_iUnion.mpr ⟨k, hyB⟩)
        obtain ⟨⟨⟨p, r⟩, ⟨hp, hr⟩, heq⟩, hyA⟩ := hm
        have hrt : r = t := hr
        subst r
        exact ⟨⟨ρ (p, t), Or.inr (hW.subset
          (mem_image_of_mem ρ ⟨hp, htI⟩)), heq⟩, hyA⟩

theorem image_union_inter_eq_of_level_traces
    {E M X T H ι : Type*} {u : E → M} {ρ : E × T → E} {F : X × H → M}
    {R W S : Set E} {A : Set M} {B : Set X} {I : Set T} {J : Set H}
    {η : ι → T → X} {t₀ : T}
    (hSR : S ⊆ R) (hW : ρ '' (S ×ˢ I) = W)
    (hzero : t₀ ∈ I → ∀ x ∈ S, ρ (x, t₀) = x)
    (htrace : u '' R ∩ A = F '' (B ×ˢ J))
    (hcore : t₀ ∈ I → ∀ k, η k t₀ ∈ B)
    (hlevels : ∀ t ∈ I \ {t₀}, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, F '' ({η k t} ×ˢ J)) :
    u '' (R ∪ W) ∩ A = F '' ((B ∪ ⋃ k, η k '' I) ×ˢ J) := by
  have hresult := image_union_inter_eq_of_fiber_traces
    (B := fun k t => F '' ({η k t} ×ˢ J)) hSR hW hzero htrace
    (fun ht k => image_mono
      (prod_mono_left (singleton_subset_iff.mpr (hcore ht k)))) hlevels
  have hband (k : ι) :
      F '' ((η k '' I) ×ˢ J) = ⋃ t ∈ I, F '' ({η k t} ×ˢ J) := by
    rw [image_eq_iUnion (η k) I]
    simp only [iUnion_prod_const, image_iUnion]
  have hright : F '' ((B ∪ ⋃ k, η k '' I) ×ˢ J) =
      F '' (B ×ˢ J) ∪ ⋃ k, ⋃ t ∈ I, F '' ({η k t} ×ˢ J) := by
    rw [union_prod, image_union, iUnion_prod_const, image_iUnion]
    exact congrArg (fun Z => F '' (B ×ˢ J) ∪ Z) (iUnion_congr fun k => hband k)
  exact hresult.trans hright.symm

theorem collar_union_trace_eq_radial_bands
    {E M I : Type*} {u : E → M} {ρ : E × ℝ → E} {v : I → ℝ × ℝ → M}
    {R W S : Set E} {A F : Set M} {c : ℝ} (hSR : S ⊆ R)
    (hW : ρ '' (S ×ˢ Icc (0 : ℝ) c) = W)
    (hzero : ∀ x ∈ S, ρ (x, 0) = x) (htrace : u '' R ∩ A = F)
    (hcore : ∀ k, v k '' ({0} ×ˢ Icc (0 : ℝ) 1) ⊆ F)
    (hlevels : ∀ t ∈ Ioc (0 : ℝ) c, (u ∘ ρ) '' (S ×ˢ {t}) ∩ A =
      ⋃ k, v k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1)) :
    u '' (R ∪ W) ∩ A = F ∪ ⋃ k, v k '' (Icc (0 : ℝ) (c / 2) ×ˢ Icc (0 : ℝ) 1) := by
  have hresult := image_union_inter_eq_of_fiber_traces
    (B := fun k t => v k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1))
    (I := Icc (0 : ℝ) c) (t₀ := (0 : ℝ)) hSR hW (fun _ => hzero) htrace
    (by intro _ k; simpa only [zero_div] using hcore k)
    (by
      intro t ht
      exact hlevels t ⟨lt_of_le_of_ne ht.1.1 (Ne.symm ht.2), ht.1.2⟩)
  have hscale : (fun t : ℝ => t / 2) '' Icc (0 : ℝ) c = Icc (0 : ℝ) (c / 2) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      (image_mul_right_Icc' (0 : ℝ) c (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num))
  have hband (k : I) :
      v k '' (Icc (0 : ℝ) (c / 2) ×ˢ Icc (0 : ℝ) 1) =
        ⋃ t ∈ Icc (0 : ℝ) c, v k '' ({t / 2} ×ˢ Icc (0 : ℝ) 1) := by
    rw [← hscale, image_eq_iUnion (fun t : ℝ => t / 2) (Icc (0 : ℝ) c)]
    simp only [iUnion_prod_const, image_iUnion]
  exact hresult.trans
    (congrArg (fun Z => F ∪ Z) (iUnion_congr fun k => (hband k).symm))

end DifferentialGeometry.Topology
