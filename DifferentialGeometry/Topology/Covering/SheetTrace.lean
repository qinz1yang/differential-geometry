/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff

open Set

namespace DifferentialGeometry.Topology.Covering

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

theorem source_subset_of_preconnected_trace {f : X → Y} {A B C : Set X} {T : Set Y}
    (hA : IsCompact A) (hf : ContinuousOn f A) (hinj : InjOn f A)
    (hB : IsClosed B) (hC : IsClosed C) (hBC : Disjoint B C)
    (hT : IsPreconnected T) (hTA : T ⊆ f '' A)
    (hcover : ∀ x ∈ A, f x ∈ T → x ∈ B ∪ C)
    {a : X} (haA : a ∈ A) (haB : a ∈ B) (hfa : f a ∈ T) :
    ∀ x ∈ A, f x ∈ T → x ∈ B := by
  have hclosedB : IsClosed (f '' (A ∩ B)) :=
    ((hA.inter_right hB).image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have hclosedC : IsClosed (f '' (A ∩ C)) :=
    ((hA.inter_right hC).image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  have hdisj : Disjoint (f '' (A ∩ B)) (f '' (A ∩ C)) := by
    rw [disjoint_left]
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hinj hx.1 hz.1 (hxy.trans hzy.symm)
    exact disjoint_left.mp hBC hx.2 (hxz.symm ▸ hz.2)
  have hTcover : T ⊆ f '' (A ∩ B) ∪ f '' (A ∩ C) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hTA hy
    rcases hcover x hx (hxy.symm ▸ hy) with hxB | hxC
    · exact Or.inl ⟨x, ⟨hx, hxB⟩, hxy⟩
    · exact Or.inr ⟨x, ⟨hx, hxC⟩, hxy⟩
  have hTB : T ⊆ f '' (A ∩ B) := by
    intro y hy
    by_contra hyB
    have hyC := (hTcover hy).resolve_left hyB
    obtain ⟨z, -, hzB, hzC⟩ := isPreconnected_closed_iff.mp hT _ _ hclosedB hclosedC hTcover
      ⟨f a, hfa, a, ⟨haA, haB⟩, rfl⟩ ⟨y, hy, hyC⟩
    exact disjoint_left.mp hdisj hzB hzC
  intro x hx hxT
  obtain ⟨y, hy, hyx⟩ := hTB hxT
  exact hinj hy.1 hx hyx ▸ hy.2

theorem source_label_of_preconnected_image
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    {f : Z → Y} {g : Z → X} {K : Set Z} {A B : Set X} {T : Set Y}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K)
    (hg : ContinuousOn g K) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hT : IsPreconnected T) (hTK : T ⊆ f '' K)
    (hcover : ∀ x ∈ K, f x ∈ T → g x ∈ A ∪ B)
    {a : Z} (ha : a ∈ K) (hga : g a ∈ A) (hfa : f a ∈ T) :
    ∀ x ∈ K, f x ∈ T → g x ∈ A := by
  have hKA : IsClosed (K ∩ g ⁻¹' A) :=
    hg.preimage_isClosed_of_isClosed hK.isClosed hA
  have hKB : IsClosed (K ∩ g ⁻¹' B) :=
    hg.preimage_isClosed_of_isClosed hK.isClosed hB
  have hKK : Disjoint (K ∩ g ⁻¹' A) (K ∩ g ⁻¹' B) :=
    disjoint_left.mpr fun x hx hy => disjoint_left.mp hAB hx.2 hy.2
  have h := source_subset_of_preconnected_trace hK hf hinj hKA hKB hKK hT hTK
    (fun x hx hfx => (hcover x hx hfx).elim
      (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)) ha ⟨ha, hga⟩ hfa
  exact fun x hx hfx => (h x hx hfx).2

theorem inter_image_source_side_eq_of_preconnected
    {f : X → Y} {A₀ A₁ B₀ B₁ H : Set X} {C : Set Y}
    (hA₀ : IsCompact A₀) (hB₀ : IsCompact B₀)
    (hfA : ContinuousOn f A₀) (hfB : ContinuousOn f B₀)
    (hinjA : InjOn f A₀) (hinjB : InjOn f B₀)
    (hA₀cl : IsClosed A₀) (hA₁cl : IsClosed A₁)
    (hB₀cl : IsClosed B₀) (hB₁cl : IsClosed B₁)
    (hAA : Disjoint A₀ A₁) (hBB : Disjoint B₀ B₁)
    (hcoverA : ∀ x ∈ A₀, f x ∈ C → x ∈ B₀ ∪ B₁)
    (hcoverB : ∀ x ∈ B₀, f x ∈ C → x ∈ A₀ ∪ A₁)
    (hconnA : IsPreconnected (C ∩ f '' (A₀ ∩ H)))
    (hconnB : IsPreconnected (C ∩ f '' (B₀ ∩ H)))
    {a : X} (haA : a ∈ A₀) (haB : a ∈ B₀) (haH : a ∈ H) (hfa : f a ∈ C) :
    C ∩ f '' (A₀ ∩ H) = C ∩ f '' (B₀ ∩ H) := by
  have hAB : ∀ x ∈ A₀, f x ∈ C ∩ f '' (A₀ ∩ H) → x ∈ B₀ :=
    source_subset_of_preconnected_trace hA₀ hfA hinjA hB₀cl hB₁cl hBB hconnA
      (inter_subset_right.trans (image_mono inter_subset_left))
      (fun x hx hfx => hcoverA x hx hfx.1) haA haB ⟨hfa, a, ⟨haA, haH⟩, rfl⟩
  have hBA : ∀ x ∈ B₀, f x ∈ C ∩ f '' (B₀ ∩ H) → x ∈ A₀ :=
    source_subset_of_preconnected_trace hB₀ hfB hinjB hA₀cl hA₁cl hAA hconnB
      (inter_subset_right.trans (image_mono inter_subset_left))
      (fun x hx hfx => hcoverB x hx hfx.1) haB haA ⟨hfa, a, ⟨haB, haH⟩, rfl⟩
  ext y
  constructor
  · rintro ⟨hyC, x, hx, hxy⟩
    refine ⟨hyC, x, ⟨hAB x hx.1 ?_, hx.2⟩, hxy⟩
    exact ⟨hxy.symm ▸ hyC, x, hx, rfl⟩
  · rintro ⟨hyC, x, hx, hxy⟩
    refine ⟨hyC, x, ⟨hBA x hx.1 ?_, hx.2⟩, hxy⟩
    exact ⟨hxy.symm ▸ hyC, x, hx, rfl⟩

end DifferentialGeometry.Topology.Covering
