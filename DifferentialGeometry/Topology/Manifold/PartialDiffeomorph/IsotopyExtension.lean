/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.Diffeomorph.Extension

/-! Compact ambient isotopies transported through partial diffeomorphisms. -/

open Set
open scoped ContDiff Manifold Topology

namespace PartialDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {J : ModelWithCorners ℝ F G}

theorem exists_isotopy_extension_of_isCompact
    (c : PartialDiffeomorph I J M N ∞)
    (D : ℝ → Diffeomorph J J N N ∞)
    (hD : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun z : ℝ × N => D z.1 z.2))
    (hDi : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ (fun z : ℝ × N => (D z.1).symm z.2))
    {K : Set N} (hK : IsCompact K) (hKt : K ⊆ c.target)
    (hfix : ∀ p x, x ∉ K → D p x = x) :
    ∃ Φ : ℝ → Diffeomorph I I M M ∞,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => Φ z.1 z.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => (Φ z.1).symm z.2) ∧
      (∀ p, Φ p '' c.source = c.source) ∧
      (∀ p z, z ∈ c.target → Φ p (c.symm z) = c.symm (D p z)) ∧
      (∀ p x, x ∈ c.source → c (Φ p x) = D p (c x)) ∧
      (∀ p, D p = Diffeomorph.refl J N ∞ → Φ p = Diffeomorph.refl I M ∞) ∧
      IsCompact (c.symm '' K) ∧ c.symm '' K ⊆ c.source ∧
      ∀ p x, x ∉ c.symm '' K → Φ p x = x ∧ (Φ p).symm x = x := by
  let U : TopologicalSpace.Opens M := ⟨c.source, c.open_source⟩
  let d := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo c
    (U := U) (Subset.refl c.source)
  let V : TopologicalSpace.Opens N :=
    ⟨c '' (U : Set M), DifferentialGeometry.image_opens_isOpen c (Subset.refl c.source)⟩
  have hV : (V : Set N) = c.target := c.toOpenPartialHomeomorph.image_source_eq_target
  let K' : Set V := Subtype.val ⁻¹' K
  have hKimage : Subtype.val '' K' = K := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x, by change x ∈ (V : Set N); rw [hV]; exact hKt hx⟩, rfl⟩
  have hK' : IsCompact K' := Subtype.isCompact_iff.mpr (by rw [hKimage]; exact hK)
  obtain ⟨Φ, hΦ, hΦi, hΦU, hconj, _, hid, hsupport⟩ :=
    Diffeomorph.exists_extension_conjugate_of_isCompact d D hD hDi hK'
      (fun p x hx => hfix p x (fun hxK => hx
        ⟨⟨x, by change x ∈ (V : Set N); rw [hV]; exact hKt hxK⟩, hxK, rfl⟩))
  have hmaps (p : ℝ) (z : N) (hz : z ∈ c.target) : D p z ∈ c.target := by
    by_contra hn
    have hk : D p z ∉ K := fun h => hn (hKt h)
    have he : D p z = z := (D p).injective (hfix p (D p z) hk)
    exact hn (he.symm ▸ hz)
  have hformula (p : ℝ) (z : N) (hz : z ∈ c.target) :
      Φ p (c.symm z) = c.symm (D p z) := by
    let x : U := ⟨c.symm z, c.map_target hz⟩
    let y : V := ⟨D p z, by change D p z ∈ (V : Set N); rw [hV]; exact hmaps p z hz⟩
    apply (hconj p x y).mpr
    change D p (c (c.symm z)) = D p z
    have hr : c (c.symm z) = z := c.right_inv hz
    rw [hr]
  have hC : (fun y : V => (d.symm y : M)) '' K' = c.symm '' K := by
    rw [← hKimage, image_image]
    rfl
  refine ⟨Φ, hΦ, hΦi, hΦU, hformula, ?_, hid, hC ▸ hsupport.1, ?_, ?_⟩
  · intro p x hx
    have hxt : c x ∈ c.target := c.map_source hx
    have he := hformula p (c x) hxt
    have hl : c.symm (c x) = x := c.left_inv hx
    have hr : c (c.symm (D p (c x))) = D p (c x) :=
      c.right_inv (hmaps p (c x) hxt)
    rw [hl] at he
    rw [he, hr]
  · rintro x ⟨z, hz, rfl⟩
    exact c.map_target (hKt hz)
  · intro p x hx
    have hx' : x ∉ (fun y : V => (d.symm y : M)) '' K' := by rwa [hC]
    exact ⟨(hsupport.2 p).1 hx', (hsupport.2 p).2 hx'⟩

end PartialDiffeomorph
