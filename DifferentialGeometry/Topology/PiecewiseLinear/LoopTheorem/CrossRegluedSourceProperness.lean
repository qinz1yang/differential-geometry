/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem preimage_frontier_of_isPLHomeomorphOn_of_subset
    {P Q W : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hP : IsClosed P) (hQ : IsClosed Q) (hQW : Q ⊆ W)
    (hf : IsPLHomeomorphOn f P Q) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ P) (hxf : f x ∈ frontier W) : x ∈ frontier P := by
  have hfxQ : f x ∈ Q := hf.bijOn.mapsTo hx
  have hfxfront : f x ∈ frontier Q := by
    refine ⟨subset_closure hfxQ, ?_⟩
    intro hxin
    exact hxf.2 (interior_mono hQW hxin)
  rw [← hf.image_frontier (by simp) hP hQ] at hfxfront
  obtain ⟨y, hy, hxy⟩ := hfxfront
  have hxy' : x = y := hf.bijOn.injOn hx (hP.frontier_subset hy) hxy.symm
  rw [hxy']
  exact hy

theorem preimage_boundary_subset_frontier_of_source_two_piece_glue
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {H : SingularTwoCell M} {BdM : Set M}
    {P Q R T : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : EuclideanSpace ℝ (Fin 2)}
    {F₁ F₂ : EuclideanSpace ℝ (Fin 2) → M}
    (hHdomain : H.domain = P ∪ Q)
    (hleft : ∀ x ∈ P, F₁ x ∈ BdM → x ∈ frontier P)
    (hright : ∀ x ∈ Q, F₂ x ∈ BdM → x ∈ frontier Q)
    (hseam : ∀ x ∈ P ∩ Q, F₁ x ∈ BdM → x = a ∨ x = b)
    (hcutP : Schoenflies.IsCutPair (frontier P) a b (P ∩ Q) R)
    (hcutQ : Schoenflies.IsCutPair (frontier Q) a b (P ∩ Q) T)
    (hfront : frontier H.domain = R ∪ T)
    (hH₁ : EqOn H F₁ P) (hH₂ : EqOn H F₂ Q) :
    H.domain ∩ H ⁻¹' BdM ⊆ frontier H.domain := by
  rintro x ⟨hx, hxb⟩
  rw [hHdomain] at hx
  by_cases hxP : x ∈ P
  · have hFxb : F₁ x ∈ BdM := by
      rw [← hH₁ hxP]
      exact hxb
    by_cases hxQ : x ∈ Q
    · rcases hseam x ⟨hxP, hxQ⟩ hFxb with rfl | rfl
      · rw [hfront]
        exact Or.inl hcutP.snd.left_mem
      · rw [hfront]
        exact Or.inl hcutP.snd.right_mem
    · have hxfront : x ∈ frontier P := hleft x hxP hFxb
      rw [← hcutP.union_eq] at hxfront
      rw [hfront]
      exact Or.inl (hxfront.resolve_left fun hxPQ => hxQ hxPQ.2)
  · have hxQ : x ∈ Q := hx.resolve_left hxP
    have hFxb : F₂ x ∈ BdM := by
      rw [← hH₂ hxQ]
      exact hxb
    have hxfront : x ∈ frontier Q := hright x hxQ hFxb
    rw [← hcutQ.union_eq] at hxfront
    rw [hfront]
    exact Or.inr (hxfront.resolve_left fun hxPQ => hxP hxPQ.1)

theorem frontier_subset_preimage_boundary_of_source_two_piece_glue
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {H : SingularTwoCell M} {BdM : Set M}
    {P Q R T : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : EuclideanSpace ℝ (Fin 2)}
    {F₁ F₂ : EuclideanSpace ℝ (Fin 2) → M}
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (hHdomain : H.domain = P ∪ Q)
    (hRboundary : ∀ x ∈ R, F₁ x ∈ BdM)
    (hTboundary : ∀ x ∈ T, F₂ x ∈ BdM)
    (hcutP : Schoenflies.IsCutPair (frontier P) a b (P ∩ Q) R)
    (hcutQ : Schoenflies.IsCutPair (frontier Q) a b (P ∩ Q) T)
    (hfront : frontier H.domain = R ∪ T)
    (hH₁ : EqOn H F₁ P) (hH₂ : EqOn H F₂ Q) :
    frontier H.domain ⊆ H.domain ∩ H ⁻¹' BdM := by
  intro x hx
  rw [hfront] at hx
  refine ⟨?_, ?_⟩
  · rw [hHdomain]
    rcases hx with hxR | hxT
    · exact Or.inl (hP.isPolyhedron.isClosed.frontier_subset
        (hcutP.snd_subset hxR))
    · exact Or.inr (hQ.isPolyhedron.isClosed.frontier_subset
        (hcutQ.snd_subset hxT))
  · rcases hx with hxR | hxT
    · have hxP : x ∈ P := hP.isPolyhedron.isClosed.frontier_subset
        (hcutP.snd_subset hxR)
      change H x ∈ BdM
      rw [hH₁ hxP]
      exact hRboundary x hxR
    · have hxQ : x ∈ Q := hQ.isPolyhedron.isClosed.frontier_subset
        (hcutQ.snd_subset hxT)
      change H x ∈ BdM
      rw [hH₂ hxQ]
      exact hTboundary x hxT

theorem preimage_boundary_eq_frontier_of_source_two_piece_glue
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {H : SingularTwoCell M} {BdM : Set M}
    {P Q R T : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : EuclideanSpace ℝ (Fin 2)}
    {F₁ F₂ : EuclideanSpace ℝ (Fin 2) → M}
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (hHdomain : H.domain = P ∪ Q)
    (hleft : ∀ x ∈ P, F₁ x ∈ BdM → x ∈ frontier P)
    (hright : ∀ x ∈ Q, F₂ x ∈ BdM → x ∈ frontier Q)
    (hseam : ∀ x ∈ P ∩ Q, F₁ x ∈ BdM → x = a ∨ x = b)
    (hRboundary : ∀ x ∈ R, F₁ x ∈ BdM)
    (hTboundary : ∀ x ∈ T, F₂ x ∈ BdM)
    (hcutP : Schoenflies.IsCutPair (frontier P) a b (P ∩ Q) R)
    (hcutQ : Schoenflies.IsCutPair (frontier Q) a b (P ∩ Q) T)
    (hfront : frontier H.domain = R ∪ T)
    (hH₁ : EqOn H F₁ P) (hH₂ : EqOn H F₂ Q) :
    H.domain ∩ H ⁻¹' BdM = frontier H.domain := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxb⟩
    rw [hHdomain] at hx
    by_cases hxP : x ∈ P
    · have hFxb : F₁ x ∈ BdM := by
        rw [← hH₁ hxP]
        exact hxb
      by_cases hxQ : x ∈ Q
      · rcases hseam x ⟨hxP, hxQ⟩ hFxb with rfl | rfl
        · rw [hfront]
          exact Or.inl hcutP.snd.left_mem
        · rw [hfront]
          exact Or.inl hcutP.snd.right_mem
      · have hxfront : x ∈ frontier P := hleft x hxP hFxb
        rw [← hcutP.union_eq] at hxfront
        rw [hfront]
        exact Or.inl (hxfront.resolve_left fun hxPQ => hxQ hxPQ.2)
    · have hxQ : x ∈ Q := hx.resolve_left hxP
      have hFxb : F₂ x ∈ BdM := by
        rw [← hH₂ hxQ]
        exact hxb
      have hxfront : x ∈ frontier Q := hright x hxQ hFxb
      rw [← hcutQ.union_eq] at hxfront
      rw [hfront]
      exact Or.inr (hxfront.resolve_left fun hxPQ => hxP hxPQ.1)
  · intro x hx
    rw [hfront] at hx
    refine ⟨?_, ?_⟩
    · rw [hHdomain]
      rcases hx with hxR | hxT
      · exact Or.inl (hP.isPolyhedron.isClosed.frontier_subset
          (hcutP.snd_subset hxR))
      · exact Or.inr (hQ.isPolyhedron.isClosed.frontier_subset
          (hcutQ.snd_subset hxT))
    · rcases hx with hxR | hxT
      · have hxP : x ∈ P := hP.isPolyhedron.isClosed.frontier_subset
          (hcutP.snd_subset hxR)
        change H x ∈ BdM
        rw [hH₁ hxP]
        exact hRboundary x hxR
      · have hxQ : x ∈ Q := hQ.isPolyhedron.isClosed.frontier_subset
          (hcutQ.snd_subset hxT)
        change H x ∈ BdM
        rw [hH₂ hxQ]
        exact hTboundary x hxT

theorem preimage_boundary_eq_frontier_of_cross_reglued_source
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {D H G : SingularTwoCell M} {BdM : Set M}
    {P Q P' Q' U₁ U₂ U₃ A C R₀ T₀ R T :
      Set (EuclideanSpace ℝ (Fin 2))}
    {p q a₀ a₁ a b : EuclideanSpace ℝ (Fin 2)}
    {f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hDproper : D.domain ∩ D ⁻¹' BdM = frontier D.domain)
    (hP : IsPLBall 2 P) (hQ : IsPLBall 2 Q)
    (hP' : IsPLBall 2 P') (hQ' : IsPLBall 2 Q')
    (hU₁ : IsPLBall 2 U₁) (hU₂ : IsPLBall 2 U₂) (hU₃ : IsPLBall 2 U₃)
    (hHdomain : H.domain = P ∪ Q) (hGdomain : G.domain = P' ∪ Q')
    (hf₁ : IsPLHomeomorphOn f₁ P U₁)
    (hf₂ : IsPLHomeomorphOn f₂ Q U₂)
    (hh : IsPLHomeomorphOn h P' H.domain)
    (hf₃ : IsPLHomeomorphOn f₃ Q' U₃)
    (hU₁sub : U₁ ⊆ D.domain) (hU₂sub : U₂ ⊆ D.domain)
    (hU₃sub : U₃ ⊆ D.domain)
    (hf₁seam : f₁ '' (P ∩ Q) = A)
    (hf₃seam : f₃ '' (P' ∩ Q') = C)
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q')
    (hcutP : Schoenflies.IsCutPair (frontier P) a₀ a₁ (P ∩ Q) R₀)
    (hcutQ : Schoenflies.IsCutPair (frontier Q) a₀ a₁ (P ∩ Q) T₀)
    (hfrontH : frontier H.domain = R₀ ∪ T₀)
    (hf₁a₀ : f₁ a₀ = p) (hf₁a₁ : f₁ a₁ = q)
    (hcut₁ : Schoenflies.IsCutPair (frontier U₁)
      p q A (U₁ ∩ frontier D.domain))
    (hcutP' : Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R)
    (hcutQ' : Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T)
    (hfrontG : frontier G.domain = R ∪ T)
    (hcut₃ : Schoenflies.IsCutPair (frontier U₃)
      (f₃ a) (f₃ b) C (U₃ ∩ frontier D.domain))
    (hRboundary : ∀ x ∈ R, (H ∘ h) x ∈ BdM)
    (hTboundary : ∀ x ∈ T, (D ∘ f₃) x ∈ BdM) :
    G.domain ∩ G ⁻¹' BdM = frontier G.domain := by
  have hleft₁ : ∀ x ∈ P, (D ∘ f₁) x ∈ BdM → x ∈ frontier P := by
    intro x hx hxb
    change D (f₁ x) ∈ BdM at hxb
    have hfx : f₁ x ∈ frontier D.domain := by
      rw [← hDproper]
      exact ⟨hU₁sub (hf₁.bijOn.mapsTo hx), hxb⟩
    exact preimage_frontier_of_isPLHomeomorphOn_of_subset
      hP.isPolyhedron.isClosed hU₁.isPolyhedron.isClosed hU₁sub hf₁ hx hfx
  have hright₁ : ∀ x ∈ Q, (D ∘ f₂) x ∈ BdM → x ∈ frontier Q := by
    intro x hx hxb
    change D (f₂ x) ∈ BdM at hxb
    have hfx : f₂ x ∈ frontier D.domain := by
      rw [← hDproper]
      exact ⟨hU₂sub (hf₂.bijOn.mapsTo hx), hxb⟩
    exact preimage_frontier_of_isPLHomeomorphOn_of_subset
      hQ.isPolyhedron.isClosed hU₂.isPolyhedron.isClosed hU₂sub hf₂ hx hfx
  have hseam₁ : ∀ x ∈ P ∩ Q, (D ∘ f₁) x ∈ BdM → x = a₀ ∨ x = a₁ := by
    intro x hx hxb
    change D (f₁ x) ∈ BdM at hxb
    have hfx : f₁ x ∈ frontier D.domain := by
      rw [← hDproper]
      exact ⟨hU₁sub (hf₁.bijOn.mapsTo hx.1), hxb⟩
    have hfxA : f₁ x ∈ A := by
      rw [← hf₁seam]
      exact ⟨x, hx, rfl⟩
    have hfxTrace : f₁ x ∈ U₁ ∩ frontier D.domain :=
      ⟨hf₁.bijOn.mapsTo hx.1, hfx⟩
    rcases hcut₁.inter_eq.subset ⟨hfxA, hfxTrace⟩ with hxp | hxq
    · left
      have ha₀ : a₀ ∈ P ∩ Q := hcutP.fst.left_mem
      exact hf₁.bijOn.injOn hx.1 ha₀.1 (hxp.trans hf₁a₀.symm)
    · right
      have ha₁ : a₁ ∈ P ∩ Q := hcutP.fst.right_mem
      exact hf₁.bijOn.injOn hx.1 ha₁.1 (hxq.trans hf₁a₁.symm)
  have hHforward : H.domain ∩ H ⁻¹' BdM ⊆ frontier H.domain :=
    preimage_boundary_subset_frontier_of_source_two_piece_glue hHdomain
      hleft₁ hright₁ hseam₁ hcutP hcutQ hfrontH hH₁ hH₂
  have hleft₂ : ∀ x ∈ P', (H ∘ h) x ∈ BdM → x ∈ frontier P' := by
    intro x hx hxb
    change H (h x) ∈ BdM at hxb
    have hxH : h x ∈ H.domain := hh.bijOn.mapsTo hx
    have hHxfront : h x ∈ frontier H.domain := hHforward ⟨hxH, hxb⟩
    exact preimage_frontier_of_isPLHomeomorphOn_of_subset
      hP'.isPolyhedron.isClosed H.isPLBall_domain.isPolyhedron.isClosed
      subset_rfl hh hx hHxfront
  have hright₂ : ∀ x ∈ Q', (D ∘ f₃) x ∈ BdM → x ∈ frontier Q' := by
    intro x hx hxb
    change D (f₃ x) ∈ BdM at hxb
    have hfx : f₃ x ∈ frontier D.domain := by
      rw [← hDproper]
      exact ⟨hU₃sub (hf₃.bijOn.mapsTo hx), hxb⟩
    exact preimage_frontier_of_isPLHomeomorphOn_of_subset
      hQ'.isPolyhedron.isClosed hU₃.isPolyhedron.isClosed hU₃sub hf₃ hx hfx
  have hseam₂ : ∀ x ∈ P' ∩ Q', (H ∘ h) x ∈ BdM → x = a ∨ x = b := by
    intro x hx hxb
    have hFxb : (D ∘ f₃) x ∈ BdM := by
      rw [← hG₃ hx.2, hGH hx.1]
      exact hxb
    change D (f₃ x) ∈ BdM at hFxb
    have hfx : f₃ x ∈ frontier D.domain := by
      rw [← hDproper]
      exact ⟨hU₃sub (hf₃.bijOn.mapsTo hx.2), hFxb⟩
    have hfxC : f₃ x ∈ C := by
      rw [← hf₃seam]
      exact ⟨x, hx, rfl⟩
    have hfxTrace : f₃ x ∈ U₃ ∩ frontier D.domain :=
      ⟨hf₃.bijOn.mapsTo hx.2, hfx⟩
    rcases hcut₃.inter_eq.subset ⟨hfxC, hfxTrace⟩ with hxa | hxb'
    · left
      have ha : a ∈ P' ∩ Q' := hcutP'.fst.left_mem
      exact hf₃.bijOn.injOn hx.2 ha.2 hxa
    · right
      have hb : b ∈ P' ∩ Q' := hcutP'.fst.right_mem
      exact hf₃.bijOn.injOn hx.2 hb.2 hxb'
  exact preimage_boundary_eq_frontier_of_source_two_piece_glue hP' hQ'
    hGdomain hleft₂ hright₂ hseam₂ hRboundary hTboundary hcutP' hcutQ'
    hfrontG hGH hG₃

end DifferentialGeometry.Topology.PiecewiseLinear
