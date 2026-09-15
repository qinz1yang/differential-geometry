import DifferentialGeometry.Topology.PiecewiseLinear.SimplyEmbedded
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.RelativePush
import DifferentialGeometry.Analysis.Convex.CompactFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_push_union_sdiff_diskInterior
    {C S₁ S₂ D : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : HasPushProperty C) (hCfront : frontier C = S₁) (hS₂ : IsPLSphere 2 S₂)
    {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hD : S₁ ∩ S₂ = D)
    (hout : S₂ \ D ⊆ Cᶜ) {W : Set (EuclideanSpace ℝ (Fin 3))}
    (hW : IsOpen W) (hCW : C ⊆ W) :
    ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn h univ univ ∧
      h '' ((S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2)) = S₂ ∧ EqOn h id Wᶜ := by
  have hS₁ : IsPLSphere 2 S₁ := hCfront ▸ hC.1.isPLSphere_frontier
  have hD₁ : D ⊆ S₁ := hD ▸ inter_subset_left
  have hD₂ : D ⊆ S₂ := hD ▸ inter_subset_right
  let A₁ := closure (S₁ \ D)
  let A₂ := closure (S₂ \ D)
  have hA₁ : IsPLBall 2 A₁ := hS₁.isPLBall_closure_sdiff ⟨q, hq⟩ hD₁
  have hA₂ : IsPLBall 2 A₂ := hS₂.isPLBall_closure_sdiff ⟨q, hq⟩ hD₂
  have hA₁S : A₁ ⊆ S₁ := closure_minimal sdiff_subset hS₁.isPolyhedron.isClosed
  have hA₂S : A₂ ⊆ S₂ := closure_minimal sdiff_subset hS₂.isPolyhedron.isClosed
  obtain ⟨f, hf⟩ := hA₁
  have hJ₁ : f '' stdSimplexBoundary 2 = A₁ ∩ D :=
    hS₁.image_stdSimplexBoundary_complement ⟨q, hq⟩ hD₁ hf
  have hJ : D ∩ A₁ = D ∩ A₂ :=
    (hS₁.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hD₁).trans
      (hS₂.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hD₂).symm
  have hA₂out : A₂ ⊆ (interior C)ᶜ :=
    closure_minimal (hout.trans (compl_subset_compl.mpr interior_subset)) isOpen_interior.isClosed_compl
  have hCA : C ∩ A₂ ⊆ f '' stdSimplexBoundary 2 := by
    rintro x ⟨hxC, hxA₂⟩
    have hxS₁ : x ∈ S₁ := hCfront ▸ (show x ∈ frontier C from ⟨subset_closure hxC, hA₂out hxA₂⟩)
    have hxD : x ∈ D := hD ▸ ⟨hxS₁, hA₂S hxA₂⟩
    rw [hJ₁]
    exact ⟨(hJ.symm ▸ (show x ∈ D ∩ A₂ from ⟨hxD, hxA₂⟩)).2, hxD⟩
  have hdense : A₂ ⊆ closure (A₂ \ C) := by
    apply closure_mono
    intro x hx
    exact ⟨subset_closure hx, hout hx⟩
  have hpush : HasPushPropertyAt C A₁ := hC.2 A₁ ⟨f, hf⟩ (hCfront.symm ▸ hA₁S)
  obtain ⟨h, hh, -, -, hfix, himage⟩ :=
    hpush.exists_homeomorph_fixed_on_of_inter_subset hf hA₂.isPolyhedron hCA hdense hW hCW
  have hsource : A₁ ∪ A₂ = (S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2) := by
    rw [show A₁ = S₁ \ (D \ q '' stdSimplexBoundary 2) from
      hS₁.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hq hD₁,
      show A₂ = S₂ \ (D \ q '' stdSimplexBoundary 2) from
      hS₂.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hq hD₂, union_sdiff_distrib]
  have htarget : D ∪ A₂ = S₂ := by
    apply Subset.antisymm (union_subset hD₂ hA₂S)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hx, hxD⟩)
  have hcomp : closure (frontier C \ A₁) = D := by
    rw [hCfront]
    exact hS₁.closure_sdiff_closure_sdiff_eq ⟨q, hq⟩ hD₁
  rw [hsource, hcomp, htarget] at himage
  exact ⟨h, hh, himage, hfix⟩

theorem exists_isPLHomeomorphOn_straighten_union_sdiff_diskInterior
    {S₁ S₂ D : Set (EuclideanSpace ℝ (Fin 3))}
    (hS₁ : IsSimplyEmbedded S₁) (hS₂ : IsSimplyEmbedded S₂)
    {q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hD : S₁ ∩ S₂ = D)
    {W : Set (EuclideanSpace ℝ (Fin 3))} (hW : Convex ℝ W) (hWo : IsOpen W) (hSW : S₁ ∪ S₂ ⊆ W) :
    ∃ (T : Finset (EuclideanSpace ℝ (Fin 3)))
      (h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
      AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3)) ∧ T.card = 4 ∧
      IsPLHomeomorphOn h univ univ ∧
      h '' ((S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2)) =
        frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) ∧ EqOn h id Wᶜ := by
  classical
  obtain ⟨T₁, h₁, hT₁, hcard₁, hh₁, himage₁, -⟩ := hS₁.2 univ convex_univ isOpen_univ (subset_univ _)
  let C₁ := h₁.symm '' convexHull ℝ (T₁ : Set (EuclideanSpace ℝ (Fin 3)))
  have hC₁ : HasPushProperty C₁ := (hasPushProperty_convexHull_simplex T₁ hT₁ hcard₁).image hh₁.homeomorph_symm
  have hfront₁ : frontier C₁ = S₁ := by
    rw [show frontier C₁ = frontier (h₁.symm '' convexHull ℝ (T₁ : Set (EuclideanSpace ℝ (Fin 3)))) from rfl,
      ← h₁.symm.image_frontier, ← himage₁, h₁.image_symm, h₁.injective.preimage_image]
  have hnorm : h₁ '' C₁ = convexHull ℝ (T₁ : Set (EuclideanSpace ℝ (Fin 3))) := by
    change h₁ '' (h₁.symm '' _) = _
    rw [image_image]
    simp only [Homeomorph.apply_symm_apply, image_id']
  have hD₁ : D ⊆ S₁ := hD ▸ inter_subset_left
  have hD₂ : D ⊆ S₂ := hD ▸ inter_subset_right
  have hS₁W : S₁ ⊆ W := subset_union_left.trans hSW
  have hS₂W : S₂ ⊆ W := subset_union_right.trans hSW
  have hC₁W : C₁ ⊆ W := DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_open
    hC₁.1.isPolyhedron.isCompact hW hWo (hfront₁.symm ▸ hS₁W)
  have hmove : ∃ S' : Set (EuclideanSpace ℝ (Fin 3)), IsSimplyEmbedded S' ∧ S' ⊆ W ∧
      ∃ g : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3), IsPLHomeomorphOn g univ univ ∧
        g '' ((S₁ ∪ S₂) \ (D \ q '' stdSimplexBoundary 2)) = S' ∧ EqOn g id Wᶜ := by
    by_cases hout : S₂ \ D ⊆ C₁ᶜ
    · exact ⟨S₂, hS₂, hS₂W,
        exists_isPLHomeomorphOn_push_union_sdiff_diskInterior hC₁ hfront₁ hS₂.1 hq hD hout hWo hC₁W⟩
    have hcover : S₂ \ D ⊆ interior C₁ ∪ C₁ᶜ := by
      rintro x ⟨hxS₂, hxD⟩
      by_cases hxC₁ : x ∈ C₁
      · left
        by_contra hxint
        have hxS₁ : x ∈ S₁ := hfront₁ ▸ (show x ∈ frontier C₁ from ⟨subset_closure hxC₁, hxint⟩)
        exact hxD (hD ▸ ⟨hxS₁, hxS₂⟩)
      · exact Or.inr hxC₁
    have hin : S₂ \ D ⊆ interior C₁ :=
      (IsPreconnected.subset_or_subset isOpen_interior hC₁.1.isPolyhedron.isClosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hcover
        (hS₂.1.isConnected_sdiff_of_isPLBall_two ⟨q, hq⟩ hD₂).isPreconnected).resolve_right hout
    have hS₂C₁ : S₂ ⊆ C₁ := by
      intro x hx
      by_cases hxD : x ∈ D
      · exact hC₁.1.isPolyhedron.isClosed.frontier_subset (hfront₁.symm ▸ hD₁ hxD)
      · exact interior_subset (hin ⟨hx, hxD⟩)
    obtain ⟨C₂, hball₂, hfront₂, -, hC₂⟩ := exists_hasPushProperty_of_isSimplyEmbedded hS₂
    have hC₂C₁ : C₂ ⊆ C₁ := DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_of_convex_image
      hball₂.isPolyhedron.isCompact h₁ (hnorm.symm ▸ convex_convexHull ℝ _) hC₁.1.isPolyhedron.isClosed
      (hfront₂.symm ▸ hS₂C₁)
    have hout' : S₁ \ D ⊆ C₂ᶜ := by
      rintro x ⟨hxS₁, hxD⟩ hxC₂
      have hxint : x ∈ interior C₂ := by
        by_contra h
        have hxS₂ : x ∈ S₂ := hfront₂ ▸ (show x ∈ frontier C₂ from ⟨subset_closure hxC₂, h⟩)
        exact hxD (hD ▸ ⟨hxS₁, hxS₂⟩)
      have hxfront : x ∈ frontier C₁ := hfront₁.symm ▸ hxS₁
      exact hxfront.2 (interior_mono hC₂C₁ hxint)
    have hC₂W : C₂ ⊆ W := hC₂C₁.trans hC₁W
    obtain ⟨g, hg, hgs, hgfix⟩ := exists_isPLHomeomorphOn_push_union_sdiff_diskInterior
      hC₂ hfront₂ hS₁.1 hq ((inter_comm _ _).trans hD) hout' hWo hC₂W
    rw [union_comm S₂ S₁] at hgs
    exact ⟨S₁, hS₁, hS₁W, g, hg, hgs, hgfix⟩
  obtain ⟨S', hS', hS'W, g, hg, hgs, hgfix⟩ := hmove
  obtain ⟨T, H, hT, hcard, hH, hHS, hHfix⟩ := hS'.2 W hW hWo hS'W
  refine ⟨T, g.trans H, hT, hcard, hg.trans hH, ?_, ?_⟩
  · change (fun x => H (g x)) '' _ = _
    rw [← image_image H g, hgs]
    exact hHS
  · intro x hx
    change H (g x) = x
    rw [hgfix hx, id_eq]
    exact hHfix hx

end DifferentialGeometry.Topology.PiecewiseLinear
