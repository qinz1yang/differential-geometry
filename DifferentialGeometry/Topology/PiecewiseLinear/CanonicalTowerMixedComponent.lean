/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerMixedAnnulus
import DifferentialGeometry.Topology.PiecewiseLinear.TorusAnnulusNullCircleComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.CircleCappingComponentInvariants
import DifferentialGeometry.Topology.Connected.Frontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.exists_mixed_oddPiece_component
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    ∃ (Glo Ghi : Set E3) (x : E3),
      Glo ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i)) ∧
      Ghi ∈ traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn Glo (T'' (2 * i + 1)) ∧
      ¬ boundsDiskIn Ghi (T'' (2 * i + 1)) ∧ x ∈ canonicalOddPiece S'' T'' i ∧
      Glo ∪ Ghi ⊆ connectedComponentIn (canonicalOddPiece S'' T'' i) x := by
  classical
  obtain ⟨Glo, Ghi, B, hlo, hhi, hloe, hhie, hB, hBT, hBdis, -, -, hcomp⟩ :=
    htw.exists_mixed_oddPiece_annulus i
  let Γ := {G ∈ oddTorusSeams T'' i | ¬ boundsDiskIn G (T'' (2 * i + 1))}
  let Λ := {G ∈ oddTorusSeams T'' i | boundsDiskIn G (T'' (2 * i + 1))}
  have hΛfin : Λ.Finite := (htw.finite_oddTorusSeams i).subset fun _ hG => hG.1
  let _ := hΛfin.to_subtype
  have hlo' : Glo ∈ traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) := by
    simpa only [traceCircles, htw.oddPiece_inter_even, inter_comm] using hlo
  have hhi' : Ghi ∈ traceCircles (T'' (2 * i + 1)) (T'' (2 * (i + 1))) := by
    simpa only [traceCircles, htw.oddPiece_inter_even] using hhi
  let lo : Γ := ⟨Glo, Or.inl hlo', hloe⟩
  let hi : Γ := ⟨Ghi, Or.inr hhi', hhie⟩
  have hΓsphere : ∀ G : Γ, IsPLSphere 1 (G : Set E3) := by
    intro G
    rcases G.property.1 with hG | hG
    · exact traceCircles_isPLSphere hG
    · exact traceCircles_isPLSphere hG
  have hΓsub : ∀ G : Γ, (G : Set E3) ⊆ T'' (2 * i + 1) := by
    intro G
    rcases G.property.1 with hG | hG
    · exact (traceCircles_subset hG).trans inter_subset_right
    · exact (traceCircles_subset hG).trans inter_subset_left
  have hΛdis : Pairwise fun G H : Λ => Disjoint (G : Set E3) (H : Set E3) := by
    intro G H hne
    exact htw.oddTorusSeams_pairwiseDisjoint i G.property.1 H.property.1
      (fun heq => hne (Subtype.ext heq))
  have hΛΓ : ∀ (G : Λ) (H : Γ), Disjoint (G : Set E3) (H : Set E3) := by
    intro G H
    apply htw.oddTorusSeams_pairwiseDisjoint i G.property.1 H.property.1
    intro heq
    exact H.property.2 (heq ▸ G.property.2)
  have hunion : (⋃ G : Γ, (G : Set E3)) = ⋃ G ∈ Γ, G := by
    ext x
    simp only [mem_iUnion, Subtype.exists, exists_prop]
  have hcomp' : ∀ x ∈ B \ ((lo : Set E3) ∪ hi),
      connectedComponentIn (T'' (2 * i + 1) \ ⋃ G : Γ, (G : Set E3)) x =
        B \ ((lo : Set E3) ∪ hi) := by
    rw [hunion]
    exact hcomp
  obtain ⟨U, hU, hUB, hUnull, hends⟩ :=
    (htw.boundary_isPLTorus (2 * i + 1)).exists_connected_annulus_subset_avoiding_null_circles
      (fun G : Γ => (G : Set E3)) hΓsphere hΓsub (fun G => G.property.2)
      (i₀ := lo) (i₁ := hi) hB hcomp' (fun G : Λ => (G : Set E3)) hΛdis hΛΓ
      (fun G => G.property.2)
  have hUT : U ⊆ T'' (2 * i + 1) := hUB.trans (sdiff_subset.trans hBT)
  have hUdis : ∀ G ∈ oddTorusSeams T'' i, Disjoint U G := by
    intro G hG
    by_cases hnull : boundsDiskIn G (T'' (2 * i + 1))
    · exact hUnull.mono Subset.rfl (subset_iUnion (fun H : Λ => (H : Set E3)) ⟨G, hG, hnull⟩)
    · exact hBdis.mono hUB fun x hx => mem_iUnion₂.mpr ⟨G, ⟨hG, hnull⟩, hx⟩
  have hUlo : Disjoint U (frontier (S'' (2 * i))) := by
    rw [← htw.boundary_eq]
    apply disjoint_left.mpr
    intro x hxU hxT
    obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp
      ((htw.traceCircles_cover (2 * i)).subset ⟨hxT, hUT hxU⟩)
    exact disjoint_left.mp (hUdis G (Or.inl hG)) hxU hxG
  have hUhi : Disjoint U (frontier (S'' (2 * (i + 1)))) := by
    rw [← htw.boundary_eq]
    apply disjoint_left.mpr
    intro x hxU hxT
    have hcover : T'' (2 * i + 1) ∩ T'' (2 * (i + 1)) =
        ⋃ G ∈ traceCircles (T'' (2 * i + 1)) (T'' (2 * (i + 1))), G := by
      simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using
        htw.traceCircles_cover (2 * i + 1)
    obtain ⟨G, hG, hxG⟩ := mem_iUnion₂.mp (hcover.subset ⟨hUT hxU, hxT⟩)
    exact disjoint_left.mp (hUdis G (Or.inr hG)) hxU hxG
  have houtside (k : ℤ) (H : Set E3) (hH : H.Nonempty) (hHcl : H ⊆ closure U)
      (hHR : Disjoint H (S'' k)) (hUR : Disjoint U (frontier (S'' k))) :
      Disjoint U (interior (S'' k)) := by
    apply disjoint_left.mpr
    intro x hxU hxI
    have hUI : U ⊆ interior (S'' k) :=
      DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
        hU.isPreconnected hUR ⟨x, hxU, hxI⟩
    have hcl : closure U ⊆ S'' k :=
      closure_minimal (hUI.trans interior_subset) (htw.solid_isPolyhedron k).isClosed
    obtain ⟨y, hy⟩ := hH
    exact disjoint_left.mp hHR hy (hcl (hHcl hy))
  have hsolidDis : Disjoint (S'' (2 * i)) (S'' (2 * (i + 1))) :=
    htw.solid_disjoint (by rw [le_abs]; omega)
  have hloSub : Glo ⊆ S'' (2 * i) :=
    (traceCircles_subset hlo).trans (inter_subset_right.trans (htw.boundary_subset_solid _))
  have hhiSub : Ghi ⊆ S'' (2 * (i + 1)) :=
    (traceCircles_subset hhi).trans (inter_subset_right.trans (htw.boundary_subset_solid _))
  have hlow := houtside (2 * i) Ghi (traceCircles_isPLSphere hhi).nonempty
    (subset_union_right.trans hends) (hsolidDis.symm.mono hhiSub Subset.rfl) hUlo
  have hhigh := houtside (2 * (i + 1)) Glo (traceCircles_isPLSphere hlo).nonempty
    (subset_union_left.trans hends) (hsolidDis.mono hloSub Subset.rfl) hUhi
  have hUrow : U ⊆ canonicalOddPiece S'' T'' i := by
    intro x hx
    refine ⟨hUT hx, ?_⟩
    rintro (hxl | hxh)
    · exact disjoint_left.mp hlow hx hxl
    · exact disjoint_left.mp hhigh hx (by
        simpa only [show 2 * (i + 1) = 2 * i + 2 by omega] using hxh)
  have hclRow : closure U ⊆ canonicalOddPiece S'' T'' i :=
    closure_minimal hUrow (htw.oddPiece_isPolyhedron i).isClosed
  obtain ⟨x, hx⟩ := hU.nonempty
  exact ⟨Glo, Ghi, x, hlo, hhi, hloe, hhie, hUrow hx,
    hends.trans (hU.closure.isPreconnected.subset_connectedComponentIn (subset_closure hx) hclRow)⟩

theorem IsCanonicalTower.exists_oddPiece_component_with_essential_seams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (X : Geometry.SimplicialComplex ℝ E3)
    (hX : X.space = canonicalOddPiece S'' T'' i) :
    ∃ (c : ConnectedComponents X.space) (Glo Ghi : Set E3),
      Glo ∈ traceCircles (connectedComponentComplex X c).space (T'' (2 * i)) ∧
      Ghi ∈ traceCircles (connectedComponentComplex X c).space (T'' (2 * (i + 1))) ∧
      ¬ boundsDiskIn Glo (T'' (2 * i + 1)) ∧ ¬ boundsDiskIn Ghi (T'' (2 * i + 1)) := by
  obtain ⟨Glo, Ghi, x, hlo, hhi, hloe, hhie, hx, hmarks⟩ :=
    htw.exists_mixed_oddPiece_component i
  let p : X.space := ⟨x, hX.symm ▸ hx⟩
  let c := ConnectedComponents.mk p
  have hspace : (connectedComponentComplex X c).space =
      connectedComponentIn (canonicalOddPiece S'' T'' i) x := by
    rw [connectedComponentComplex_mk, restrict_connectedComponentIn_space]
    change connectedComponentIn X.space x = _
    rw [hX]
  have hsub : (connectedComponentComplex X c).space ⊆ X.space := by
    rw [hspace, hX]
    exact connectedComponentIn_subset _ _
  have hloX : Glo ∈ traceCircles X.space (T'' (2 * i)) := hX.symm ▸ hlo
  have hhiX : Ghi ∈ traceCircles X.space (T'' (2 * (i + 1))) := hX.symm ▸ hhi
  refine ⟨c, Glo, Ghi, (mem_traceCircles_iff_subset hloX hsub).mpr ?_,
    (mem_traceCircles_iff_subset hhiX hsub).mpr ?_, hloe, hhie⟩
  · rw [hspace]
    exact subset_union_left.trans hmarks
  · rw [hspace]
    exact subset_union_right.trans hmarks

end DifferentialGeometry.Topology.PiecewiseLinear
