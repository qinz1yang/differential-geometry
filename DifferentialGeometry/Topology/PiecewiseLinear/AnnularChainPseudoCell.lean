/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCell
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRim
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainTopology
import DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSphereImageSplitRim
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellBallPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem isOpenTopologicalCell_annularChain (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' annularChain H B P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v})) :
    IsOpenTopologicalCell 2 (annularChain H B P') ∧
    IsLocallyPolyhedral (annularChain H B P' \ {P'}) ∧
    closure (annularChain H B P') = annularChain H B P' ∪ h '' Dbd {u, v} ∧
    ∀ x ∈ annularChain H B P' \ {P'}, ∃ Q₁ Q₂ DQ : Set E3,
      IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧ Q₁ ∩ Q₂ = DQ ∧ IsPLBall 2 DQ ∧
      DQ ⊆ annularChain H B P' \ {P'} ∧ Q₁ ∪ Q₂ ∈ 𝓝 x ∧
      Q₁ ∪ Q₂ ⊆ interior (h '' C u ∪ h '' C v) ∧
      (Q₁ ∪ Q₂) ∩ (annularChain H B P' ∪ h '' Dbd {u, v}) = DQ := by
  have hR := ht.splitRim_subset_closure_annularChain hu hv huv he hP' htw hch
  have hcell := ht.isOpenTopologicalCell_annularChain hu hv huv he hP' htw hch
  have hlp := hch.locallyPolyhedral_off_center htw
  have hsub := hch.annularChain_subset_interior htw
  have hclosed : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      annularChain H B P') := by
    obtain ⟨U, V, hU, hV, -, hcover, -, -⟩ := hsep
    rw [← isOpen_compl_iff, ← hcover]
    exact hU.union hV
  have hcover : closure (annularChain H B P') ⊆
      interior (h '' C u ∪ h '' C v) ∪ h '' Dbd {u, v} :=
    (hch.closure_annularChain_subset htw).trans (union_subset_union hsub subset_rfl)
  have hbound : closure (annularChain H B P') ⊆
      annularChain H B P' ∪ h '' Dbd {u, v} := by
    intro x hx
    rcases hcover hx with hxI | hxR
    · apply Or.inl
      apply isClosed_preimage_val.mp hclosed
      exact ⟨hxI, by simpa only [inter_eq_right.mpr hsub] using hx⟩
    · exact Or.inr hxR
  have hclos : closure (annularChain H B P') =
      annularChain H B P' ∪ h '' Dbd {u, v} :=
    Subset.antisymm hbound (union_subset subset_closure hR)
  have hpair : h '' C u ∪ h '' C v ⊆ N' := by
    rw [ht.imageEq]
    exact union_subset (image_mono (ht.dualCell_subset hu))
      (image_mono (ht.dualCell_subset hv))
  have hdis : Disjoint (annularChain H B P') (h '' Dbd {u, v}) :=
    (ht.disjoint_image_rim_interior he (Finset.card_pair huv)).symm.mono_left
      (hsub.trans (interior_mono hpair))
  have hpc : IsPseudoCell (annularChain H B P' ∪ h '' Dbd {u, v})
      (annularChain H B P') (h '' Dbd {u, v}) P' :=
    ⟨rfl, hcell, isTopologicalSphere_image_splitRim ht he (Finset.card_pair huv),
      hdis, hclos, Or.inr rfl, hlp⟩
  refine ⟨hcell, hlp, hclos, fun x hx => ?_⟩
  exact hpc.exists_isPLBall_neighborhood_pair hx (isOpen_interior.mem_nhds (hsub hx.1))

end DifferentialGeometry.Topology.PiecewiseLinear
