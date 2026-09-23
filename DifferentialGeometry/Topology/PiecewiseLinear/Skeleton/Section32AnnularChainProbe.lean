/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainLocalPolyhedral

/-!
# Reconnaissance of the annular-chain topology leaf

The four geometric conclusions are isolated without changing the frozen
Section 32 statement. The chain's PL annuli and interior containment are
proved in the imported real module.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.Section32AnnularChainProbe

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
  {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h φ : E3 → E3}
  {u v P' : E3} {W : Set E3}
  {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

local notation "chain" => annularChain H B P'
local notation "pairInterior" => interior (h '' C u ∪ h '' C v)

theorem open_cell_of_two_ends
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W pairInterior P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hsep : Separates (((↑) : pairInterior → E3) ⁻¹' chain)
      (((↑) : pairInterior → E3) ⁻¹' {h u})
      (((↑) : pairInterior → E3) ⁻¹' {h v})) :
    IsOpenTopologicalCell 2 chain := by
  sorry

theorem locally_polyhedral_off_center
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W pairInterior P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    IsLocallyPolyhedral (chain \ {P'}) := by
  exact hch.locallyPolyhedral_off_center htw

theorem closure_adds_intrinsic_rim
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W pairInterior P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hsep : Separates (((↑) : pairInterior → E3) ⁻¹' chain)
      (((↑) : pairInterior → E3) ⁻¹' {h u})
      (((↑) : pairInterior → E3) ⁻¹' {h v})) :
    closure chain = chain ∪ h '' Dbd {u, v} := by
  sorry

theorem local_two_ball_pair
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W pairInterior P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hsep : Separates (((↑) : pairInterior → E3) ⁻¹' chain)
      (((↑) : pairInterior → E3) ⁻¹' {h u})
      (((↑) : pairInterior → E3) ⁻¹' {h v})) :
    ∀ x ∈ chain \ {P'}, ∃ Q₁ Q₂ DQ : Set E3,
      IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧ Q₁ ∩ Q₂ = DQ ∧ IsPLBall 2 DQ ∧
      DQ ⊆ chain \ {P'} ∧ Q₁ ∪ Q₂ ∈ 𝓝 x ∧
      Q₁ ∪ Q₂ ⊆ pairInterior ∧
      (Q₁ ∪ Q₂) ∩ (chain ∪ h '' Dbd {u, v}) = DQ := by
  sorry

theorem annular_chain_topology_of_subleaves
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W pairInterior P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hsep : Separates (((↑) : pairInterior → E3) ⁻¹' chain)
      (((↑) : pairInterior → E3) ⁻¹' {h u})
      (((↑) : pairInterior → E3) ⁻¹' {h v})) :
    IsOpenTopologicalCell 2 chain ∧
    IsLocallyPolyhedral (chain \ {P'}) ∧
    closure chain = chain ∪ h '' Dbd {u, v} ∧
    ∀ x ∈ chain \ {P'}, ∃ Q₁ Q₂ DQ : Set E3,
      IsPLBall 3 Q₁ ∧ IsPLBall 3 Q₂ ∧ Q₁ ∩ Q₂ = DQ ∧ IsPLBall 2 DQ ∧
      DQ ⊆ chain \ {P'} ∧ Q₁ ∪ Q₂ ∈ 𝓝 x ∧
      Q₁ ∪ Q₂ ⊆ pairInterior ∧
      (Q₁ ∪ Q₂) ∩ (chain ∪ h '' Dbd {u, v}) = DQ := by
  exact ⟨open_cell_of_two_ends ht hu hv huv he hP' htw hch hsep,
    locally_polyhedral_off_center htw hch,
    closure_adds_intrinsic_rim ht hu hv huv he hP' htw hch hsep,
    local_two_ball_pair ht hu hv huv he hP' htw hch hsep⟩

end DifferentialGeometry.Topology.PiecewiseLinear.Section32AnnularChainProbe
