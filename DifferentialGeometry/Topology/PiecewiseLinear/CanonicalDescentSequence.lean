/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSeedDescentSequence
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerMixedComponent
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningWitnessTransport
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningExteriorComponentDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem exists_descentSequence (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (hcl : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (h303 : Moise303) (h286 : Moise286) (h267 : Moise267) (h314 : Moise314) :
    ∃ (H B Jlo Jhi : ℤ → Set E3) (M : ℕ → Set E3),
      IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P' ∧
      M 0 = initialSurface S'' T'' P' ∧
      (∀ n, IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' M n)) ∧
      (∀ n, Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' M n)
        (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
        (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v})) ∧
      (∀ n, P' ∈ M n) ∧
      IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' annularChain H B P') ∧
      ∀ x ∈ interior (h '' C u ∪ h '' C v), x ≠ P' →
        ∃ U ∈ 𝓝 x, ∃ n₀ : ℕ, ∀ n ≥ n₀, M n ∩ U = annularChain H B P' ∩ U := by
  rcases hP' with rfl
  obtain ⟨X₀, U, Y, hspace, -, hclass, hclosed, hY, -⟩ :=
    IsCanonicalTower.exists_initial_annular_window ht hu hv huv he htw havoid hcl hsep
      h303 h286 h314 {0} (F := ∅) (fun _ _ => empty_disjoint _) (fun _ _ => empty_disjoint _)
  have hwitness₀ : HasCanonicalBridgeWitnesses X₀ T'' := fun i =>
    htw.exists_oddPiece_component_with_essential_seams i (X₀ i) (hspace i)
  have hwitness :=
    (hwitness₀.of_null_splits htw h314 (towerWindowSeams {0}) hclass.splits).of_closed_reduction
      hclosed
  have hseed : ∃ Z : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalAnnularWindow Z (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v))
        (h (({u, v} : Finset E3).centroid ℝ id)) (h u) (h v) {0} ∧
      HasCanonicalBridgeWitnesses Z T'' := by
    by_cases hreturn : ∃ c : ConnectedComponents (Y 0).space,
        IsCanonicalReturningComponent Y T'' 0 c
    · obtain ⟨c, hc⟩ := hreturn
      obtain ⟨k, G₀, G₁, hk, hC, hdis, h₀, h₁, he₀, he₁⟩ := hc
      obtain ⟨Z, -, -, hZ, hd, -⟩ :=
        hY.exists_returning_component_deletion_of_moise267 htw h314 h267 isOpen_interior
          havoid 0 c hC hdis k hk h₀ h₁ he₀ he₁ (F := ∅) (empty_disjoint _)
      exact ⟨Z, hZ,
        hwitness.of_returning_component_deletion hY.surface htw 0 c
          ⟨k, G₀, G₁, hk, hC, hdis, h₀, h₁, he₀, he₁⟩ hd⟩
    · exact ⟨Y, hY, hwitness⟩
  obtain ⟨Z, hZ, hZw⟩ := hseed
  obtain ⟨H, B, Jlo, Jhi, M, hchain, -, hM, hMP, hlimit, hlocal⟩ :=
    hZ.surface.exists_annular_chain_sequence ht hu hv huv he htw havoid h303 h286 h314
      hZ.embeddings hZw
  let M' : ℕ → Set E3 := fun n => match n with
    | 0 => initialSurface S'' T'' (h (({u, v} : Finset E3).centroid ℝ id))
    | n + 1 => M n
  refine ⟨H, B, Jlo, Jhi, M', hchain, rfl, ?_, ?_, ?_, hlimit, ?_⟩
  · intro n
    cases n with
    | zero => exact hcl
    | succ n => exact (hM n).1
  · intro n
    cases n with
    | zero => exact hsep
    | succ n => exact (hM n).2
  · intro n
    cases n with
    | zero => exact Or.inr rfl
    | succ n => exact hMP n
  · intro x hx hxP
    obtain ⟨U, hU, N, hN⟩ := hlocal x hx hxP
    refine ⟨U, hU, N + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n => exact hN n (by omega)

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
