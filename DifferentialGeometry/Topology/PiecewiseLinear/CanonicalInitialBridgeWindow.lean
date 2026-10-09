/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeNormalization
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerMixedComponent

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalTower.exists_initial_bridge_window [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (hcl : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    (rows : Finset ℤ) {F : Set E3}
    (hFO : ∀ i ∈ towerWindowSeams rows, Disjoint F (interior (φ '' S (2 * i))))
    (hF : ∀ i ∈ rows, Disjoint F
      (canonicalOddPiece S'' T'' i \ (T'' (2 * i) ∪ T'' (2 * (i + 1))))) :
    ∃ X Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      (∀ i, (X i).space = canonicalOddPiece S'' T'' i) ∧
      towerSurface T'' (fun i => (X i).space) P' = initialSurface S'' T'' P' ∧
      IsCanonicalBridgeNormalization X Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F := by
  obtain ⟨X, hX, hspace⟩ := htw.exists_initial_surface_state (h u) (h v) hcl hsep
  have hmodel (i : ℤ) : HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)) := by
    let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
    apply HasEssentialBoundaryPLEmbeddings.of_subset (X i)
    rw [hspace i]
    exact sdiff_subset
  have hwitness : HasCanonicalBridgeWitnesses X T'' := fun i =>
    htw.exists_oddPiece_component_with_essential_seams i (X i) (hspace i)
  have hXF (i : ℤ) (hi : i ∈ rows) :
      Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space) := by
    apply (hF i hi).mono_right
    intro x hx
    refine ⟨(hspace i).subset hx.1, ?_⟩
    intro hxt
    exact hx.2 ((hX.boundary i).symm.subset ⟨hx.1, hxt⟩)
  obtain ⟨Y, hnorm⟩ := hX.exists_window_bridge_normalization ht hu hv huv he htw havoid
    h303 h286 h314 hmodel hwitness rows hFO hXF
  refine ⟨X, Y, hspace, ?_, hnorm⟩
  rw [htw.initialSurface_eq_iUnion]
  simp only [towerSurface, hspace]

end DifferentialGeometry.Topology.PiecewiseLinear
