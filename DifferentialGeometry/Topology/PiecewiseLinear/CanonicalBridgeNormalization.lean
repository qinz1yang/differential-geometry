/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeWitnesses

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalBridgeNormalization [DecidableEq E3]
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' S'' T : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) (F : Set E3) : Prop where
  source : IsCanonicalSurface X S' T I P' a b
  target : IsCanonicalAnnularWindow Y S' S'' T I P' a b rows
  bridgeWitnesses : HasCanonicalBridgeWitnesses Y T
  bridgeComponents : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    IsCanonicalBridgeComponent Y T i c
  singleComponent : ∀ i ∈ rows, Nat.card (ConnectedComponents (Y i).space) = 1
  stages : ∃ U V Z : ℤ → Geometry.SimplicialComplex ℝ E3,
    IsCanonicalWindowClassification X U S' S'' T I P' a b rows F ∧
    IsCanonicalClosedWindowReduction U V S' T I P' a b rows F ∧
    IsCanonicalReturningWindowReduction V Z S' S'' T I P' a b rows F ∧
    IsCanonicalBridgeWindowReduction Z Y S' S'' T I P' a b rows F
  unchanged : ∀ i, i ∉ towerWindowSeams rows → i + 1 ∉ towerWindowSeams rows → Y i = X i
  fixedSet : towerSurface T (fun i => (Y i).space) P' ∩ F =
    towerSurface T (fun i => (X i).space) P' ∩ F

theorem IsCanonicalSurface.disjoint_row_interior_of_space_subset [DecidableEq E3]
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I F : Set E3} {P' a b : E3}
    (hX : IsCanonicalSurface X S' T I P' a b)
    (hY : IsCanonicalSurface Y S' T I P' a b) (i : ℤ)
    (hsub : (Y i).space ⊆ (X i).space)
    (hF : Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    Disjoint F ((Y i).space \ (boundaryComplex 2 (Y i)).space) := by
  apply hF.mono_right
  rintro x ⟨hx, hxB⟩
  refine ⟨hsub hx, ?_⟩
  intro hxB'
  exact hxB ((hY.boundary i).symm.subset ⟨hx, ((hX.boundary i).subset hxB').2⟩)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_window_bridge_normalization [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (hmodel : ∀ i, HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)))
    (hwitness : HasCanonicalBridgeWitnesses X T'') (rows : Finset ℤ) {F : Set E3}
    (hFO : ∀ i ∈ towerWindowSeams rows, Disjoint F (interior (φ '' S (2 * i))))
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalBridgeNormalization X Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F := by
  obtain ⟨U, hclass⟩ := hX.exists_window_component_classification ht hu hv huv he htw
    havoid h303 h286 h314 hmodel rows hFO
  have hUF := hclass.disjoint_row_interiors hFO hF
  have hUw := hwitness.of_null_splits htw h314 (towerWindowSeams rows) hclass.splits
  obtain ⟨V, hclosed, hV⟩ := hclass.exists_annular_window ht hu hv huv he htw havoid hUF
  have hVw := hUw.of_closed_reduction hclosed
  have hVF (i : ℤ) (hi : i ∈ rows) :=
    hclass.target.disjoint_row_interior_of_space_subset hclosed.target i
      (hclosed.pieceSubset i) (hUF i hi)
  obtain ⟨Z, hreturn⟩ := hV.exists_window_returning_reduction htw h314 isOpen_interior
    havoid hVF
  have hZw := hVw.of_returning_reduction htw hreturn
  have hZF (i : ℤ) (hi : i ∈ rows) :=
    hV.surface.disjoint_row_interior_of_space_subset hreturn.target.surface i
      (hreturn.pieceSubset i) (hVF i hi)
  obtain ⟨Y, hbridge⟩ := hreturn.target.exists_window_bridge_reduction htw h314 isOpen_interior
    havoid hreturn.bridge_components (fun i _ => hZw.nonempty_components i) hZF
  refine ⟨Y,
    { source := hX
      target := hbridge.target
      bridgeWitnesses := hZw.of_bridge_reduction hbridge
      bridgeComponents := hbridge.bridgeComponents
      singleComponent := hbridge.singleComponent
      stages := ⟨U, V, Z, hclass, hclosed, hreturn, hbridge⟩
      unchanged := ?_
      fixedSet := hbridge.fixedSet.trans
        (hreturn.fixedSet.trans (hclosed.fixedSet.trans hclass.fixedSet)) }⟩
  intro i hi hi₁
  have hir : i ∉ rows := fun hir => hi (Finset.mem_union_left _ hir)
  exact (hbridge.unchanged i hir).trans ((hreturn.unchanged i hir).trans
    ((hclosed.unchanged i hir).trans (hclass.unchanged i hi hi₁)))

end DifferentialGeometry.Topology.PiecewiseLinear
