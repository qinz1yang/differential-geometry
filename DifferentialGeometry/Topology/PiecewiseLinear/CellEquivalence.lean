/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CellComplex
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Finite ι]

open Classical in
theorem isGlueIso_cellDerived_of_cellsOf_eq
    (l : ι → E →ᵃ[ℝ] ℝ) (P : Set E) (m : ι → F →ᵃ[ℝ] ℝ) (Q : Set F)
    (hcells : cellsOf l P = cellsOf m Q) :
    IsGlueIso (cellDerived l P) (cellDerived m Q)
      (cellPt m Q ∘ signVec l) (cellPt l P ∘ signVec m) := by
  classical
  have hforward : ∀ s ∈ (cellDerived l P).faces,
      s.image (cellPt m Q ∘ signVec l) ∈ (cellDerived m Q).faces := by
    rintro s ⟨d, hd, hne, rfl⟩
    refine ⟨d, ⟨fun σ hσ => hcells.subset (hd.mem_cells hσ), hd.2⟩, hne, ?_⟩
    rw [Finset.image_image]
    exact Finset.image_congr fun σ hσ =>
      congrArg (cellPt m Q) (cellPt_mem_openCell l P (hd.mem_cells hσ))
  have hback : ∀ t ∈ (cellDerived m Q).faces,
      t.image (cellPt l P ∘ signVec m) ∈ (cellDerived l P).faces := by
    rintro t ⟨d, hd, hne, rfl⟩
    refine ⟨d, ⟨fun σ hσ => hcells.symm.subset (hd.mem_cells hσ), hd.2⟩, hne, ?_⟩
    rw [Finset.image_image]
    exact Finset.image_congr fun σ hσ =>
      congrArg (cellPt l P) (cellPt_mem_openCell m Q (hd.mem_cells hσ))
  refine ⟨hforward, hback, ?_, ?_⟩
  · rintro s ⟨d, hd, -, rfl⟩ v hv
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hv
    simp only [Function.comp_apply,
      show signVec l (cellPt l P σ) = σ from cellPt_mem_openCell l P (hd.mem_cells hσ),
      show signVec m (cellPt m Q σ) = σ from
        cellPt_mem_openCell m Q (hcells.subset (hd.mem_cells hσ))]
  · rintro t ⟨d, hd, -, rfl⟩ v hv
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hv
    simp only [Function.comp_apply,
      show signVec m (cellPt m Q σ) = σ from cellPt_mem_openCell m Q (hd.mem_cells hσ),
      show signVec l (cellPt l P σ) = σ from
        cellPt_mem_openCell l P (hcells.symm.subset (hd.mem_cells hσ))]

open Classical in
theorem signLE_signVec_simplicialMap_cellDerived
    (l : ι → E →ᵃ[ℝ] ℝ) (P : Set E) (m : ι → F →ᵃ[ℝ] ℝ) (Q : Set F)
    (hcells : cellsOf l P ⊆ cellsOf m Q) {x : E} (hx : x ∈ (cellDerived l P).space) :
    SignLE (signVec m (simplicialMap (cellDerived l P) (cellPt m Q ∘ signVec l) x))
      (signVec l x) := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex (cellDerived l P) hx
  obtain ⟨d, hd, hne, rfl⟩ := hs
  obtain ⟨τ, hτ, htop⟩ := hd.exists_top hne
  have hxsign : signVec l x = τ := mem_openCell_top l P hd hτ htop hxs
  rw [hxsign]
  apply convexHull_min ?_ (convex_closedCell m τ)
    (simplicialMap_mem_convexHull_image (cellDerived l P) _ ⟨d, hd, hne, rfl⟩
      (openSimplex_subset_convexHull _ hxs))
  intro y hy
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hv
  change cellPt m Q (signVec l (cellPt l P σ)) ∈ closedCell m τ
  rw [show signVec l (cellPt l P σ) = σ from cellPt_mem_openCell l P (hd.mem_cells hσ)]
  exact cellPt_mem_closedCell m Q (hcells (hd.mem_cells hσ)) (htop σ hσ)

theorem exists_isPLHomeomorphOn_of_cellsOf_eq [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (l : ι → E →ᵃ[ℝ] ℝ) (P : Set E) (m : ι → F →ᵃ[ℝ] ℝ) (Q : Set F)
    (hP : IsCellClosed l P) (hPc : IsCompact P) (hQ : IsCellClosed m Q) (hQc : IsCompact Q)
    (hcells : cellsOf l P = cellsOf m Q) :
    ∃ f : E → F, IsPLHomeomorphOn f P Q ∧ ∀ x ∈ P, signVec m (f x) = signVec l x := by
  classical
  let K := cellDerived l P
  let L := cellDerived m Q
  let _ : Finite K.faces := (finite_cellDerived_faces l P).to_subtype
  let _ : Finite L.faces := (finite_cellDerived_faces m Q).to_subtype
  let φ := cellPt m Q ∘ signVec l
  let ψ := cellPt l P ∘ signVec m
  have hiso : IsGlueIso K L φ ψ := isGlueIso_cellDerived_of_cellsOf_eq l P m Q hcells
  have hKspace : K.space = P := space_cellDerived l P hP hPc
  have hLspace : L.space = Q := space_cellDerived m Q hQ hQc
  have hf := hiso.isPLHomeomorphOn
  refine ⟨simplicialMap K φ, hKspace ▸ hLspace ▸ hf, ?_⟩
  intro x hx
  have hxK : x ∈ K.space := hKspace.symm ▸ hx
  have hleft := signLE_signVec_simplicialMap_cellDerived l P m Q hcells.subset hxK
  have hright := signLE_signVec_simplicialMap_cellDerived m Q l P hcells.symm.subset
    (hf.bijOn.mapsTo hxK)
  have hinv := simplicialMap_simplicialMap K L φ ψ hiso.image₁ hiso.left hxK
  change SignLE (signVec l (simplicialMap L ψ (simplicialMap K φ x)))
    (signVec m (simplicialMap K φ x)) at hright
  rw [hinv] at hright
  exact hleft.antisymm hright

end DifferentialGeometry.Topology.PiecewiseLinear
