/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerDiskPair
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamPolyhedral
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem exists_polyhedral_initialSurface_split (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3))
    (hcl : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (h303 : Moise303) (i : ℤ)
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (j : ℤ) (G M L' U : Set E3), (j = i - 1 ∨ j = i) ∧
      G ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) ∧
      IsOpen U ∧ U ⊆ interior (h '' C u ∪ h '' C v) ∧
      IsSeparatorIn (interior (h '' C u ∪ h '' C v)) M {h u} {h v} ∧
      P' ∈ M ∧ M ⊆ interior (h '' C u ∪ h '' C v) ∧
      M \ U = initialSurface S'' T'' P' \ U ∧
      M = (initialSurface S'' T'' P' \ (T'' (2 * i) ∪ canonicalOddPiece S'' T'' j)) ∪
        (T'' (2 * i) ∪ L') ∧
      L' ⊆ φ '' S (2 * i) ∪ φ '' S (2 * j + 1) ∧
      L' \ U = canonicalOddPiece S'' T'' j \ U ∧
      traceCircles L' (T'' (2 * i)) =
        traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) \ {G} ∧
      nullTraceCount L' (T'' (2 * i)) <
        nullTraceCount (canonicalOddPiece S'' T'' j) (T'' (2 * i)) ∧ IsPolyhedron L' := by
  let I := interior (h '' C u ∪ h '' C v)
  let M₀ := initialSurface S'' T'' P'
  obtain ⟨j, Δ, U, D₁, D₂, r, r₁, r₂, hj, hG, hr, hΔT, hU, hΔU, hUI, hUouter,
      hUavoid, hRU, hr₁, hr₂, hΔ₁, hΔ₂, hpair, hD₁T, hD₂T, hsub, hnear, hisolated⟩ :=
    htw.exists_innermost_disk_pair_with_trace i (havoid (2 * i)) hnull
  let L := canonicalOddPiece S'' T'' j
  let R := M₀ \ (T'' (2 * i) ∪ L)
  have hTL : T'' (2 * i) ∪ L ⊆ M₀ := by
    rw [show M₀ = initialSurface S'' T'' P' from rfl, htw.initialSurface_eq_iUnion]
    rintro x (hx | hx)
    · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inl hx⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨j, Or.inr hx⟩)
  have hCeq : R ∪ (T'' (2 * i) ∪ L) = M₀ := by
    apply Subset.antisymm (union_subset sdiff_subset hTL)
    intro x hx
    by_cases hxTL : x ∈ T'' (2 * i) ∪ L
    · exact Or.inr hxTL
    · exact Or.inl ⟨hx, hxTL⟩
  have hM₀I : M₀ ⊆ I := by
    rw [show M₀ = initialSurface S'' T'' P' from rfl, htw.initialSurface_eq_iUnion]
    refine union_subset (iUnion_subset fun l => union_subset ?_ ?_)
      (singleton_subset_iff.mpr htw.centerMemInterior)
    · exact (htw.boundary_subset_outer _).trans (htw.subsetInterior _)
    · intro x hx
      exact htw.subsetInterior _ (htw.boundary_subset_outer _ hx.1)
  have hP₀ : P' ∈ M₀ := Or.inr rfl
  have huI : h u ∈ I := interior_mono subset_union_left (ht.mem_interior_image_dualCell hu)
  have hvI : h v ∈ I := interior_mono subset_union_right (ht.mem_interior_image_dualCell hv)
  have huv' : h u ≠ h v := fun heq => huv (ht.injOn
    (ht.dualCell_subset hu (interior_subset (ht.mem_interior_dualCell hu)))
    (ht.dualCell_subset hv (interior_subset (ht.mem_interior_dualCell hv))) heq)
  have hfin : (traceCircles L (T'' (2 * i))).Finite := by
    rcases hj with hj | hj
    · dsimp [L]
      rw [hj]
      simpa only [sub_add_cancel] using htw.finite_oddPiece_traceCircles_upper (i - 1)
    · dsimp [L]
      rw [hj]
      exact htw.finite_oddPiece_traceCircles_lower i
  have hcover : L ∩ T'' (2 * i) = ⋃ G ∈ traceCircles L (T'' (2 * i)), G := by
    dsimp [L]
    simp only [traceCircles, htw.oddPiece_inter_even]
    rcases hj with hj | hj
    · rw [hj, show 2 * (i - 1) + 1 = 2 * i - 1 by omega]
      simpa only [traceCircles, sub_add_cancel] using htw.traceCircles_cover (2 * i - 1)
    · rw [hj]
      simpa only [traceCircles, inter_comm] using htw.traceCircles_cover (2 * i)
  have hUHK : Disjoint U (({h u} : Set E3) ∪ {h v}) := by
    apply disjoint_left.mpr
    intro x hxU hxHK
    exact disjoint_left.mp hUavoid hxU (Or.inr (by simpa only [mem_union, mem_singleton_iff,
      mem_insert_iff] using hxHK))
  have hFU : Disjoint ({P'} : Set E3) U := disjoint_left.mpr fun x hxP hxU =>
    disjoint_left.mp hUavoid hxU (Or.inl hxP)
  obtain ⟨M, L', hMsep, hprot, hMeq, -, hseams, hdecrease, hL'out, hL'poly⟩ :=
    exists_polyhedral_disk_split_reducing_seams h303 I {h u} {h v} R (T'' (2 * i)) L Δ D₁ D₂ U {P'}
      r r₁ r₂ isOpen_interior (ht.isConnected_interior_image_pair hu hv huv he)
      (singleton_subset_iff.mpr huI) (singleton_subset_iff.mpr hvI)
      (by simpa only [disjoint_singleton_left, mem_singleton_iff] using huv')
      (isClosed_singleton.preimage continuous_subtype_val)
      (isClosed_singleton.preimage continuous_subtype_val)
      (by rw [hCeq]; exact hM₀I) (by rw [hCeq]; exact ⟨hcl, hsep⟩)
      hr hΔT hr₁ hr₂ hpair hD₁T
      (by rw [hCeq]; exact hsub.trans inter_subset_left)
      (by rw [hCeq]; exact hnear) hΔ₁ hΔ₂ hU hΔU hUI hUHK hRU hFU hfin hcover hG
      (htw.oddPiece_isPolyhedron j) hD₂T hisolated
  have hout : M \ U = M₀ \ U := by simpa only [hCeq] using hprot.1
  have hP : P' ∈ M := by
    have hp : P' ∈ M ∩ {P'} := hprot.2.symm.subset
      ⟨hCeq.symm ▸ hP₀, mem_singleton _⟩
    exact hp.1
  have hMI : M ⊆ I := by
    intro x hxM
    by_cases hxU : x ∈ U
    · exact hUI hxU
    · exact hM₀I (hout.subset ⟨hxM, hxU⟩).1
  have hL'carrier : L' ⊆ φ '' S (2 * i) ∪ φ '' S (2 * j + 1) := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl (hUouter hxU)
    · have hxL : x ∈ L := (hL'out.subset ⟨hx, hxU⟩).1
      exact Or.inr (htw.boundary_subset_outer _ hxL.1)
  exact ⟨j, r '' stdSimplexBoundary 2, M, L', U, hj, hG, hU, hUI, hMsep, hP, hMI,
    hout, hMeq, hL'carrier, hL'out, hseams, hdecrease, hL'poly⟩

open Classical in
theorem exists_initialSurface_split (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3))
    (hcl : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (h303 : Moise303) (i : ℤ)
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (j : ℤ) (G M L' U : Set E3), (j = i - 1 ∨ j = i) ∧
      G ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) ∧
      IsOpen U ∧ U ⊆ interior (h '' C u ∪ h '' C v) ∧
      IsSeparatorIn (interior (h '' C u ∪ h '' C v)) M {h u} {h v} ∧
      P' ∈ M ∧ M ⊆ interior (h '' C u ∪ h '' C v) ∧
      M \ U = initialSurface S'' T'' P' \ U ∧
      M = (initialSurface S'' T'' P' \ (T'' (2 * i) ∪ canonicalOddPiece S'' T'' j)) ∪
        (T'' (2 * i) ∪ L') ∧
      L' ⊆ φ '' S (2 * i) ∪ φ '' S (2 * j + 1) ∧
      L' \ U = canonicalOddPiece S'' T'' j \ U ∧
      traceCircles L' (T'' (2 * i)) =
        traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) \ {G} ∧
      nullTraceCount L' (T'' (2 * i)) <
        nullTraceCount (canonicalOddPiece S'' T'' j) (T'' (2 * i)) := by
  obtain ⟨j, G, M, L', U, hj, hG, hU, hUI, hMsep, hP, hMI, hout, heq,
      hcarrier, hL'out, hseams, hdecrease, -⟩ :=
    exists_polyhedral_initialSurface_split ht hu hv huv he htw havoid hcl hsep h303 i hnull
  exact ⟨j, G, M, L', U, hj, hG, hU, hUI, hMsep, hP, hMI, hout, heq,
    hcarrier, hL'out, hseams, hdecrease⟩

end DifferentialGeometry.Topology.PiecewiseLinear
