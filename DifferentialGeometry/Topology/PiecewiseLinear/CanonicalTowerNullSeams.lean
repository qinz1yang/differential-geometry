/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerWindowSurface
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurfaceNullSeams
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerInnermostSeam
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem exists_initialSurface_orientable_nullTraceCount_eq_zero
    [d : DecidableEq E3] (ht : IsTube K N C D Dbd h N')
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
    (h303 : Moise303) (i : ℤ) :
    ∃ (M : Set E3) (Q : Geometry.SimplicialComplex ℝ E3) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ IsOrientable 2 Q ∧
      HasFiniteCollaredTrace Q.space (T'' (2 * i)) ∧
      nullTraceCount Q.space (T'' (2 * i)) = 0 ∧
      IsSeparatorIn (interior (h '' C u ∪ h '' C v)) M {h u} {h v} ∧
      P' ∈ M ∧ M ⊆ interior (h '' C u ∪ h '' C v) ∧
      M \ interior (φ '' S (2 * i)) = initialSurface S'' T'' P' \ interior (φ '' S (2 * i)) ∧
      M = (initialSurface S'' T'' P' \ (T'' (2 * i) ∪
        (canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i))) ∪
          (T'' (2 * i) ∪ Q.space) ∧
      Q.space ⊆ (φ '' S (2 * i - 1) ∪ φ '' S (2 * i)) ∪ φ '' S (2 * i + 1) ∧
      Q.space \ interior (φ '' S (2 * i)) =
        (canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i) \
          interior (φ '' S (2 * i)) ∧
      traceCircles Q.space (T'' (2 * i)) ⊆ evenTorusSeams T'' i ∧
      (boundaryComplex 2 Q).space ∩ interior (φ '' S (2 * i)) ⊆ T'' (2 * i) ∧
      (boundaryComplex 2 Q).space ⊆
        (canonicalOddPiece S'' T'' (i - 1) ∩ (T'' (2 * i - 2) ∪ T'' (2 * i))) ∪
          (canonicalOddPiece S'' T'' i ∩ (T'' (2 * i) ∪ T'' (2 * i + 2))) ∧
      (boundaryComplex 2 Q).space \ interior (φ '' S (2 * i)) =
        ((canonicalOddPiece S'' T'' (i - 1) ∩ (T'' (2 * i - 2) ∪ T'' (2 * i))) ∪
          (canonicalOddPiece S'' T'' i ∩ (T'' (2 * i) ∪ T'' (2 * i + 2)))) \
            interior (φ '' S (2 * i)) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let I := interior (h '' C u ∪ h '' C v)
  let M₀ := initialSurface S'' T'' P'
  let L := canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i
  let R := M₀ \ (T'' (2 * i) ∪ L)
  let O := interior (φ '' S (2 * i))
  have hleft := htw.hasFiniteCollaredTrace_oddPiece i (i - 1) (Or.inl rfl)
  have hright := htw.hasFiniteCollaredTrace_oddPiece i i (Or.inr rfl)
  have hdis : Disjoint (canonicalOddPiece S'' T'' (i - 1)) (canonicalOddPiece S'' T'' i) :=
    (htw.apart (2 * (i - 1) + 1) (2 * i + 1) (by rw [le_abs]; omega)).mono
      (fun x hx => htw.boundary_subset_outer _ hx.1)
      (fun x hx => htw.boundary_subset_outer _ hx.1)
  have hstate : HasFiniteCollaredTrace L (T'' (2 * i)) := hleft.union_of_disjoint hright hdis
  obtain ⟨X, hXfin, hX, hXo, hXspace, hXb, hBoundary⟩ := htw.exists_adjacentOdd_surface i
  let _ : Finite X.faces := hXfin.to_subtype
  have hstateX : HasFiniteCollaredTrace X.space (T'' (2 * i)) := hXspace.symm ▸ hstate
  have hTL : T'' (2 * i) ∪ L ⊆ M₀ := by
    rw [show M₀ = initialSurface S'' T'' P' from rfl, htw.initialSurface_eq_iUnion]
    rintro x (hx | hx | hx)
    · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inl hx⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i - 1, Or.inr hx⟩)
    · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inr hx⟩)
  have hCeq : R ∪ (T'' (2 * i) ∪ L) = M₀ := by
    refine Subset.antisymm (union_subset sdiff_subset hTL) ?_
    intro x hx
    by_cases hxTL : x ∈ T'' (2 * i) ∪ L
    · exact Or.inr hxTL
    · exact Or.inl ⟨hx, hxTL⟩
  have hM₀I : M₀ ⊆ I := by
    rw [show M₀ = initialSurface S'' T'' P' from rfl, htw.initialSurface_eq_iUnion]
    refine union_subset (iUnion_subset fun k => union_subset ?_ ?_)
      (singleton_subset_iff.mpr htw.centerMemInterior)
    · exact (htw.boundary_subset_outer _).trans (htw.subsetInterior _)
    · exact fun x hx => htw.subsetInterior _ (htw.boundary_subset_outer _ hx.1)
  have hTO : T'' (2 * i) ⊆ O := by
    have hinner : S'' (2 * i) ⊆ O := by
      simpa [O] using (htw.config (2 * i)).innerSubset 0
    exact (htw.boundary_subset_solid _).trans hinner
  have hRO : Disjoint R O := by
    apply disjoint_left.mpr
    rintro x ⟨hxM, hxTL⟩ hxO
    rw [show M₀ = initialSurface S'' T'' P' from rfl, htw.initialSurface_eq_iUnion] at hxM
    rcases hxM with hxM | hxP
    · obtain ⟨k, hxT | hxL⟩ := mem_iUnion.mp hxM
      · have hki : k = i := by
          by_contra hne
          exact disjoint_left.mp (htw.apart (2 * i) (2 * k) (by rw [le_abs]; omega))
            (interior_subset hxO) (htw.boundary_subset_outer _ hxT)
        exact hxTL (Or.inl (hki ▸ hxT))
      · have hki : k = i - 1 ∨ k = i := by
          by_contra hne
          push Not at hne
          exact disjoint_left.mp (htw.apart (2 * i) (2 * k + 1) (by rw [le_abs]; omega))
            (interior_subset hxO) (htw.boundary_subset_outer _ hxL.1)
        exact hxTL (Or.inr (hki.elim (fun he => Or.inl (he ▸ hxL))
          (fun he => Or.inr (he ▸ hxL))))
    · exact htw.center_notMem_interior_outer _ (hxP ▸ hxO)
  have hFO : Disjoint ({P'} : Set E3) O := disjoint_left.mpr fun x hx hxO =>
    htw.center_notMem_interior_outer _ (hx ▸ hxO)
  have hOHK : Disjoint O (({h u} : Set E3) ∪ {h v}) := by
    apply disjoint_left.mpr
    intro x hxO hxV
    exact disjoint_left.mp (havoid (2 * i)) (interior_subset hxO)
      (by simpa only [mem_union, mem_insert_iff, mem_singleton_iff] using hxV)
  have huI : h u ∈ I := interior_mono subset_union_left (ht.mem_interior_image_dualCell hu)
  have hvI : h v ∈ I := interior_mono subset_union_right (ht.mem_interior_image_dualCell hv)
  have huv' : h u ≠ h v := fun heq => huv (ht.injOn
    (ht.dualCell_subset hu (interior_subset (ht.mem_interior_dualCell hu)))
    (ht.dualCell_subset hv (interior_subset (ht.mem_interior_dualCell hv))) heq)
  obtain ⟨Q, hQfin, -, hQ, hQo, hstate', hsep', hMI, hprot, hout, hsub, hzero,
      hQboundary, hBsub, hBout, -, -⟩ :=
    hX.exists_separating_nullTraceCount_eq_zero X hXo hstateX
      (htw.boundary_isPLTorus (2 * i)) h303 isOpen_interior
      (ht.isConnected_interior_image_pair hu hv huv (by
        exact (congrArg (fun d : DecidableEq E3 =>
          @insert E3 (Finset E3) (@Finset.instInsert E3 d) u {v} ∈ K.faces)
            (Subsingleton.elim _ _)).mp he))
      (singleton_subset_iff.mpr huI) (singleton_subset_iff.mpr hvI)
      (by simpa only [disjoint_singleton_left, mem_singleton_iff] using huv')
      (isClosed_singleton.preimage continuous_subtype_val)
      (isClosed_singleton.preimage continuous_subtype_val)
      (by rw [hXspace, hCeq]; exact hM₀I) (by rw [hXspace, hCeq]; exact ⟨hcl, hsep⟩)
      isOpen_interior hTO (interior_subset.trans (htw.subsetInterior _)) hOHK hRO hFO hBoundary
  let _ : Finite Q.faces := hQfin.to_subtype
  let L' := Q.space
  rw [hXspace] at hprot hout hsub
  have hP : P' ∈ R ∪ (T'' (2 * i) ∪ L') :=
    (hprot.2.symm.subset ⟨hCeq.symm ▸ (show P' ∈ M₀ from Or.inr rfl), rfl⟩).1
  refine ⟨R ∪ (T'' (2 * i) ∪ L'), Q, hQfin, hQ, hQo, hstate', hzero, hsep', hP, hMI,
    hprot.1.trans (congrArg (fun Z : Set E3 => Z \ O) hCeq), rfl, ?_, hout, ?_, hQboundary,
    hBsub.trans hXb.subset, ?_⟩
  · intro x hxL'
    by_cases hxO : x ∈ O
    · exact Or.inl (Or.inr (interior_subset hxO))
    · have hxL : x ∈ L := (hout.subset ⟨hxL', hxO⟩).1
      rcases hxL with hxL | hxL
      · exact Or.inl (Or.inl (by
          simpa only [show 2 * (i - 1) + 1 = 2 * i - 1 by omega] using
            htw.boundary_subset_outer _ hxL.1))
      · exact Or.inr (htw.boundary_subset_outer _ hxL.1)
  · have heq := traceCircles_eq_union_of_disjoint hleft.finiteTrace hright.finiteTrace
      hleft.traceCover hright.traceCover hdis
    intro G hG
    rcases heq.subset (hsub hG) with hG | hG
    · left
      simpa only [traceCircles, htw.oddPiece_inter_even,
        show 2 * (i - 1) + 1 = 2 * i - 1 by omega] using hG
    · right
      simpa only [traceCircles, htw.oddPiece_inter_even, inter_comm] using hG
  · rw [hXb] at hBout
    exact hBout

open Classical in
theorem exists_initialSurface_nullTraceCount_eq_zero (ht : IsTube K N C D Dbd h N')
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
    (h303 : Moise303) (i : ℤ) :
    ∃ M L' : Set E3, HasFiniteCollaredTrace L' (T'' (2 * i)) ∧
      nullTraceCount L' (T'' (2 * i)) = 0 ∧
      IsSeparatorIn (interior (h '' C u ∪ h '' C v)) M {h u} {h v} ∧
      P' ∈ M ∧ M ⊆ interior (h '' C u ∪ h '' C v) ∧
      M \ interior (φ '' S (2 * i)) = initialSurface S'' T'' P' \ interior (φ '' S (2 * i)) ∧
      M = (initialSurface S'' T'' P' \ (T'' (2 * i) ∪
        (canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i))) ∪
          (T'' (2 * i) ∪ L') ∧
      L' ⊆ (φ '' S (2 * i - 1) ∪ φ '' S (2 * i)) ∪ φ '' S (2 * i + 1) ∧
      L' \ interior (φ '' S (2 * i)) =
        (canonicalOddPiece S'' T'' (i - 1) ∪ canonicalOddPiece S'' T'' i) \
          interior (φ '' S (2 * i)) ∧
      traceCircles L' (T'' (2 * i)) ⊆ evenTorusSeams T'' i := by
  obtain ⟨M, Q, -, -, -, hstate, hzero, hsep', hP, hMI, hout, heq,
      hcarrier, hLout, htrace, -, -, -⟩ :=
    exists_initialSurface_orientable_nullTraceCount_eq_zero ht hu hv huv he htw havoid hcl
      hsep h303 i
  exact ⟨M, Q.space, hstate, hzero, hsep', hP, hMI, hout, heq, hcarrier, hLout, htrace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
