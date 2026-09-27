/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalAnnularWindow
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceComponentRemoval

open Set
open scoped BigOperators

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalComponentDeletion (i : ℤ)
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3)
    (c : ConnectedComponents (X i).space) : Prop where
  unchanged : ∀ j, j ≠ i → Y j = X j
  space : (Y i).space = (X i).space \ (connectedComponentComplex (X i) c).space
  retained : ∃ e : {q : ConnectedComponents (X i).space // q ≠ c} ≃
      ConnectedComponents (Y i).space,
    ∀ q, (connectedComponentComplex (Y i) (e q)).space =
      (connectedComponentComplex (X i) q).space
  componentCount : Nat.card (ConnectedComponents (Y i).space) + 1 =
    Nat.card (ConnectedComponents (X i).space)

variable {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}
  {c : ConnectedComponents (X i).space}

theorem IsCanonicalComponentDeletion.space_subset
    (h : IsCanonicalComponentDeletion i X Y c) (j : ℤ) : (Y j).space ⊆ (X j).space := by
  classical
  by_cases hji : j = i
  · subst j
    exact h.space.subset.trans sdiff_subset
  · rw [h.unchanged j hji]

theorem IsCanonicalComponentDeletion.windowComponentRank_lt
    (h : IsCanonicalComponentDeletion i X Y c) {rows : Finset ℤ} (hi : i ∈ rows) :
    windowComponentRank Y rows < windowComponentRank X rows := by
  classical
  have hlt : Nat.card (ConnectedComponents (Y i).space) <
      Nat.card (ConnectedComponents (X i).space) := by
    have hc := h.componentCount
    omega
  unfold windowComponentRank
  apply Finset.sum_lt_sum ?_ ⟨i, hi, hlt⟩
  intro j _
  by_cases hji : j = i
  · exact hji ▸ hlt.le
  · exact (congrArg (fun Q : Geometry.SimplicialComplex ℝ E3 =>
      Nat.card (ConnectedComponents Q.space)) (h.unchanged j hji)).le

theorem IsCanonicalComponentDeletion.exists_component_embedding
    (h : IsCanonicalComponentDeletion i X Y c) (j : ℤ) :
    ∃ e : ConnectedComponents (Y j).space ↪ ConnectedComponents (X j).space,
      ∀ q, (connectedComponentComplex (Y j) q).space =
        (connectedComponentComplex (X j) (e q)).space := by
  classical
  by_cases hji : j = i
  · subst j
    obtain ⟨e, he⟩ := h.retained
    refine ⟨⟨fun q => (e.symm q).val, ?_⟩, ?_⟩
    · intro q r hqr
      exact e.symm.injective (Subtype.ext hqr)
    · intro q
      change (connectedComponentComplex (Y i) q).space =
        (connectedComponentComplex (X i) (e.symm q).val).space
      simpa only [e.apply_symm_apply] using he (e.symm q)
  · rw [h.unchanged j hji]
    exact ⟨Function.Embedding.refl _, fun _ => rfl⟩

variable [DecidableEq E3] {S' S'' T'' : ℤ → Set E3} {I : Set E3} {P' a b : E3}

theorem IsCanonicalComponentDeletion.boundary_eq_sdiff
    (h : IsCanonicalComponentDeletion i X Y c)
    (hX : IsCanonicalSurface X S' T'' I P' a b)
    (hY : IsCanonicalSurface Y S' T'' I P' a b) :
    (boundaryComplex 2 (Y i)).space =
      (boundaryComplex 2 (X i)).space \ (connectedComponentComplex (X i) c).space := by
  rw [hY.boundary i, h.space, hX.boundary i]
  ext x
  exact ⟨fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩,
    fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩⟩

theorem IsCanonicalComponentDeletion.adjacent_trace_subset
    (h : IsCanonicalComponentDeletion i X Y c)
    (hX : IsCanonicalSurface X S' T'' I P' a b) (k : ℤ) :
    traceCircles ((Y (k - 1)).space ∪ (Y k).space) (T'' (2 * k)) ⊆
      traceCircles ((X (k - 1)).space ∪ (X k).space) (T'' (2 * k)) :=
  traceCircles_subset_of_inter_subset (hX.adjacentTrace k).traceCover
    (inter_subset_inter_left _ (union_subset_union (h.space_subset _) (h.space_subset _)))

theorem IsCanonicalComponentDeletion.windowNullRank_le
    (h : IsCanonicalComponentDeletion i X Y c)
    (hX : IsCanonicalSurface X S' T'' I P' a b) (window : Finset ℤ) :
    windowNullRank Y T'' window ≤ windowNullRank X T'' window := by
  unfold windowNullRank
  exact Finset.sum_le_sum fun k _ =>
    nullTraceCount_le_of_traceCircles_subset (hX.adjacentTrace k).finiteTrace
      (h.adjacent_trace_subset hX k)

theorem IsCanonicalAnnularWindow.of_component_deletion
    {rows : Finset ℤ} (hX : IsCanonicalAnnularWindow X S' S'' T'' I P' a b rows)
    (hd : IsCanonicalComponentDeletion i X Y c)
    (hY : IsCanonicalSurface Y S' T'' I P' a b) :
    IsCanonicalAnnularWindow Y S' S'' T'' I P' a b rows := by
  refine
    { surface := hY
      embeddings := ?_
      nullRank := Nat.eq_zero_of_le_zero ((hd.windowNullRank_le hX.surface _).trans_eq hX.nullRank)
      generators := fun k hk G hG => hX.generators k hk G
        (hd.adjacent_trace_subset hX.surface k hG)
      components := ?_ }
  · intro j
    let _ : Finite (X j).faces := (hX.surface.finiteFaces j).to_subtype
    let _ : Finite (Y j).faces := (hY.finiteFaces j).to_subtype
    obtain ⟨e, he⟩ := hd.exists_component_embedding j
    exact HasEssentialBoundaryPLEmbeddings.of_component_space_eq (X j) (Y j)
      (hX.surface.manifold j) (hX.embeddings j) e he
  · intro j hj q
    obtain ⟨e, he⟩ := hd.exists_component_embedding j
    simpa only [he q] using hX.components j hj (e q)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T : ℤ → Set E3}
  {Dimg Dbdimg W : Set E3}

theorem IsCanonicalComponentDeletion.towerSurface_eq_sdiff_interior
    (hd : IsCanonicalComponentDeletion i X Y c)
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    towerSurface T'' (fun j => (Y j).space) P' =
      towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \
          (boundaryComplex 2 (connectedComponentComplex (X i) c)).space) := by
  have hCX : (connectedComponentComplex (X i) c).space ⊆ (X i).space :=
    (subset_iUnion (fun q => (connectedComponentComplex (X i) q).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hbd := boundaryComplex_space_connectedComponentComplex 2 (X i) c
  have htorus (k : ℤ) {x : E3} (hx : x ∈ T'' (2 * k)) :
      x ∉ (connectedComponentComplex (X i) c).space \
        (boundaryComplex 2 (connectedComponentComplex (X i) c)).space := by
    rintro ⟨hxC, hxB⟩
    exact hxB (hbd.symm.subset ⟨hX.inter_even_subset_boundary htw i k ⟨hCX hxC, hx⟩, hxC⟩)
  ext x
  constructor
  · rintro (hx | hxP)
    · obtain ⟨j, hxT | hxY⟩ := mem_iUnion.mp hx
      · exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxT⟩), htorus j hxT⟩
      · refine ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inr (hd.space_subset j hxY)⟩), ?_⟩
        rintro ⟨hxC, -⟩
        by_cases hji : j = i
        · subst j
          exact (hd.space.subset hxY).2 hxC
        · exact disjoint_left.mp (hX.piecesDisjoint hji) (hd.space_subset j hxY) (hCX hxC)
    · refine ⟨Or.inr hxP, ?_⟩
      rintro ⟨hxC, -⟩
      exact hX.centerNotMem i (hxP ▸ hCX hxC)
  · rintro ⟨hx | hxP, hxnot⟩
    · obtain ⟨j, hxT | hxX⟩ := mem_iUnion.mp hx
      · exact Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxT⟩)
      · by_cases hji : j = i
        · subst j
          by_cases hxC : x ∈ (connectedComponentComplex (X i) c).space
          · have hxB : x ∈ (boundaryComplex 2 (X i)).space :=
              (hbd.subset (by by_contra h; exact hxnot ⟨hxC, h⟩)).1
            rcases ((hX.boundary i).subset hxB).2 with hxlo | hxhi
            · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inl hxlo⟩)
            · exact Or.inl (mem_iUnion.mpr ⟨i + 1, Or.inl hxhi⟩)
          · exact Or.inl (mem_iUnion.mpr ⟨i, Or.inr (hd.space.symm.subset ⟨hxX, hxC⟩)⟩)
        · apply Or.inl
          refine mem_iUnion.mpr ⟨j, Or.inr ?_⟩
          simpa only [hd.unchanged j hji] using hxX
    · exact Or.inr hxP

theorem IsCanonicalComponentDeletion.towerSurface_inter_eq
    (hd : IsCanonicalComponentDeletion i X Y c)
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {F : Set E3} (hF : Disjoint F ((connectedComponentComplex (X i) c).space \
      (boundaryComplex 2 (connectedComponentComplex (X i) c)).space)) :
    towerSurface T'' (fun j => (Y j).space) P' ∩ F =
      towerSurface T'' (fun j => (X j).space) P' ∩ F := by
  rw [hd.towerSurface_eq_sdiff_interior hX htw]
  ext x
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
    fun hx => ⟨⟨hx.1, disjoint_left.mp hF hx.2⟩, hx.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
