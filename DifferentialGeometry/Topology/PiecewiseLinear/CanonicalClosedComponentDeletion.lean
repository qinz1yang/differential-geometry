/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentSubsurfaceRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceClosedDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceLocality

open Set
open scoped BigOperators

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable def windowComponentRank (X : ℤ → Geometry.SimplicialComplex ℝ E3)
    (rows : Finset ℤ) : ℕ := ∑ i ∈ rows, Nat.card (ConnectedComponents (X i).space)

structure IsCanonicalClosedDeletion [DecidableEq E3] (i : ℤ)
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) : Prop where
  unchanged : ∀ j, j ≠ i → Y j = X j
  removed : ∃ c : ConnectedComponents (X i).space,
    (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅ ∧
    (Y i).space = (X i).space \ (connectedComponentComplex (X i) c).space ∧
    ∃ e : {q : ConnectedComponents (X i).space // q ≠ c} ≃ ConnectedComponents (Y i).space,
      ∀ q, (connectedComponentComplex (Y i) (e q)).space =
        (connectedComponentComplex (X i) q).space
  componentCount : Nat.card (ConnectedComponents (Y i).space) + 1 =
    Nat.card (ConnectedComponents (X i).space)

variable [DecidableEq E3] {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}

theorem IsCanonicalClosedDeletion.space_subset (h : IsCanonicalClosedDeletion i X Y) (j : ℤ) :
    (Y j).space ⊆ (X j).space := by
  by_cases hji : j = i
  · subst j
    obtain ⟨c, -, hspace, -⟩ := h.removed
    exact hspace.subset.trans sdiff_subset
  · rw [h.unchanged j hji]

theorem IsCanonicalClosedDeletion.windowComponentRank_lt
    (h : IsCanonicalClosedDeletion i X Y) {rows : Finset ℤ} (hi : i ∈ rows) :
    windowComponentRank Y rows < windowComponentRank X rows := by
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

theorem IsCanonicalClosedDeletion.exists_component_embedding
    (h : IsCanonicalClosedDeletion i X Y) (j : ℤ) :
    ∃ e : ConnectedComponents (Y j).space ↪ ConnectedComponents (X j).space,
      ∀ c, (connectedComponentComplex (Y j) c).space =
        (connectedComponentComplex (X j) (e c)).space := by
  by_cases hji : j = i
  · subst j
    obtain ⟨c, -, -, e, he⟩ := h.removed
    refine ⟨⟨fun q => (e.symm q).val, ?_⟩, ?_⟩
    · intro q r hqr
      exact e.symm.injective (Subtype.ext hqr)
    · intro q
      change (connectedComponentComplex (Y i) q).space =
        (connectedComponentComplex (X i) (e.symm q).val).space
      simpa only [e.apply_symm_apply] using he (e.symm q)
  · rw [h.unchanged j hji]
    exact ⟨Function.Embedding.refl _, fun _ => rfl⟩

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalClosedDeletion.inter_even_eq (h : IsCanonicalClosedDeletion i X Y)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b) (j k : ℤ) :
    (Y j).space ∩ T'' (2 * k) = (X j).space ∩ T'' (2 * k) := by
  by_cases hji : j = i
  · subst j
    obtain ⟨c, hclosed, hspace, -⟩ := h.removed
    have hdis := hX.closed_component_disjoint_even htw i c hclosed k
    rw [hspace]
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, disjoint_left.mp hdis.symm hx.2⟩, hx.2⟩⟩
  · rw [h.unchanged j hji]

theorem IsCanonicalClosedDeletion.boundary_eq (h : IsCanonicalClosedDeletion i X Y)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b) (j : ℤ) :
    (boundaryComplex 2 (Y j)).space = (boundaryComplex 2 (X j)).space := by
  rw [hY.boundary j, hX.boundary j, inter_union_distrib_left, inter_union_distrib_left,
    h.inter_even_eq htw hX j j, h.inter_even_eq htw hX j (j + 1)]

theorem IsCanonicalClosedDeletion.windowNullRank_eq (h : IsCanonicalClosedDeletion i X Y)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b) (window : Finset ℤ) :
    windowNullRank Y T'' window = windowNullRank X T'' window := by
  unfold windowNullRank
  apply Finset.sum_congr rfl
  intro k _
  apply nullTraceCount_eq_of_inter_eq
  rw [union_inter_distrib_right, union_inter_distrib_right,
    h.inter_even_eq htw hX (k - 1) k, h.inter_even_eq htw hX k k]

theorem IsCanonicalClosedDeletion.preserves_subsurface_embeddings
    (h : IsCanonicalClosedDeletion i X Y)
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b)
    (hmodel : ∀ j, HasEssentialBoundaryPLEmbeddings (X j) (T'' (2 * j + 1))) :
    ∀ j, HasEssentialBoundaryPLEmbeddings (Y j) (T'' (2 * j + 1)) := by
  intro j
  by_cases hji : j = i
  · subst j
    let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
    let _ : Finite (Y i).faces := (hY.finiteFaces i).to_subtype
    obtain ⟨c, -, -, e, he⟩ := h.removed
    apply HasEssentialBoundaryPLEmbeddings.of_component_space_eq (X i) (Y i)
      (hX.manifold i) (hmodel i) (fun q => (e.symm q).val)
    intro q
    simpa only [e.apply_symm_apply] using he (e.symm q)
  · rw [h.unchanged j hji]
    exact hmodel j

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}

open Classical in
theorem IsCanonicalSurface.exists_closed_component_deletion_step
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3))
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (i : ℤ) (c : ConnectedComponents (X i).space)
    (hclosed : (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅)
    {F : Set E3} (hF : Disjoint F (connectedComponentComplex (X i) c).space) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalSurface Y (fun j => φ '' S j) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
      IsCanonicalClosedDeletion i X Y ∧
      IsTypeOneDeletion (interior (h '' C u ∪ h '' C v)) {h u} {h v}
        (connectedComponentComplex (X i) c).space (towerSurface T'' (fun j => (Y j).space) P')
        (towerSurface T'' (fun j => (X j).space) P')
        (towerSurface T'' (fun j => (Y j).space) P') F := by
  obtain ⟨Y, hY, hother, hspace, hcount, hdel⟩ :=
    IsCanonicalSurface.exists_delete_closed_component ht hu hv huv he htw havoid hX i c hclosed hF
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let _ : Finite (Y i).faces := (hY.finiteFaces i).to_subtype
  let _ : Finite (ConnectedComponents (X i).space) := finite_connectedComponents_space (X i)
  let _ (q : ConnectedComponents (X i).space) :
      Finite (connectedComponentComplex (X i) q).faces :=
    (connectedComponentComplex_faces_finite (X i) q).to_subtype
  have hcover : (Y i).space =
      ⋃ q : {q : ConnectedComponents (X i).space // q ≠ c},
        (connectedComponentComplex (X i) q).space :=
    hspace.trans (sdiff_connectedComponentComplex_space (X i) c)
  obtain ⟨e, heq⟩ := exists_equiv_connectedComponents_of_finite_partition (Y i)
    (fun q : {q : ConnectedComponents (X i).space // q ≠ c} =>
      (connectedComponentComplex (X i) q).space)
    (fun q => isConnected_connectedComponentComplex_space (X i) q)
    (fun q => (isPolyhedron_space (connectedComponentComplex (X i) q)).isClosed)
    (fun q r hqr => pairwise_disjoint_connectedComponentComplex_space (X i)
      (fun heq => hqr (Subtype.ext heq))) hcover
  exact ⟨Y, hY,
    { unchanged := hother
      removed := ⟨c, hclosed, hspace, e, heq⟩
      componentCount := hcount }, hdel⟩

end DifferentialGeometry.Topology.PiecewiseLinear
