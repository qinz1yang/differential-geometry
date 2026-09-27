/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalClosedComponentDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalWindowComponentClassification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalClosedWindowReduction [DecidableEq E3]
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' T : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) (F : Set E3) : Prop where
  source : IsCanonicalSurface X S' T I P' a b
  target : IsCanonicalSurface Y S' T I P' a b
  embeddings : ∀ i, HasEssentialBoundaryPLEmbeddings (Y i) (T (2 * i + 1))
  closedFree : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    (boundaryComplex 2 (connectedComponentComplex (Y i) c)).space ≠ ∅
  steps : Relation.ReflTransGen (fun U V =>
    IsCanonicalSurface U S' T I P' a b ∧ IsCanonicalSurface V S' T I P' a b ∧
      ∃ i ∈ rows, ∃ c : ConnectedComponents (U i).space,
        (boundaryComplex 2 (connectedComponentComplex (U i) c)).space = ∅ ∧
        IsCanonicalClosedDeletion i U V ∧
        IsTypeOneDeletion I {a} {b} (connectedComponentComplex (U i) c).space
          (towerSurface T (fun j => (V j).space) P')
          (towerSurface T (fun j => (U j).space) P')
          (towerSurface T (fun j => (V j).space) P') F) X Y
  pieceSubset : ∀ i, (Y i).space ⊆ (X i).space
  unchanged : ∀ i, i ∉ rows → Y i = X i
  boundary : ∀ i, (boundaryComplex 2 (Y i)).space = (boundaryComplex 2 (X i)).space
  evenTrace : ∀ i k, (Y i).space ∩ T (2 * k) = (X i).space ∩ T (2 * k)
  nullRankEq : ∀ window, windowNullRank Y T window = windowNullRank X T window
  componentEmbedding : ∀ i,
    ∃ e : ConnectedComponents (Y i).space ↪ ConnectedComponents (X i).space,
      ∀ c, (connectedComponentComplex (Y i) c).space =
        (connectedComponentComplex (X i) (e c)).space
  fixedSet : towerSurface T (fun i => (Y i).space) P' ∩ F =
    towerSurface T (fun i => (X i).space) P' ∩ F
  rankLE : windowComponentRank Y rows ≤ windowComponentRank X rows

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_window_closed_reduction [d : DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (hmodel : ∀ i, HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)))
    (rows : Finset ℤ) {F : Set E3}
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalClosedWindowReduction X Y (fun i => φ '' S i) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  induction hn : windowComponentRank X rows using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hdone : ∀ i ∈ rows, ∀ c : ConnectedComponents (X i).space,
        (boundaryComplex 2 (connectedComponentComplex (X i) c)).space ≠ ∅
    · exact ⟨X,
        { source := hX
          target := hX
          embeddings := hmodel
          closedFree := hdone
          steps := Relation.ReflTransGen.refl
          pieceSubset := fun _ => Subset.rfl
          unchanged := fun _ _ => rfl
          boundary := fun _ => rfl
          evenTrace := fun _ _ => rfl
          nullRankEq := fun _ => rfl
          componentEmbedding := fun _ => ⟨Function.Embedding.refl _, fun _ => rfl⟩
          fixedSet := rfl
          rankLE := le_rfl }⟩
    · push Not at hdone
      obtain ⟨i, hi, c, hclosed⟩ := hdone
      have hsub : (connectedComponentComplex (X i) c).space ⊆
          (X i).space \ (boundaryComplex 2 (X i)).space := by
        intro x hx
        refine ⟨(iUnion_connectedComponentComplex_space (X i)).subset
          (mem_iUnion.mpr ⟨c, hx⟩), ?_⟩
        intro hxB
        have hxC := (boundaryComplex_space_connectedComponentComplex 2 (X i) c).symm.subset
          ⟨hxB, hx⟩
        exact notMem_empty x (hclosed ▸ hxC)
      obtain ⟨X₁, hX₁, hstep, hdel⟩ :=
        IsCanonicalSurface.exists_closed_component_deletion_step ht hu hv huv he htw havoid
          hX i c hclosed ((hF i hi).mono_right hsub)
      have hmodel₁ := hstep.preserves_subsurface_embeddings hX hX₁ hmodel
      have hF₁ : ∀ j ∈ rows, Disjoint F ((X₁ j).space \ (boundaryComplex 2 (X₁ j)).space) := by
        intro j hj
        apply (hF j hj).mono_right
        rw [hstep.boundary_eq htw hX hX₁ j]
        exact sdiff_subset_sdiff (hstep.space_subset j) Subset.rfl
      have hlt : windowComponentRank X₁ rows < n := hn ▸ hstep.windowComponentRank_lt hi
      obtain ⟨Y, hred⟩ := ih (windowComponentRank X₁ rows) hlt hX₁ hmodel₁ hF₁ rfl
      have hfix : towerSurface T'' (fun j => (X₁ j).space) P' ∩ F =
          towerSurface T'' (fun j => (X j).space) P' ∩ F := by
        obtain ⟨-, -, -, -, -, -, -, hfix⟩ := hdel
        exact hfix
      refine ⟨Y,
        { source := hX
          target := hred.target
          embeddings := hred.embeddings
          closedFree := hred.closedFree
          steps := ?_
          pieceSubset := fun j => (hred.pieceSubset j).trans (hstep.space_subset j)
          unchanged := ?_
          boundary := fun j => (hred.boundary j).trans (hstep.boundary_eq htw hX hX₁ j)
          evenTrace := fun j k => (hred.evenTrace j k).trans (hstep.inter_even_eq htw hX j k)
          nullRankEq := fun window => (hred.nullRankEq window).trans
            (hstep.windowNullRank_eq htw hX window)
          componentEmbedding := ?_
          fixedSet := hred.fixedSet.trans hfix
          rankLE := hred.rankLE.trans (hstep.windowComponentRank_lt hi).le }⟩
      · apply Relation.ReflTransGen.trans ?_ hred.steps
        exact Relation.ReflTransGen.single ⟨hX, hX₁, i, hi, c, hclosed, hstep, hdel⟩
      · intro j hj
        exact (hred.unchanged j hj).trans (hstep.unchanged j (fun hji => hj (hji.symm ▸ hi)))
      · intro j
        obtain ⟨e₁, he₁⟩ := hstep.exists_component_embedding j
        obtain ⟨e₂, he₂⟩ := hred.componentEmbedding j
        exact ⟨e₂.trans e₁, fun c => (he₂ c).trans (he₁ (e₂ c))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
