/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningComponentDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalReturningWindowReduction [DecidableEq E3]
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' S'' T : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) (F : Set E3) : Prop where
  source : IsCanonicalAnnularWindow X S' S'' T I P' a b rows
  target : IsCanonicalAnnularWindow Y S' S'' T I P' a b rows
  returningFree : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    ¬ IsCanonicalReturningComponent Y T i c
  steps : Relation.ReflTransGen (fun U V =>
    IsCanonicalAnnularWindow U S' S'' T I P' a b rows ∧
    IsCanonicalAnnularWindow V S' S'' T I P' a b rows ∧
      ∃ i ∈ rows, ∃ c : ConnectedComponents (U i).space,
        IsCanonicalReturningComponent U T i c ∧ IsCanonicalComponentDeletion i U V c ∧
        ∃ (k : ℤ) (J₀ J₁ B₀ B₁ : Set E3), (k = i ∨ k = i + 1) ∧
          IsReturningAnnulusDeletion I {a} {b} (connectedComponentComplex (U i) c).space
            J₀ J₁ (T (2 * k)) B₀ B₁ (towerSurface T (fun j => (U j).space) P')
            (towerSurface T (fun j => (V j).space) P') F) X Y
  pieceSubset : ∀ i, (Y i).space ⊆ (X i).space
  unchanged : ∀ i, i ∉ rows → Y i = X i
  boundarySubset : ∀ i,
    (boundaryComplex 2 (Y i)).space ⊆ (boundaryComplex 2 (X i)).space
  traceSubset : ∀ k, traceCircles ((Y (k - 1)).space ∪ (Y k).space) (T (2 * k)) ⊆
    traceCircles ((X (k - 1)).space ∪ (X k).space) (T (2 * k))
  nullRankLE : ∀ window, windowNullRank Y T window ≤ windowNullRank X T window
  componentEmbedding : ∀ i,
    ∃ e : ConnectedComponents (Y i).space ↪ ConnectedComponents (X i).space,
      ∀ c, (connectedComponentComplex (Y i) c).space =
        (connectedComponentComplex (X i) (e c)).space
  fixedSet : towerSurface T (fun i => (Y i).space) P' ∩ F =
    towerSurface T (fun i => (X i).space) P' ∩ F
  rankLE : windowComponentRank Y rows ≤ windowComponentRank X rows

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

open Classical in
theorem IsCanonicalAnnularWindow.exists_window_returning_reduction [d : DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {rows : Finset ℤ}
    (hX : IsCanonicalAnnularWindow X (fun j => φ '' S j) S'' T'' I P' a b rows)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    {F : Set E3}
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalReturningWindowReduction X Y (fun j => φ '' S j) S'' T'' I P' a b rows F := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  induction hn : windowComponentRank X rows using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hdone : ∀ i ∈ rows, ∀ c : ConnectedComponents (X i).space,
        ¬ IsCanonicalReturningComponent X T'' i c
    · exact ⟨X,
        { source := hX
          target := hX
          returningFree := hdone
          steps := Relation.ReflTransGen.refl
          pieceSubset := fun _ => Subset.rfl
          unchanged := fun _ _ => rfl
          boundarySubset := fun _ => Subset.rfl
          traceSubset := fun _ => Subset.rfl
          nullRankLE := fun _ => le_rfl
          componentEmbedding := fun _ => ⟨Function.Embedding.refl _, fun _ => rfl⟩
          fixedSet := rfl
          rankLE := le_rfl }⟩
    · push Not at hdone
      obtain ⟨i, hi, c, hreturn⟩ := hdone
      obtain ⟨k, J₀, J₁, hk, hC, hdis, h₀, h₁, hess₀, hess₁⟩ := hreturn
      let _ : Finite (X i).faces := (hX.surface.finiteFaces i).to_subtype
      let _ : Finite (connectedComponentComplex (X i) c).faces :=
        (connectedComponentComplex_faces_finite (X i) c).to_subtype
      have hCb := hC.boundaryComplex_space (connectedComponentComplex (X i) c)
      have hsub : (connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁) ⊆
          (X i).space \ (boundaryComplex 2 (X i)).space := by
        rintro x ⟨hxC, hxJ⟩
        refine ⟨(iUnion_connectedComponentComplex_space (X i)).subset
          (mem_iUnion.mpr ⟨c, hxC⟩), ?_⟩
        intro hxB
        exact hxJ (hCb.subset ((boundaryComplex_space_connectedComponentComplex
          2 (X i) c).symm.subset ⟨hxB, hxC⟩))
      obtain ⟨X₁, B₀, B₁, hX₁, hstep, hdel⟩ :=
        hX.exists_returning_component_deletion htw h314 hI havoid i c hC hdis k hk
          h₀ h₁ hess₀ hess₁ ((hF i hi).mono_right hsub)
      have hboundary (j : ℤ) : (boundaryComplex 2 (X₁ j)).space ⊆
          (boundaryComplex 2 (X j)).space := by
        rw [hX₁.surface.boundary j, hX.surface.boundary j]
        exact inter_subset_inter_left _ (hstep.space_subset j)
      have hF₁ : ∀ j ∈ rows, Disjoint F ((X₁ j).space \ (boundaryComplex 2 (X₁ j)).space) := by
        intro j hj
        apply (hF j hj).mono_right
        rintro x ⟨hx, hxB⟩
        refine ⟨hstep.space_subset j hx, ?_⟩
        intro hxB'
        exact hxB ((hX₁.surface.boundary j).symm.subset
          ⟨hx, ((hX.surface.boundary j).subset hxB').2⟩)
      have hlt : windowComponentRank X₁ rows < n := hn ▸ hstep.windowComponentRank_lt hi
      obtain ⟨Y, hred⟩ := ih (windowComponentRank X₁ rows) hlt hX₁ hF₁ rfl
      have hfixed : towerSurface T'' (fun j => (X₁ j).space) P' ∩ F =
          towerSurface T'' (fun j => (X j).space) P' ∩ F := hdel.2.2.2.2.2.2.2.2.2.2
      refine ⟨Y,
        { source := hX
          target := hred.target
          returningFree := hred.returningFree
          steps := ?_
          pieceSubset := fun j => (hred.pieceSubset j).trans (hstep.space_subset j)
          unchanged := ?_
          boundarySubset := fun j => (hred.boundarySubset j).trans (hboundary j)
          traceSubset := fun j => (hred.traceSubset j).trans
            (hstep.adjacent_trace_subset hX.surface j)
          nullRankLE := fun window => (hred.nullRankLE window).trans
            (hstep.windowNullRank_le hX.surface window)
          componentEmbedding := ?_
          fixedSet := hred.fixedSet.trans hfixed
          rankLE := hred.rankLE.trans (hstep.windowComponentRank_lt hi).le }⟩
      · apply Relation.ReflTransGen.trans ?_ hred.steps
        exact Relation.ReflTransGen.single ⟨hX, hX₁, i, hi, c,
          ⟨k, J₀, J₁, hk, hC, hdis, h₀, h₁, hess₀, hess₁⟩,
          hstep, k, J₀, J₁, B₀, B₁, hk, hdel⟩
      · intro j hj
        exact (hred.unchanged j hj).trans (hstep.unchanged j (fun hji => hj (hji.symm ▸ hi)))
      · intro j
        obtain ⟨e₁, he₁⟩ := hstep.exists_component_embedding j
        obtain ⟨e₂, he₂⟩ := hred.componentEmbedding j
        exact ⟨e₂.trans e₁, fun c => (he₂ c).trans (he₁ (e₂ c))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
