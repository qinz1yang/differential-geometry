/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeWindow

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalBridgeWindowReduction [DecidableEq E3]
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' S'' T : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) (F : Set E3) : Prop where
  source : IsCanonicalAnnularWindow X S' S'' T I P' a b rows
  target : IsCanonicalAnnularWindow Y S' S'' T I P' a b rows
  bridgeComponents : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    IsCanonicalBridgeComponent Y T i c
  singleComponent : ∀ i ∈ rows, Nat.card (ConnectedComponents (Y i).space) = 1
  steps : Relation.ReflTransGen (fun U V =>
    IsCanonicalAnnularWindow U S' S'' T I P' a b rows ∧
    IsCanonicalAnnularWindow V S' S'' T I P' a b rows ∧
      ∃ i ∈ rows, ∃ c d : ConnectedComponents (U i).space,
        c ≠ d ∧ IsCanonicalBridgeComponent U T i c ∧ IsCanonicalBridgeComponent U T i d ∧
        IsCanonicalComponentDeletion i U V c ∧
        (connectedComponentComplex (U i) d).space ⊆ (V i).space ∧
        towerSurface T (fun j => (V j).space) P' ∩ F =
          towerSurface T (fun j => (U j).space) P' ∩ F) X Y
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
theorem IsCanonicalAnnularWindow.exists_window_bridge_reduction [d : DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {rows : Finset ℤ}
    (hX : IsCanonicalAnnularWindow X (fun j => φ '' S j) S'' T'' I P' a b rows)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (hbridge : ∀ i ∈ rows, ∀ c : ConnectedComponents (X i).space,
      IsCanonicalBridgeComponent X T'' i c)
    (hne : ∀ i ∈ rows, Nonempty (ConnectedComponents (X i).space))
    {F : Set E3}
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalBridgeWindowReduction X Y (fun j => φ '' S j) S'' T'' I P' a b rows F := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  induction hn : windowComponentRank X rows using Nat.strong_induction_on generalizing X with
  | h n ih =>
    by_cases hdone : ∀ i ∈ rows, Nat.card (ConnectedComponents (X i).space) = 1
    · exact ⟨X,
        { source := hX
          target := hX
          bridgeComponents := hbridge
          singleComponent := hdone
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
      obtain ⟨i, hi, hnot⟩ := hdone
      obtain ⟨keep⟩ := hne i hi
      have hnotall : ¬ ∀ c : ConnectedComponents (X i).space, c = keep :=
        fun hc => hnot (Nat.card_eq_one_iff_exists.mpr ⟨keep, hc⟩)
      push Not at hnotall
      obtain ⟨c, hck⟩ := hnotall
      obtain ⟨J₀, J₁, hC, hJ₀, hJ₁, hJess₀, hJess₁⟩ := hbridge i hi c
      obtain ⟨K₀, K₁, hK, hK₀, hK₁, hKess₀, hKess₁⟩ := hbridge i hi keep
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
      obtain ⟨X₁, hX₁, hstep, -, hkeep, hretained, hfixed⟩ :=
        hX.exists_bridge_component_deletion htw h314 hI havoid i c keep hck hC hK
          hJ₀ hJ₁ hK₀ hK₁ hJess₀ hJess₁ hKess₀ hKess₁ ((hF i hi).mono_right hsub)
      have hbridge₁ : ∀ j ∈ rows, ∀ q : ConnectedComponents (X₁ j).space,
          IsCanonicalBridgeComponent X₁ T'' j q := by
        intro j hj q
        obtain ⟨e, he⟩ := hstep.exists_component_embedding j
        exact (hbridge j hj (e q)).of_component_space_eq (he q)
      have hne₁ : ∀ j ∈ rows, Nonempty (ConnectedComponents (X₁ j).space) := by
        intro j hj
        by_cases hji : j = i
        · subst j
          obtain ⟨q, -⟩ := hretained
          exact ⟨q⟩
        · rw [hstep.unchanged j hji]
          exact hne j hj
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
      obtain ⟨Y, hred⟩ := ih (windowComponentRank X₁ rows) hlt
        (hbridge := hbridge₁) (hne := hne₁) (hX := hX₁) (hF := hF₁) rfl
      refine ⟨Y,
        { source := hX
          target := hred.target
          bridgeComponents := hred.bridgeComponents
          singleComponent := hred.singleComponent
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
        exact Relation.ReflTransGen.single ⟨hX, hX₁, i, hi, c, keep, hck,
          ⟨J₀, J₁, hC, hJ₀, hJ₁, hJess₀, hJess₁⟩,
          ⟨K₀, K₁, hK, hK₀, hK₁, hKess₀, hKess₁⟩, hstep, hkeep, hfixed⟩
      · intro j hj
        exact (hred.unchanged j hj).trans (hstep.unchanged j (fun hji => hj (hji.symm ▸ hi)))
      · intro j
        obtain ⟨e₁, he₁⟩ := hstep.exists_component_embedding j
        obtain ⟨e₂, he₂⟩ := hred.componentEmbedding j
        exact ⟨e₂.trans e₁, fun c => (he₂ c).trans (he₁ (e₂ c))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
