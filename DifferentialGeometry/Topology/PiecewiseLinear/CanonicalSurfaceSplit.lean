/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceNullRank
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurfacePairSplit
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsCircleCapping (L L' T B : Set E3) : Prop :=
  ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3) (f : E3 → E3),
    IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
    L ∩ Δ = r '' stdSimplexBoundary 2 ∧ r '' stdSimplexBoundary 2 ∈ traceCircles L T ∧
    HasPLCircleCollar L (r '' stdSimplexBoundary 2) ∧ IsPLHomeomorphOn f (L ∪ Δ) L' ∧
    EqOn f id (B \ r '' stdSimplexBoundary 2)

structure IsCanonicalNullSplit (S' T : ℤ → Set E3) (i : ℤ)
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) : Prop where
  unchanged : ∀ j, j ≠ i - 1 → j ≠ i → Y j = X j
  outside : ∀ j, (Y j).space \ interior (S' (2 * i)) =
    (X j).space \ interior (S' (2 * i))
  countLt : nullTraceCount ((Y (i - 1)).space ∪ (Y i).space) (T (2 * i)) <
    nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T (2 * i))
  capping :
    (IsCircleCapping (X (i - 1)).space (Y (i - 1)).space (T (2 * i))
        ((X (i - 1)).space ∩ (T (2 * (i - 1)) ∪ T (2 * i))) ∧
      ∃ f : E3 → E3, IsPLHomeomorphOn f (X i).space (Y i).space ∧
        EqOn f id ((X i).space ∩ (T (2 * i) ∪ T (2 * (i + 1))))) ∨
    ((∃ f : E3 → E3, IsPLHomeomorphOn f (X (i - 1)).space (Y (i - 1)).space ∧
        EqOn f id ((X (i - 1)).space ∩ (T (2 * (i - 1)) ∪ T (2 * i)))) ∧
      IsCircleCapping (X i).space (Y i).space (T (2 * i))
        ((X i).space ∩ (T (2 * i) ∪ T (2 * (i + 1)))))

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

theorem IsCanonicalNullSplit.windowNullRank_lt
    {Dimg Dbdimg W I : Set E3} {P' : E3}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {i : ℤ}
    (hstep : IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y)
    {window : Finset ℤ} (hi : i ∈ window) :
    windowNullRank Y T'' window < windowNullRank X T'' window :=
  htw.windowNullRank_lt_of_local_replacement hi hstep.outside hstep.countLt

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}

open Classical in
theorem IsCanonicalSurface.exists_null_seam_split [d : DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3)) (h303 : Moise303)
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (i : ℤ) {F : Set E3} (hFO : Disjoint F (interior (φ '' S (2 * i))))
    (hnull : ∃ G ∈ traceCircles ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)),
      boundsDiskIn G (T'' (2 * i))) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalSurface Y (fun j => φ '' S j) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
      IsCanonicalNullSplit (fun j => φ '' S j) T'' i X Y ∧
      IsProtectedReplacement (towerSurface T'' (fun j => (X j).space) P')
        (towerSurface T'' (fun j => (Y j).space) P') F (interior (φ '' S (2 * i))) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ : Finite (X (i - 1)).faces := (hX.finiteFaces (i - 1)).to_subtype
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  have hleft : HasFiniteCollaredTrace (X (i - 1)).space (T'' (2 * i)) := by
    simpa only [sub_add_cancel] using hX.upperTrace (i - 1)
  have hOHK : Disjoint (interior (φ '' S (2 * i))) (({h u} : Set E3) ∪ {h v}) := by
    apply disjoint_left.mpr
    intro x hxO hxV
    exact disjoint_left.mp (havoid (2 * i)) (interior_subset hxO)
      (by simpa only [mem_union, mem_insert_iff, mem_singleton_iff] using hxV)
  have huI : h u ∈ interior (h '' C u ∪ h '' C v) :=
    interior_mono subset_union_left (ht.mem_interior_image_dualCell hu)
  have hvI : h v ∈ interior (h '' C u ∪ h '' C v) :=
    interior_mono subset_union_right (ht.mem_interior_image_dualCell hv)
  have huv' : h u ≠ h v := fun heq => huv (ht.injOn
    (ht.dualCell_subset hu (interior_subset (ht.mem_interior_dualCell hu)))
    (ht.dualCell_subset hv (interior_subset (ht.mem_interior_dualCell hv))) heq)
  obtain ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, G, hG, hQ₀, hQ₀o, hQ₁, hQ₁o,
      htrace₀, htrace₁, hdis, hsep, hCI, hprot, hout₀, hout₁, -, -, hmeet₀, hmeet₁,
      hb₀, hb₁, hcount, -, Δ, r, f, hr, hrG, hΔT, hmeet, hfix₀, hfix₁, hcaps⟩ :=
    exists_separating_surface_pair_split (X (i - 1)) (X i)
      (hX.manifold _) (hX.orientable _) (hX.manifold _) (hX.orientable _)
      hleft (hX.lowerTrace i) (hX.piecesDisjoint (by omega))
      (htw.boundary_isPLTorus (2 * i)) h303 isOpen_interior
      (ht.isConnected_interior_image_pair hu hv huv (by
        exact (congrArg (fun d : DecidableEq E3 =>
          @insert E3 (Finset E3) (@Finset.instInsert E3 d) u {v} ∈ K.faces)
            (Subsingleton.elim _ _)).mp he))
      (singleton_subset_iff.mpr huI) (singleton_subset_iff.mpr hvI)
      (by simpa only [disjoint_singleton_left, mem_singleton_iff] using huv')
      (isClosed_singleton.preimage continuous_subtype_val)
      (isClosed_singleton.preimage continuous_subtype_val)
      (by rw [← towerSurface_eq_remainder]; exact hX.subsetInterior)
      (by rw [← towerSurface_eq_remainder]; exact hX.separator)
      isOpen_interior (htw.boundary_subset_interior_outer _)
      (interior_subset.trans (htw.subsetInterior _)) hOHK
      (hX.remainder_disjoint_interior_outer htw i) hFO
      (hX.boundary_inter_interior_outer_subset htw (i - 1) i)
      (hX.boundary_inter_interior_outer_subset htw i i) hnull
  let _ : Finite Q₀.faces := hQ₀fin.to_subtype
  let _ : Finite Q₁.faces := hQ₁fin.to_subtype
  have hboundary₀ : (boundaryComplex 2 (X (i - 1))).space =
      (X (i - 1)).space ∩ (T'' (2 * (i - 1)) ∪ T'' (2 * i)) := by
    simpa only [sub_add_cancel] using hX.boundary (i - 1)
  rw [hboundary₀] at hfix₀
  rw [hX.boundary i] at hfix₁
  let Y := replaceAdjacentSurfaces X i Q₀ Q₁
  refine ⟨Y, hX.of_adjacent_replacement htw i Q₀ Q₁ hQ₀ hQ₀o hQ₁ hQ₁o htrace₀ htrace₁
    hdis ((traceCircles_subset hG).trans inter_subset_right) hout₀ hout₁
    hmeet₀ hmeet₁ hb₀ hb₁ hCI hsep, ?_, ?_⟩
  · refine
      { unchanged := fun j hj₀ hj₁ => replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj₀ hj₁
        outside := ?_
        countLt := by simpa only [Y, replaceAdjacentSurfaces_left,
          replaceAdjacentSurfaces_right] using hcount
        capping := ?_ }
    · intro j
      by_cases hj₀ : j = i - 1
      · subst j
        simpa only [Y, replaceAdjacentSurfaces_left] using hout₀
      · by_cases hj₁ : j = i
        · subst j
          simpa only [Y, replaceAdjacentSurfaces_right] using hout₁
        · simp only [Y, replaceAdjacentSurfaces_of_ne X i Q₀ Q₁ hj₀ hj₁]
    · rcases hcaps with ⟨hG₀, hf₀, hf₁, -, -⟩ | ⟨hG₁, hf₀, hf₁, -, -⟩
      · refine Or.inl ⟨?_, ⟨f, ?_, ?_⟩⟩
        · refine ⟨Δ, r, f, hr, hΔT, ?_, hrG.symm ▸ hG₀,
            hrG.symm ▸ hleft.circleCollar G hG₀, ?_, ?_⟩
          · rw [hrG]
            exact Subset.antisymm (fun x hx => hmeet.subset ⟨Or.inl hx.1, hx.2⟩)
              (fun x hx => ⟨(traceCircles_subset hG₀ hx).1, (hmeet.symm.subset hx).2⟩)
          · simpa only [Y, replaceAdjacentSurfaces_left] using hf₀
          · simpa only [hrG] using hfix₀
        · simpa only [Y, replaceAdjacentSurfaces_right] using hf₁
        · apply hfix₁.mono
          intro x hx
          exact ⟨hx, fun hxG => disjoint_left.mp (hX.piecesDisjoint (by omega))
            (traceCircles_subset hG₀ hxG).1 hx.1⟩
      · refine Or.inr ⟨⟨f, ?_, ?_⟩, ?_⟩
        · simpa only [Y, replaceAdjacentSurfaces_left] using hf₀
        · apply hfix₀.mono
          intro x hx
          exact ⟨hx, fun hxG => disjoint_left.mp (hX.piecesDisjoint (by omega))
            hx.1 (traceCircles_subset hG₁ hxG).1⟩
        · refine ⟨Δ, r, f, hr, hΔT, ?_, hrG.symm ▸ hG₁,
            hrG.symm ▸ (hX.lowerTrace i).circleCollar G hG₁, ?_, ?_⟩
          · rw [hrG]
            exact Subset.antisymm (fun x hx => hmeet.subset ⟨Or.inr hx.1, hx.2⟩)
              (fun x hx => ⟨(traceCircles_subset hG₁ hx).1, (hmeet.symm.subset hx).2⟩)
          · simpa only [Y, replaceAdjacentSurfaces_right] using hf₁
          · simpa only [hrG] using hfix₁
  · dsimp only [Y]
    rw [towerSurface_replaceAdjacentSurfaces,
      towerSurface_eq_remainder T'' (fun j => (X j).space) P' i]
    exact hprot

end DifferentialGeometry.Topology.PiecewiseLinear
