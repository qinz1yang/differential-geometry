/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerOddSurface
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerInnermostSeam
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion

open Set Topology
open scoped BigOperators

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def towerSurface (T L : ℤ → Set E3) (P' : E3) : Set E3 :=
  (⋃ i, T (2 * i) ∪ L i) ∪ {P'}

structure IsCanonicalSurface [DecidableEq E3]
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (S' T : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) : Prop where
  finiteFaces : ∀ i, (X i).faces.Finite
  manifold : ∀ i, IsCombinatorialManifoldWithBoundary 2 (X i)
  orientable : ∀ i, letI := (finiteFaces i).to_subtype; IsOrientable 2 (X i)
  interiorCarrier : ∀ i, (X i).space ⊆
    interior ((S' (2 * i) ∪ S' (2 * i + 1)) ∪ S' (2 * (i + 1)))
  piecesDisjoint : Pairwise fun i j => Disjoint (X i).space (X j).space
  boundary : ∀ i, (boundaryComplex 2 (X i)).space =
    (X i).space ∩ (T (2 * i) ∪ T (2 * (i + 1)))
  lowerTrace : ∀ i, HasFiniteCollaredTrace (X i).space (T (2 * i))
  upperTrace : ∀ i, HasFiniteCollaredTrace (X i).space (T (2 * (i + 1)))
  lowerOrigin : ∀ i, traceCircles (X i).space (T (2 * i)) ⊆
    traceCircles (T (2 * i + 1)) (T (2 * i))
  upperOrigin : ∀ i, traceCircles (X i).space (T (2 * (i + 1))) ⊆
    traceCircles (T (2 * i + 1)) (T (2 * (i + 1)))
  centerNotMem : ∀ i, P' ∉ (X i).space
  subsetInterior : towerSurface T (fun i => (X i).space) P' ⊆ I
  separator : IsSeparatorIn I (towerSurface T (fun i => (X i).space) P') {a} {b}

theorem IsCanonicalSurface.carrier [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (h : IsCanonicalSurface X S' T I P' a b) (i : ℤ) :
    (X i).space ⊆ (S' (2 * i) ∪ S' (2 * i + 1)) ∪ S' (2 * (i + 1)) :=
  (h.interiorCarrier i).trans interior_subset

noncomputable def windowNullRank (X : ℤ → Geometry.SimplicialComplex ℝ E3)
    (T : ℤ → Set E3) (window : Finset ℤ) : ℕ :=
  ∑ i ∈ window, nullTraceCount ((X (i - 1)).space ∪ (X i).space) (T (2 * i))

theorem IsCanonicalSurface.adjacentTrace [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (h : IsCanonicalSurface X S' T I P' a b) (i : ℤ) :
    HasFiniteCollaredTrace ((X (i - 1)).space ∪ (X i).space) (T (2 * i)) := by
  have hleft : HasFiniteCollaredTrace (X (i - 1)).space (T (2 * i)) := by
    simpa only [sub_add_cancel] using h.upperTrace (i - 1)
  exact hleft.union_of_disjoint (h.lowerTrace i) (h.piecesDisjoint (by omega))

theorem IsCanonicalSurface.windowNullRank_eq_zero_iff [DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3} (h : IsCanonicalSurface X S' T I P' a b) (window : Finset ℤ) :
    windowNullRank X T window = 0 ↔
      ∀ i ∈ window, ∀ G ∈ traceCircles ((X (i - 1)).space ∪ (X i).space) (T (2 * i)),
        ¬ boundsDiskIn G (T (2 * i)) := by
  rw [windowNullRank, Finset.sum_eq_zero_iff]
  constructor
  · intro hzero i hi
    exact (nullTraceCount_eq_zero_iff (h.adjacentTrace i).finiteTrace).mp (hzero i hi)
  · intro hzero i hi
    exact (nullTraceCount_eq_zero_iff (h.adjacentTrace i).finiteTrace).mpr (hzero i hi)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.exists_initial_surface_state [d : DecidableEq E3]
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (a b : E3)
    (hcl : IsClosed (((↑) : I → E3) ⁻¹' initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : I → E3) ⁻¹' initialSurface S'' T'' P')
      (((↑) : I → E3) ⁻¹' {a}) (((↑) : I → E3) ⁻¹' {b})) :
    ∃ X : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalSurface X (fun i => φ '' S i) T'' I P' a b ∧
      ∀ i, (X i).space = canonicalOddPiece S'' T'' i := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  choose X hXfin hX hXo hXspace hXb using fun i : ℤ => htw.exists_oddPiece_surface i
  have hsurface : towerSurface T'' (fun i => (X i).space) P' = initialSurface S'' T'' P' := by
    rw [htw.initialSurface_eq_iUnion]
    simp only [towerSurface, hXspace]
  refine ⟨X, ?_, hXspace⟩
  refine
    { finiteFaces := hXfin
      manifold := hX
      orientable := hXo
      interiorCarrier := ?_
      piecesDisjoint := ?_
      boundary := ?_
      lowerTrace := ?_
      upperTrace := ?_
      lowerOrigin := ?_
      upperOrigin := ?_
      centerNotMem := ?_
      subsetInterior := ?_
      separator := ?_ }
  · intro i x hx
    rw [hXspace] at hx
    have hinner : S'' (2 * i + 1) ⊆ interior (φ '' S (2 * i + 1)) := by
      simpa using (htw.config (2 * i + 1)).innerSubset 0
    exact interior_mono (fun _ hx => Or.inl (Or.inr hx))
      (hinner (htw.boundary_subset_solid _ hx.1))
  · intro i j hij
    rw [hXspace, hXspace]
    exact (htw.apart (2 * i + 1) (2 * j + 1) (by rw [le_abs]; omega)).mono
      (fun x hx => htw.boundary_subset_outer _ hx.1)
      (fun x hx => htw.boundary_subset_outer _ hx.1)
  · intro i
    rw [hXspace, show 2 * (i + 1) = 2 * i + 2 by omega]
    exact hXb i
  · intro i
    rw [hXspace]
    exact htw.hasFiniteCollaredTrace_oddPiece i i (Or.inr rfl)
  · intro i
    rw [hXspace]
    exact htw.hasFiniteCollaredTrace_oddPiece (i + 1) i (Or.inl (by omega))
  · intro i G hG
    rw [hXspace] at hG
    simpa only [traceCircles, htw.oddPiece_inter_even] using hG
  · intro i G hG
    rw [hXspace] at hG
    simpa only [traceCircles, htw.oddPiece_inter_even] using hG
  · intro i hx
    rw [hXspace] at hx
    have hinner : S'' (2 * i + 1) ⊆ interior (φ '' S (2 * i + 1)) := by
      simpa using (htw.config (2 * i + 1)).innerSubset 0
    exact htw.center_notMem_interior_outer _ (hinner (htw.boundary_subset_solid _ hx.1))
  · rw [hsurface, htw.initialSurface_eq_iUnion]
    refine union_subset (iUnion_subset fun i => union_subset ?_ ?_)
      (singleton_subset_iff.mpr htw.centerMemInterior)
    · exact (htw.boundary_subset_outer _).trans (htw.subsetInterior _)
    · exact fun x hx => htw.subsetInterior _ (htw.boundary_subset_outer _ hx.1)
  · rw [hsurface]
    exact ⟨hcl, hsep⟩

end DifferentialGeometry.Topology.PiecewiseLinear
