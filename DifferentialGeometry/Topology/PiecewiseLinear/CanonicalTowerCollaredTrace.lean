/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerFiniteWindow
import DifferentialGeometry.Topology.PiecewiseLinear.FiniteCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSeamDiskPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.boundary_isPLTorus
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsPLTorus (T'' i) := by
  have hX : IsCombinatorialSolidTorus (S'' i) := by
    simpa using (htw.config i).isPolyhedralSolidTorus 0
  rw [htw.boundary_eq]
  exact hX.isPLTorus_frontier

theorem IsCanonicalTower.hasFiniteCollaredTrace_oddPiece
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i j : ℤ) (hj : j = i - 1 ∨ j = i) :
    HasFiniteCollaredTrace (canonicalOddPiece S'' T'' j) (T'' (2 * i)) := by
  have hfin : (traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i))).Finite := by
    rcases hj with hj | hj
    · rw [hj]
      simpa only [sub_add_cancel] using htw.finite_oddPiece_traceCircles_upper (i - 1)
    · rw [hj]
      exact htw.finite_oddPiece_traceCircles_lower i
  have hcover : canonicalOddPiece S'' T'' j ∩ T'' (2 * i) =
      ⋃ G ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)), G := by
    simp only [traceCircles, htw.oddPiece_inter_even]
    rcases hj with hj | hj
    · rw [hj, show 2 * (i - 1) + 1 = 2 * i - 1 by omega]
      simpa only [traceCircles, sub_add_cancel] using htw.traceCircles_cover (2 * i - 1)
    · rw [hj]
      simpa only [traceCircles, inter_comm] using htw.traceCircles_cover (2 * i)
  refine ⟨htw.oddPiece_isPolyhedron j, hfin, hcover, ?_⟩
  intro G hG
  have hG' : G ∈ traceCircles (T'' (2 * j + 1)) (T'' (2 * i)) := by
    simpa only [traceCircles, htw.oddPiece_inter_even] using hG
  have hX : IsCombinatorialSolidTorus (S'' (2 * i)) := by
    simpa using (htw.config (2 * i)).isPolyhedralSolidTorus 0
  have hcross : ∀ x ∈ G,
      HasPLCrossingAt (T'' (2 * j + 1)) (frontier (S'' (2 * i))) x := by
    intro x hx
    obtain ⟨hxO, hxE⟩ := traceCircles_subset hG' hx
    rw [← htw.boundary_eq]
    rcases hj with hj | hj
    · have hi : 2 * j + 1 = 2 * i - 1 := by omega
      rw [hi] at hxO ⊢
      simpa using (htw.config (2 * i - 1)).crossing 0 x
        (by simpa using (show x ∈ T'' (2 * i - 1) ∩ T'' (2 * i) from ⟨hxO, hxE⟩))
    · subst j
      have h : HasPLCrossingAt (T'' (2 * i)) (T'' (2 * i + 1)) x := by
        simpa using (htw.config (2 * i)).crossing 0 x
          (by simpa using (show x ∈ T'' (2 * i) ∩ T'' (2 * i + 1) from ⟨hxE, hxO⟩))
      exact h.symm
  have hcollar := (htw.boundary_isPLTorus (2 * j + 1)).hasPLCircleCollar_sdiff_interior
    hX.isPolyhedron.isClosed hX.subset_closure_interior
    (by simpa only [traceCircles, htw.oddPiece_inter_even, ← htw.boundary_eq] using hfin)
    (by simpa only [traceCircles, htw.oddPiece_inter_even, ← htw.boundary_eq] using hcover)
    (by simpa only [← htw.boundary_eq] using hG') hcross
  let U := interior (φ '' S (2 * i))
  have hTU : T'' (2 * i) ⊆ U := by
    have hXU : S'' (2 * i) ⊆ U := by
      simpa [U] using (htw.config (2 * i)).innerSubset 0
    exact (htw.boundary_subset_solid _).trans hXU
  have heven : ∀ x ∈ U, ∀ k : ℤ, x ∈ S'' (2 * k) → k = i := by
    intro x hxU k hxk
    by_contra hki
    exact disjoint_left.mp (htw.apart (2 * i) (2 * k) (by rw [le_abs]; omega))
      (interior_subset hxU) (htw.solid_subset_outer _ hxk)
  apply hcollar.of_locally_eq isOpen_interior
    (fun x hx => hTU (traceCircles_subset hG' hx).2)
  rw [htw.oddPiece_eq_sdiff_iUnion]
  ext x
  constructor
  · rintro ⟨⟨hxT, hxAll⟩, hxU⟩
    exact ⟨⟨hxT, fun hxi => hxAll (mem_iUnion.mpr ⟨i, hxi⟩)⟩, hxU⟩
  · rintro ⟨⟨hxT, hxi⟩, hxU⟩
    refine ⟨⟨hxT, ?_⟩, hxU⟩
    intro hxAll
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxAll
    exact hxi (heven x hxU k (interior_subset hxk) ▸ hxk)

end DifferentialGeometry.Topology.PiecewiseLinear
