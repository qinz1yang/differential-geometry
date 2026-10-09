/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem polyhedron_sdiff_interior {P Q : Set E3}
    (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) : IsPolyhedron (P \ interior Q) := by
  have heq : P \ interior Q = (P ∩ frontier Q) ∪ closure (P \ Q) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxP, hxI⟩
      by_cases hxQ : x ∈ Q
      · exact Or.inl ⟨hxP, (hQ.isClosed.frontier_eq).symm ▸ ⟨hxQ, hxI⟩⟩
      · exact Or.inr (subset_closure ⟨hxP, hxQ⟩)
    · refine union_subset (fun x hx => ⟨hx.1, hx.2.2⟩) ?_
      exact closure_minimal (fun x hx => ⟨hx.1, fun hxI => hx.2 (interior_subset hxI)⟩)
        (hP.isClosed.sdiff isOpen_interior)
  rw [heq]
  exact (hP.inter hQ.frontier).union (hP.closure_sdiff hQ)

def canonicalOddPiece (S'' T'' : ℤ → Set E3) (i : ℤ) : Set E3 :=
  T'' (2 * i + 1) \ (interior (S'' (2 * i)) ∪ interior (S'' (2 * i + 2)))

def towerWindowPiece (S'' T'' : ℤ → Set E3) (i : ℤ) (j : Fin 3) : Set E3 :=
  if j = 0 then T'' (2 * i) else if j = 1 then canonicalOddPiece S'' T'' i
    else T'' (2 * i + 2)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.solid_disjoint
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {i k : ℤ} (hik : 2 ≤ |i - k|) : Disjoint (S'' i) (S'' k) :=
  (htw.apart i k hik).mono (htw.solid_subset_outer i) (htw.solid_subset_outer k)

theorem IsCanonicalTower.even_boundary_disjoint_interior
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i k : ℤ) : Disjoint (T'' (2 * i)) (interior (S'' (2 * k))) := by
  by_cases hik : i = k
  · subst k
    rw [htw.boundary_eq]
    exact disjoint_interior_frontier.symm
  · exact (htw.solid_disjoint (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_solid _) interior_subset

theorem IsCanonicalTower.oddPiece_isPolyhedron
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsPolyhedron (canonicalOddPiece S'' T'' i) := by
  rw [canonicalOddPiece, ← sdiff_sdiff]
  exact polyhedron_sdiff_interior
    (polyhedron_sdiff_interior (htw.boundary_isPolyhedron _) (htw.solid_isPolyhedron _))
    (htw.solid_isPolyhedron _)

theorem IsCanonicalTower.oddPiece_eq_sdiff_iUnion
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    canonicalOddPiece S'' T'' i = T'' (2 * i + 1) \ ⋃ k, interior (S'' (2 * k)) := by
  ext x
  constructor
  · rintro ⟨hxT, hxI⟩
    refine ⟨hxT, ?_⟩
    intro hxU
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hxU
    by_cases hki : k = i
    · exact hxI (Or.inl (hki ▸ hxk))
    by_cases hkn : k = i + 1
    · apply hxI
      right
      simpa [hkn, mul_add] using hxk
    · exact disjoint_left.mp (htw.apart (2 * i + 1) (2 * k) (by rw [le_abs]; omega))
        (htw.boundary_subset_outer _ hxT) (htw.solid_subset_outer _ (interior_subset hxk))
  · rintro ⟨hxT, hxU⟩
    refine ⟨hxT, ?_⟩
    rintro (hx | hx)
    · exact hxU (mem_iUnion.mpr ⟨i, hx⟩)
    · apply hxU
      refine mem_iUnion.mpr ⟨i + 1, ?_⟩
      simpa [mul_add] using hx

theorem IsCanonicalTower.initialSurface_eq_iUnion
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') :
    initialSurface S'' T'' P' =
      (⋃ i, T'' (2 * i) ∪ canonicalOddPiece S'' T'' i) ∪ {P'} := by
  simp only [initialSurface, htw.oddPiece_eq_sdiff_iUnion, iUnion_union_distrib,
    iUnion_sdiff]

theorem IsCanonicalTower.oddPiece_inter_even
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i k : ℤ) :
    canonicalOddPiece S'' T'' i ∩ T'' (2 * k) = T'' (2 * i + 1) ∩ T'' (2 * k) := by
  rw [htw.oddPiece_eq_sdiff_iUnion]
  refine Subset.antisymm (fun _ hx => ⟨hx.1.1, hx.2⟩) ?_
  rintro x ⟨hxT, hxE⟩
  refine ⟨⟨hxT, ?_⟩, hxE⟩
  intro hxU
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
  exact disjoint_left.mp (htw.even_boundary_disjoint_interior k j) hxE hxj

theorem IsCanonicalTower.finite_oddPiece_traceCircles_lower
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i))).Finite := by
  have heq : traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * i)) =
      traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) := by
    simp only [traceCircles, htw.oddPiece_inter_even, inter_comm]
  rw [heq]
  exact htw.finite_traceCircles _

theorem IsCanonicalTower.finite_oddPiece_traceCircles_upper
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * (i + 1)))).Finite := by
  have heq : traceCircles (canonicalOddPiece S'' T'' i) (T'' (2 * (i + 1))) =
      traceCircles (T'' (2 * i + 1)) (T'' (2 * i + 1 + 1)) := by
    unfold traceCircles
    rw [htw.oddPiece_inter_even i (i + 1)]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
  rw [heq]
  exact htw.finite_traceCircles _

theorem IsCanonicalTower.windowPiece_isPolyhedron
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) (j : Fin 3) : IsPolyhedron (towerWindowPiece S'' T'' i j) := by
  unfold towerWindowPiece
  split
  · exact htw.boundary_isPolyhedron _
  · split
    · exact htw.oddPiece_isPolyhedron _
    · exact htw.boundary_isPolyhedron _

theorem IsCanonicalTower.exists_surface_window_triangulation
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (window : Finset ℤ) :
    ∃ K : Geometry.SimplicialComplex ℝ E3, K.faces.Finite ∧
      K.space = ⋃ i ∈ window, ⋃ j : Fin 3, towerWindowPiece S'' T'' i j ∧
      ∀ i ∈ window, ∀ j : Fin 3,
        towerWindowPiece S'' T'' i j =
          ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E3) ⊆ towerWindowPiece S'' T'' i j},
            convexHull ℝ (s : Set E3) := by
  classical
  let Q : window × Fin 3 → Set E3 := fun p => towerWindowPiece S'' T'' p.1 p.2
  have hQ : ∀ p, IsPolyhedron (Q p) := fun p => htw.windowPiece_isPolyhedron p.1 p.2
  obtain ⟨K, hKfin, hK⟩ := (IsPolyhedron.iUnion hQ).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  obtain ⟨R, hRK, hRfin, hcover⟩ := exists_isSubdivision_subcomplexes K Q hQ
    (fun p => (subset_iUnion Q p).trans hK.ge)
  refine ⟨R, hRfin, ?_, fun i hi j => hcover (⟨i, hi⟩, j)⟩
  rw [hRK.space_eq, hK]
  ext x
  simp only [Q, mem_iUnion, Prod.exists, Subtype.exists]

theorem IsCanonicalTower.exists_finite_carrier_neighborhood
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {C : Set E3} (hC : IsCompact C) (hCI : C ⊆ I \ {P'}) :
    ∃ (U : Set E3) (window : Finset ℤ), IsOpen U ∧ C ⊆ U ∧
      ∀ i : ℤ, (φ '' S i ∩ U).Nonempty → i ∈ window := by
  classical
  have hlocal : ∀ x : C, ∃ U ∈ 𝓝 (x : E3), {i | (φ '' S i ∩ U).Nonempty}.Finite := by
    intro x
    exact htw.locallyFinite x (hCI x.property).1 (hCI x.property).2
  choose U hU hfin using hlocal
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => interior (U x))
    (fun _ => isOpen_interior) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hU ⟨x, hx⟩)⟩)
  let F : Set ℤ := ⋃ x ∈ t, {i | (φ '' S i ∩ U x).Nonempty}
  have hF : F.Finite := t.finite_toSet.biUnion fun x _ => hfin x
  refine ⟨⋃ x ∈ t, interior (U x), hF.toFinset,
    isOpen_biUnion fun _ _ => isOpen_interior, ht, ?_⟩
  rintro i ⟨y, hyS, hyU⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp hyU
  exact hF.mem_toFinset.mpr (mem_biUnion hxt ⟨y, hyS, interior_subset hyx⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
