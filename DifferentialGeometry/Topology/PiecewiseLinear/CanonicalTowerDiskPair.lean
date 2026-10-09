/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerInnermostSeam
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSeamDiskPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.exists_innermost_disk_pair_with_trace
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) {a b : E3} (havoid : Disjoint (φ '' S (2 * i)) ({a, b} : Set E3))
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (j : ℤ) (Δ U D₁ D₂ : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3),
      (j = i - 1 ∨ j = i) ∧
      r '' stdSimplexBoundary 2 ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) ∧
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' (2 * i) ∧
      IsOpen U ∧ Δ ⊆ U ∧ U ⊆ I ∧ U ⊆ φ '' S (2 * i) ∧
      Disjoint U ({P', a, b} : Set E3) ∧
      Disjoint (initialSurface S'' T'' P' \ (T'' (2 * i) ∪ canonicalOddPiece S'' T'' j)) U ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2 ∧ Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = Δ ∧ D₁ ∩ T'' (2 * i) = Δ ∧ D₂ ⊆ T'' (2 * i) ∧
      D₁ ∪ D₂ ⊆ initialSurface S'' T'' P' ∩ U ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[initialSurface S'' T'' P'] Δ ∧
      U ∩ canonicalOddPiece S'' T'' j ∩ T'' (2 * i) ⊆ r '' stdSimplexBoundary 2 := by
  classical
  obtain ⟨G, Δ, Ω, r, hG, hr, hΔT, hrG, hΩ, hΔΩ, hΩI, hΩouter, hΩavoid, hΩseam⟩ :=
    htw.exists_innermost_seam_neighborhood i havoid hnull
  obtain ⟨j, hj, hGtrace⟩ : ∃ j : ℤ, (j = i - 1 ∨ j = i) ∧
      G ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) := by
    rcases hG with hG | hG
    · refine ⟨i - 1, Or.inl rfl, ?_⟩
      have heq : traceCircles (canonicalOddPiece S'' T'' (i - 1)) (T'' (2 * i)) =
          traceCircles (T'' (2 * i - 1)) (T'' (2 * i)) := by
        unfold traceCircles
        rw [htw.oddPiece_inter_even, show 2 * (i - 1) + 1 = 2 * i - 1 by omega]
      rwa [heq]
    · refine ⟨i, Or.inr rfl, ?_⟩
      simpa only [traceCircles, htw.oddPiece_inter_even, inter_comm] using hG
  have hGodd : G ⊆ T'' (2 * j + 1) := fun x hx => (traceCircles_subset hGtrace hx).1.1
  have hGΔ : G ⊆ Δ := by
    rw [← hrG]
    exact (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hseam : ∀ k : ℤ, (k = i - 1 ∨ k = i) → ∀ x ∈ T'' (2 * i),
      x ∈ T'' (2 * k + 1) → ∃ H ∈ evenTorusSeams T'' i, x ∈ H := by
    intro k hk x hxE hxO
    rcases hk with hk | hk
    · subst k
      have hxO' : x ∈ T'' (2 * i - 1) := by
        rwa [show 2 * (i - 1) + 1 = 2 * i - 1 by omega] at hxO
      have hcover := htw.traceCircles_cover (2 * i - 1)
      simp only [sub_add_cancel] at hcover
      obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp (hcover.subset ⟨hxO', hxE⟩)
      exact ⟨H, Or.inl hH, hxH⟩
    · subst k
      obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp ((htw.traceCircles_cover (2 * i)).subset ⟨hxE, hxO⟩)
      exact ⟨H, Or.inr hH, hxH⟩
  let k := 2 * i - 1 - j
  have hk : k = i - 1 ∨ k = i := by
    dsimp [k]
    rcases hj with hj | hj <;> omega
  have hsep : 2 ≤ |(2 * j + 1) - (2 * k + 1)| := by
    dsimp [k]
    rw [le_abs]
    rcases hj with hj | hj <;> omega
  have hΔother : Disjoint Δ (T'' (2 * k + 1)) := by
    apply disjoint_left.mpr
    intro x hxΔ hxOther
    obtain ⟨H, hH, hxH⟩ := hseam k hk x (hΔT hxΔ) hxOther
    by_cases hHG : H = G
    · exact disjoint_left.mp (htw.apart _ _ hsep)
        (htw.boundary_subset_outer _ (hGodd (hHG ▸ hxH)))
        (htw.boundary_subset_outer _ hxOther)
    · exact disjoint_left.mp (hΩseam H hH hHG) (hΔΩ hxΔ) hxH
  let U := Ω \ T'' (2 * k + 1)
  have hU : IsOpen U := hΩ.sdiff (htw.boundary_isPolyhedron _).isClosed
  have hΔU : Δ ⊆ U := fun x hx => ⟨hΔΩ hx, fun hxO => disjoint_left.mp hΔother hx hxO⟩
  have hUouter : U ⊆ φ '' S (2 * i) := sdiff_subset.trans hΩouter
  have heven : ∀ x ∈ U, ∀ l : ℤ, x ∈ S'' (2 * l) → l = i := by
    intro x hxU l hxl
    by_contra hli
    exact disjoint_left.mp (htw.apart (2 * i) (2 * l) (by rw [le_abs]; omega))
      (hUouter hxU) (htw.solid_subset_outer _ hxl)
  have hodd : ∀ x ∈ U, ∀ l : ℤ, x ∈ T'' (2 * l + 1) → l = j := by
    intro x hxU l hxl
    have hadj : l = i - 1 ∨ l = i := by
      by_contra hne
      push Not at hne
      exact disjoint_left.mp (htw.apart (2 * i) (2 * l + 1) (by rw [le_abs]; omega))
        (hUouter hxU) (htw.boundary_subset_outer _ hxl)
    by_contra hlj
    have hlk : l = k := by
      dsimp [k]
      rcases hadj with h | h <;> rcases hj with h' | h' <;> omega
    exact hxU.2 (hlk ▸ hxl)
  have hlocal : initialSurface S'' T'' P' ∩ U =
      (T'' (2 * i) ∪ canonicalOddPiece S'' T'' j) ∩ U := by
    rw [htw.initialSurface_eq_iUnion]
    ext x
    constructor
    · rintro ⟨hx | hxP, hxU⟩
      · obtain ⟨l, hxl | hxl⟩ := mem_iUnion.mp hx
        · exact ⟨Or.inl (heven x hxU l (htw.boundary_subset_solid _ hxl) ▸ hxl), hxU⟩
        · exact ⟨Or.inr (hodd x hxU l hxl.1 ▸ hxl), hxU⟩
      · have hxP' : x = P' := hxP
        exact (disjoint_left.mp hΩavoid hxU.1 (Or.inl hxP')).elim
    · rintro ⟨hx | hx, hxU⟩
      · exact ⟨Or.inl (mem_iUnion.mpr ⟨i, Or.inl hx⟩), hxU⟩
      · exact ⟨Or.inl (mem_iUnion.mpr ⟨j, Or.inr hx⟩), hxU⟩
  have hclip : ∀ x ∈ U, x ∈ canonicalOddPiece S'' T'' j ↔
      x ∈ T'' (2 * j + 1) \ interior (S'' (2 * i)) := by
    intro x hxU
    rw [htw.oddPiece_eq_sdiff_iUnion]
    constructor
    · intro hx
      exact ⟨hx.1, fun hxi => hx.2 (mem_iUnion.mpr ⟨i, hxi⟩)⟩
    · rintro ⟨hxT, hxI⟩
      refine ⟨hxT, ?_⟩
      intro hxAll
      obtain ⟨l, hxl⟩ := mem_iUnion.mp hxAll
      exact hxI (heven x hxU l (interior_subset hxl) ▸ hxl)
  have htrace : U ∩ T'' (2 * j + 1) ∩ T'' (2 * i) ⊆ G := by
    rintro x ⟨⟨hxU, hxO⟩, hxE⟩
    obtain ⟨H, hH, hxH⟩ := hseam j hj x hxE hxO
    by_cases hHG : H = G
    · exact hHG ▸ hxH
    · exact (disjoint_left.mp (hΩseam H hH hHG) hxU.1 hxH).elim
  have hΔodd : Δ ∩ T'' (2 * j + 1) = r '' stdSimplexBoundary 2 := by
    rw [hrG]
    exact Subset.antisymm (fun x hx => htrace ⟨⟨hΔU hx.1, hx.2⟩, hΔT hx.1⟩)
      (fun x hx => ⟨hGΔ hx, hGodd hx⟩)
  have hX : IsCombinatorialSolidTorus (S'' (2 * i)) := by
    simpa using (htw.config (2 * i)).isPolyhedralSolidTorus 0
  have hTodd : IsPLTorus (T'' (2 * j + 1)) := by
    have hS : IsCombinatorialSolidTorus (S'' (2 * j + 1)) := by
      simpa using (htw.config (2 * j + 1)).isPolyhedralSolidTorus 0
    rw [htw.boundary_eq]
    exact hS.isPLTorus_frontier
  have hcross : ∀ x ∈ r '' stdSimplexBoundary 2,
      HasPLCrossingAt (T'' (2 * j + 1)) (frontier (S'' (2 * i))) x := by
    intro x hx
    have hxG : x ∈ G := hrG ▸ hx
    have hxE : x ∈ T'' (2 * i) := hΔT (hGΔ hxG)
    have hxO := hGodd hxG
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
  obtain ⟨D₁, D₂, r₁, r₂, hr₁, hr₂, hΔ₁, hΔ₂, hpair, hD₁T, hD₂T, -, hsub, hnear⟩ :=
    exists_disk_pair_of_crossing_torus_seam hX hTodd hr
      (by rwa [← htw.boundary_eq]) hΔodd hU hΔU
      (by simpa only [← htw.boundary_eq, hrG] using htrace) hcross
  have hlocal' : (frontier (S'' (2 * i)) ∪
      (T'' (2 * j + 1) \ interior (S'' (2 * i)))) ∩ U = initialSurface S'' T'' P' ∩ U := by
    rw [← htw.boundary_eq, hlocal]
    ext x
    constructor
    · rintro ⟨hx | hx, hxU⟩
      · exact ⟨Or.inl hx, hxU⟩
      · exact ⟨Or.inr ((hclip x hxU).mpr hx), hxU⟩
    · rintro ⟨hx | hx, hxU⟩
      · exact ⟨Or.inl hx, hxU⟩
      · exact ⟨Or.inr ((hclip x hxU).mp hx), hxU⟩
  refine ⟨j, Δ, U, D₁, D₂, r, r₁, r₂, hj, hrG.symm ▸ hGtrace, hr, hΔT,
    hU, hΔU, sdiff_subset.trans hΩI, hUouter,
    hΩavoid.mono_left sdiff_subset, ?_, hr₁, hr₂,
    hΔ₁, hΔ₂, hpair, ?_, ?_, hsub.trans hlocal'.subset, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨hxC, hxnot⟩ hxU
    exact hxnot (hlocal.subset ⟨hxC, hxU⟩).1
  · rwa [← htw.boundary_eq] at hD₁T
  · rwa [← htw.boundary_eq] at hD₂T
  · obtain ⟨O, hO, hΔO, hOD⟩ := mem_nhdsSetWithin.mp hnear
    refine mem_nhdsSetWithin.mpr ⟨O ∩ U, hO.inter hU, fun x hx => ⟨hΔO hx, hΔU hx⟩, ?_⟩
    rintro x ⟨hxOU, hxC⟩
    exact hOD ⟨hxOU.1, (hlocal'.symm.subset ⟨hxC, hxOU.2⟩).1⟩
  · rintro x ⟨⟨hxU, hxL⟩, hxT⟩
    rw [hrG]
    exact htrace ⟨⟨hxU, hxL.1⟩, hxT⟩

theorem IsCanonicalTower.exists_innermost_disk_pair
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) {a b : E3} (havoid : Disjoint (φ '' S (2 * i)) ({a, b} : Set E3))
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (j : ℤ) (Δ U D₁ D₂ : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3),
      (j = i - 1 ∨ j = i) ∧
      r '' stdSimplexBoundary 2 ∈ traceCircles (canonicalOddPiece S'' T'' j) (T'' (2 * i)) ∧
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' (2 * i) ∧
      IsOpen U ∧ Δ ⊆ U ∧ U ⊆ I ∧ U ⊆ φ '' S (2 * i) ∧
      Disjoint U ({P', a, b} : Set E3) ∧
      Disjoint (initialSurface S'' T'' P' \ (T'' (2 * i) ∪ canonicalOddPiece S'' T'' j)) U ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
      IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂ ∧
      Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2 ∧ Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2 ∧
      D₁ ∩ D₂ = Δ ∧ D₁ ∩ T'' (2 * i) = Δ ∧ D₂ ⊆ T'' (2 * i) ∧
      D₁ ∪ D₂ ⊆ initialSurface S'' T'' P' ∩ U ∧
      D₁ ∪ D₂ ∈ 𝓝ˢ[initialSurface S'' T'' P'] Δ := by
  obtain ⟨j, Δ, U, D₁, D₂, r, r₁, r₂, hj, hG, hr, hΔT, hU, hΔU, hUI, hUout,
      hUavoid, hR, hr₁, hr₂, hΔ₁, hΔ₂, hpair, hD₁T, hD₂T, hsub, hnear, -⟩ :=
    htw.exists_innermost_disk_pair_with_trace i havoid hnull
  exact ⟨j, Δ, U, D₁, D₂, r, r₁, r₂, hj, hG, hr, hΔT, hU, hΔU, hUI, hUout,
    hUavoid, hR, hr₁, hr₂, hΔ₁, hΔ₂, hpair, hD₁T, hD₂T, hsub, hnear⟩
end DifferentialGeometry.Topology.PiecewiseLinear
