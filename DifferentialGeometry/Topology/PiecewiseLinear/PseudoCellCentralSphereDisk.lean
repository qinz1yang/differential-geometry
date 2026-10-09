/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellCentralTrace
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInnermostDisk

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_central_sphere_disk
    {Ec Eint Ebd Bl Dc Dcint : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (hBl : IsPLBall 3 Bl) (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hBE : Bl ∩ Ec ⊆ Dc) {n : ℕ} {G : Fin n → Set E3}
    (hG : ∀ i, IsPLSphere 1 (G i)) (hdisj : Pairwise fun i j => Disjoint (G i) (G j))
    (htrace : frontier Bl ∩ Ec = ⋃ i, G i) :
    ∃ (i₀ : Fin n) (Δ : Set E3) (r : (Fin 3 → ℝ) → E3) (DJ DJint : Set E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ frontier Bl ∧
      r '' stdSimplexBoundary 2 = G i₀ ∧ IsTopologicalCellWithInterior 2 DJ DJint ∧
      DJ ⊆ Dc ∧ DJ \ DJint = G i₀ ∧ P ∈ DJint ∧
      (∀ i, G i ⊆ Δ ∨ Disjoint (G i) Δ) ∧
      (∀ i, i ≠ i₀ → G i ⊆ Δ →
        ¬ ∃ D I : Set E3, IsTopologicalCellWithInterior 2 D I ∧ D ⊆ Dc ∧
          D \ I = G i ∧ P ∈ I) ∧
      Δ ∩ Ec = ⋃ i : {i : Fin n | G i ⊆ Δ}, G i.1 := by
  classical
  let C : Set (Fin n) := {i | ∃ D I : Set E3,
    IsTopologicalCellWithInterior 2 D I ∧ D ⊆ Dc ∧ D \ I = G i ∧ P ∈ I}
  have hGsub : ∀ i, G i ⊆ frontier Bl ∩ Ec := by
    intro i x hx
    rw [htrace]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hGS : ∀ i, G i ⊆ frontier Bl := fun i => (hGsub i).trans inter_subset_left
  have : Nonempty C := by
    obtain ⟨i, D, I, hD, hDDc, hrim, hPI⟩ :=
      hE.exists_central_disk_of_finite_trace hBl hP hDc hDcE hBE hG hdisj htrace
    exact ⟨⟨i, D, I, hD, hDDc, hrim, hPI⟩⟩
  have hS := hBl.isPLSphere_frontier
  obtain ⟨j, Δ, r, hr, hΔ, hrim, hclean⟩ := hS.exists_innermost_disk
    (J := fun i : C => G i.1) (fun i => hG i.1) (fun i => hGS i.1)
    (fun i j hij => hdisj fun heq => hij (Subtype.ext heq))
  obtain ⟨DJ, DJint, hDJ, hDJDc, hDJrim, hPDJ⟩ := j.property
  have hbound : G j.1 ⊆ Δ := by
    rw [← hrim, ← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hside : ∀ i, G i ⊆ Δ ∨ Disjoint (G i) Δ := by
    intro i
    by_cases hij : i = j.1
    · exact Or.inl (hij.symm ▸ hbound)
    have hmeet : Δ ∩ closure (frontier Bl \ Δ) = G j.1 := by
      rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hΔ, hrim]
    have hcover : G i ⊆ Δ ∪ closure (frontier Bl \ Δ) := fun y hy => by
      by_cases hyΔ : y ∈ Δ
      · exact Or.inl hyΔ
      · exact Or.inr (subset_closure ⟨hGS i hy, hyΔ⟩)
    have hd : G i ∩ (Δ ∩ closure (frontier Bl \ Δ)) = ∅ := by
      rw [hmeet]
      exact (hdisj hij).inter_eq
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp (hG i).isConnected.isPreconnected
        Δ (closure (frontier Bl \ Δ)) (show IsPLBall 2 Δ from ⟨r, hr⟩).isPolyhedron.isClosed
        isClosed_closure hcover hd with h | h
    · exact Or.inl h
    · refine Or.inr (Set.disjoint_left.mpr fun y hyG hyΔ => ?_)
      have hy : y ∈ Δ ∩ closure (frontier Bl \ Δ) := ⟨hyΔ, h hyG⟩
      rw [hmeet] at hy
      exact Set.disjoint_left.mp (hdisj hij) hyG hy
  refine ⟨j.1, Δ, r, DJ, DJint, hr, hΔ, hrim, hDJ, hDJDc, hDJrim, hPDJ, hside, ?_, ?_⟩
  · intro i hij hiΔ hiC
    have hne : (⟨i, hiC⟩ : C) ≠ j := fun heq => hij (congrArg Subtype.val heq)
    obtain ⟨x, hx⟩ := (hG i).nonempty
    exact Set.disjoint_left.mp (hclean ⟨i, hiC⟩ hne) (hiΔ hx) hx
  · ext x
    constructor
    · rintro ⟨hxΔ, hxE⟩
      have hxtr : x ∈ ⋃ i, G i := htrace ▸ (show x ∈ frontier Bl ∩ Ec from ⟨hΔ hxΔ, hxE⟩)
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtr
      rcases hside i with hsub | hd
      · exact mem_iUnion.mpr ⟨⟨i, hsub⟩, hxi⟩
      · exact (Set.disjoint_left.mp hd hxi hxΔ).elim
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact ⟨i.property hxi, (hGsub i.1 hxi).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
