/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem annulus_ends_subset {B J₀ J₁ : Set E3}
    (hB : IsPLAnnulusWithEnds B J₀ J₁) : J₀ ∪ J₁ ⊆ B := by
  obtain ⟨Q, ρ, -, hρ, rfl, rfl⟩ := hB
  rw [← image_union, ← hρ.image_eq]
  apply image_mono
  rintro p (hp | hp)
  · refine ⟨hp.1, ?_⟩
    rw [show p.2 = 0 from hp.2]
    exact ⟨le_rfl, zero_le_one⟩
  · refine ⟨hp.1, ?_⟩
    rw [show p.2 = 1 from hp.2]
    exact ⟨zero_le_one, le_rfl⟩

theorem pairwise_disjoint_of_eventually_stable_canonical_rows [DecidableEq E3]
    {X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3} {S' T : ℤ → Set E3}
    {I : Set E3} {P' a b : E3}
    (hX : ∀ n, IsCanonicalSurface (X n) S' T I P' a b) (B : ℤ → Set E3)
    (hstable : ∀ i, ∃ N, ∀ n, N ≤ n → (X n i).space = B i) :
    Pairwise fun i k => Disjoint (B i) (B k) := by
  intro i k hik
  obtain ⟨N, hN⟩ := hstable i
  obtain ⟨M, hM⟩ := hstable k
  simpa only [hN (max N M) (le_max_left _ _), hM (max N M) (le_max_right _ _)] using
    (hX (max N M)).piecesDisjoint hik

theorem IsCanonicalTower.isAnnularChain_of_eventually_stable_rows [DecidableEq E3]
    {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
    {Dimg Dbdimg W I : Set E3} {P' a b : E3}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3)
    (hX : ∀ n, IsCanonicalSurface (X n) (fun j => φ '' S j) T'' I P' a b)
    (H B Jlo Jhi : ℤ → Set E3)
    (hstable : ∀ i, ∃ N, ∀ n, N ≤ n → (X n i).space = B i)
    (hH : ∀ i, IsPLAnnulusWithEnds (H i) (Jhi (i - 1)) (Jlo i))
    (hHT : ∀ i, H i ⊆ T'' (2 * i))
    (hB : ∀ i, IsPLAnnulusWithEnds (B i) (Jlo i) (Jhi i))
    (hlo : ∀ i, B i ∩ T'' (2 * i) = Jlo i)
    (hhi : ∀ i, B i ∩ T'' (2 * (i + 1)) = Jhi i)
    (hloGen : ∀ i, ∀ hsub : Jlo i ⊆ S'' (2 * i), ∀ x : Jlo i,
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(Jlo i, S'' (2 * i))) x))
    (hhiGen : ∀ i, ∀ hsub : Jhi i ⊆ S'' (2 * (i + 1)), ∀ x : Jhi i,
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(Jhi i, S'' (2 * (i + 1)))) x)) :
    IsAnnularChain H B Jlo Jhi (fun j => φ '' S j) S'' T'' P' := by
  have hcarrier (i : ℤ) :
      B i ⊆ φ '' S (2 * i) ∪ φ '' S (2 * i + 1) ∪ φ '' S (2 * i + 2) := by
    obtain ⟨N, hN⟩ := hstable i
    simpa only [hN N le_rfl, show 2 * (i + 1) = 2 * i + 2 by omega] using
      (hX N).carrier i
  have hBP (i : ℤ) : P' ∉ B i := by
    obtain ⟨N, hN⟩ := hstable i
    exact hN N le_rfl ▸ (hX N).centerNotMem i
  have hHP (i : ℤ) : P' ∉ H i := by
    have hinner : S'' (2 * i) ⊆ interior (φ '' S (2 * i)) := by
      simpa using (htw.config (2 * i)).innerSubset 0
    exact fun hx => htw.center_notMem_interior_outer _
      (hinner (htw.boundary_subset_solid _ (hHT i hx)))
  refine
    { half := hH
      halfSubset := hHT
      halfSubsetTorus := fun i => (hHT i).trans (htw.boundary_subset_outer _)
      bridge := hB
      bridgeSubset := hcarrier
      loSubset := fun i => (hlo i).symm.subset.trans inter_subset_right
      hiSubset := ?_
      loGenerator := hloGen
      hiGenerator := ?_
      halfInterBridge := ?_
      bridgeInterHalf := ?_
      halfDisjoint := ?_
      bridgeDisjoint := ?_
      halfBridgeDisjoint := ?_
      centerNotMem := fun i hx => hx.elim (hHP i) (hBP i) }
  · intro i
    simpa only [show 2 * (i + 1) = 2 * i + 2 by omega] using
      (hhi i).symm.subset.trans inter_subset_right
  · intro i
    rw [show 2 * i + 2 = 2 * (i + 1) by omega]
    exact hhiGen i
  · intro i
    apply Subset.antisymm
    · exact fun x hx => (hlo i).subset ⟨hx.2, hHT i hx.1⟩
    · exact fun x hx =>
        ⟨annulus_ends_subset (hH i) (Or.inr hx), ((hlo i).symm.subset hx).1⟩
  · intro i
    apply Subset.antisymm
    · exact fun x hx => (hhi i).subset ⟨hx.1, hHT (i + 1) hx.2⟩
    · intro x hx
      refine ⟨((hhi i).symm.subset hx).1, annulus_ends_subset (hH (i + 1)) ?_⟩
      exact Or.inl (by simpa only [add_sub_cancel_right] using hx)
  · intro i k hik
    exact (htw.apart (2 * i) (2 * k) (by rw [le_abs]; omega)).mono
      ((hHT i).trans (htw.boundary_subset_outer _))
      ((hHT k).trans (htw.boundary_subset_outer _))
  · exact fun i k hik => pairwise_disjoint_of_eventually_stable_canonical_rows hX B hstable hik
  · intro i k hki hprev
    apply disjoint_left.mpr
    intro x hxH hxB
    have hxS := htw.boundary_subset_outer _ (hHT i hxH)
    rcases hcarrier k hxB with (hxLo | hxMid) | hxHi
    · exact disjoint_left.mp (htw.apart (2 * i) (2 * k) (by rw [le_abs]; omega)) hxS hxLo
    · exact disjoint_left.mp (htw.apart (2 * i) (2 * k + 1) (by rw [le_abs]; omega)) hxS hxMid
    · exact disjoint_left.mp (htw.apart (2 * i) (2 * k + 2) (by rw [le_abs]; omega)) hxS hxHi

end DifferentialGeometry.Topology.PiecewiseLinear
