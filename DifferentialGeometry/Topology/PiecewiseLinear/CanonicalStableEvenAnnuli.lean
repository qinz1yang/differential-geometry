/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalAnnularChainAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.TorusCirclePair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem annulus_ends_isPLSphere {B J₀ J₁ : Set E3}
    (hB : IsPLAnnulusWithEnds B J₀ J₁) : IsPLSphere 1 J₀ ∧ IsPLSphere 1 J₁ := by
  obtain ⟨Q, ρ, hQ, hρ, rfl, rfl⟩ := hB
  have hlevel (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      IsPLSphere 1 (ρ '' (Q ×ˢ {t})) :=
    hQ.of_isPLHomeomorphOn ((hQ.isPolyhedron.isPLHomeomorphOn_prod_const t).trans
      (hρ.restrict (isPolyhedron_prod_singleton hQ.isPolyhedron t)
        (prod_mono Subset.rfl (singleton_subset_iff.mpr ht))))
  exact ⟨hlevel 0 ⟨le_rfl, zero_le_one⟩, hlevel 1 ⟨zero_le_one, le_rfl⟩⟩

theorem IsCanonicalTower.exists_complementary_even_annuli_of_eventually_stable_rows
    [DecidableEq E3]
    {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
    {Dimg Dbdimg W I : Set E3} {P' a b : E3}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (X : ℕ → ℤ → Geometry.SimplicialComplex ℝ E3)
    (hX : ∀ n, IsCanonicalSurface (X n) (fun j => φ '' S j) T'' I P' a b)
    (B Jlo Jhi : ℤ → Set E3)
    (hstable : ∀ i, ∃ N, ∀ n, N ≤ n → (X n i).space = B i)
    (hB : ∀ i, IsPLAnnulusWithEnds (B i) (Jlo i) (Jhi i))
    (hlo : ∀ i, B i ∩ T'' (2 * i) = Jlo i)
    (hhi : ∀ i, B i ∩ T'' (2 * (i + 1)) = Jhi i)
    (hloEss : ∀ i, ¬ boundsDiskIn (Jlo i) (T'' (2 * i)))
    (hhiEss : ∀ i, ¬ boundsDiskIn (Jhi i) (T'' (2 * (i + 1)))) :
    ∃ H H' : ℤ → Set E3, ∀ i,
      IsPLAnnulusWithEnds (H i) (Jhi (i - 1)) (Jlo i) ∧
      IsPLAnnulusWithEnds (H' i) (Jhi (i - 1)) (Jlo i) ∧
      H i ∪ H' i = T'' (2 * i) ∧ H i ∩ H' i = Jhi (i - 1) ∪ Jlo i := by
  have hpairs (i : ℤ) : ∃ H H' : Set E3,
      IsPLAnnulusWithEnds H (Jhi (i - 1)) (Jlo i) ∧
      IsPLAnnulusWithEnds H' (Jhi (i - 1)) (Jlo i) ∧
      H ∪ H' = T'' (2 * i) ∧ H ∩ H' = Jhi (i - 1) ∪ Jlo i := by
    have hsolid : IsCombinatorialSolidTorus (S'' (2 * i)) := by
      simpa using (htw.config (2 * i)).isPolyhedralSolidTorus 0
    have h₀T : Jhi (i - 1) ⊆ T'' (2 * i) := by
      simpa only [sub_add_cancel] using (hhi (i - 1)).symm.subset.trans inter_subset_right
    have h₁T : Jlo i ⊆ T'' (2 * i) := (hlo i).symm.subset.trans inter_subset_right
    have hdis : Disjoint (Jhi (i - 1)) (Jlo i) :=
      (pairwise_disjoint_of_eventually_stable_canonical_rows hX B hstable
        (by omega : i - 1 ≠ i)).mono
        ((hhi (i - 1)).symm.subset.trans inter_subset_left)
        ((hlo i).symm.subset.trans inter_subset_left)
    obtain ⟨H, H', hH, hH', hcover, hinter⟩ :=
      hsolid.exists_annulus_pair_of_essential_circles
        (annulus_ends_isPLSphere (hB (i - 1))).2 (annulus_ends_isPLSphere (hB i)).1
        (h₀T.trans (htw.boundary_eq _).subset) (h₁T.trans (htw.boundary_eq _).subset) hdis
        (by simpa only [sub_add_cancel, ← htw.boundary_eq] using hhiEss (i - 1))
        (by simpa only [← htw.boundary_eq] using hloEss i)
    exact ⟨H, H', hH, hH', hcover.trans (htw.boundary_eq _).symm, hinter⟩
  choose H H' h using hpairs
  exact ⟨H, H', h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
