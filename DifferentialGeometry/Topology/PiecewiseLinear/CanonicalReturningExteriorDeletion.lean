/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusTripleExterior
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningAnnulusDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.exists_returning_exterior_annuli_and_separator
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (h267 : Moise267) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (i : ℤ) (c : ConnectedComponents (X i).space) {J₀ J₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (hdis : Disjoint J₀ J₁) (k : ℤ) (hk : k = i ∨ k = i + 1)
    (h₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (h₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (hess₀ : ¬ boundsDiskIn J₀ (T'' (2 * i + 1)))
    (hess₁ : ¬ boundsDiskIn J₁ (T'' (2 * i + 1)))
    (hR : IsClosed (((↑) : I → E3) ⁻¹'
      (towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))))) :
    ∃ B₀ B₁ : Set E3, IsPLAnnulusWithEnds B₀ J₀ J₁ ∧
      IsPLAnnulusWithEnds B₁ J₀ J₁ ∧ T'' (2 * k) = B₀ ∪ B₁ ∧
      B₀ ∩ B₁ = J₀ ∪ J₁ ∧
      (connectedComponentComplex (X i) c).space ∩ T'' (2 * k) = J₀ ∪ J₁ ∧
      IsSeparatorIn I
        (towerSurface T'' (fun j => (X j).space) P' \
          ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))) {a} {b} ∧
      ∃ x, x ∉ (connectedComponentComplex (X i) c).space ∪ T'' (2 * k) ∧
        ¬ Bornology.IsBounded (connectedComponentIn
          ((connectedComponentComplex (X i) c).space ∪ T'' (2 * k))ᶜ x) ∧
        B₀ ⊆ frontier (connectedComponentIn
          ((connectedComponentComplex (X i) c).space ∪ T'' (2 * k))ᶜ x) := by
  let L := connectedComponentComplex (X i) c
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  obtain ⟨B₀, B₁, hB₀, hB₁, hcover, hmeet, hCT⟩ :=
    hX.exists_annulus_pair_of_returning_component htw h314 i c hC hdis k hk h₀ h₁
      hess₀ hess₁
  have h₀T : B₀ ⊆ T'' (2 * k) := subset_union_left.trans hcover.symm.subset
  have h₁T : B₁ ⊆ T'' (2 * k) := subset_union_right.trans hcover.symm.subset
  have hC₀ : L.space ∩ B₀ = J₀ ∪ J₁ := by
    apply Subset.antisymm
    · exact fun _ hx => hCT.subset ⟨hx.1, h₀T hx.2⟩
    · exact fun _ hx => ⟨(hCT.symm.subset hx).1, (hmeet.symm.subset hx).1⟩
  have hC₁ : L.space ∩ B₁ = J₀ ∪ J₁ := by
    apply Subset.antisymm
    · exact fun _ hx => hCT.subset ⟨hx.1, h₁T hx.2⟩
    · exact fun _ hx => ⟨(hCT.symm.subset hx).1, (hmeet.symm.subset hx).2⟩
  obtain ⟨B, x, r, s, t, hchoice, hfrontier, hx, hunbounded, -, -, -, hfront, -⟩ :=
    hC.exists_exterior_complementary_annulus h267 hB₀ hB₁ hC₀ hC₁ hmeet
  have hB : IsPLAnnulusWithEnds B J₀ J₁ :=
    hchoice.elim (fun h => h.symm ▸ hB₀) (fun h => h.symm ▸ hB₁)
  have hBT : B ⊆ T'' (2 * k) :=
    hchoice.elim (fun h => h.symm ▸ h₀T) (fun h => h.symm ▸ h₁T)
  have hCB : L.space ∩ B = J₀ ∪ J₁ :=
    hchoice.elim (fun h => h.symm ▸ hC₀) (fun h => h.symm ▸ hC₁)
  have hunion : (⋃ l : Fin 3, ![L.space, B₀, B₁] l) = L.space ∪ T'' (2 * k) := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨l, hl⟩ := mem_iUnion.mp hy
      fin_cases l
      · exact Or.inl hl
      · exact Or.inr (h₀T hl)
      · exact Or.inr (h₁T hl)
    · intro y hy
      rcases hy with hy | hy
      · exact mem_iUnion.mpr ⟨0, hy⟩
      · rcases hcover.subset hy with hy | hy
        · exact mem_iUnion.mpr ⟨1, hy⟩
        · exact mem_iUnion.mpr ⟨2, hy⟩
  have hBfront : B ⊆ frontier (connectedComponentIn (L.space ∪ T'' (2 * k))ᶜ x) := by
    rw [← hunion, hfront]
    rcases hfrontier with rfl | rfl
    · exact subset_union_left
    · exact subset_union_right
  have hexterior : ∃ x, x ∉ L.space ∪ T'' (2 * k) ∧
      ¬ Bornology.IsBounded (connectedComponentIn (L.space ∪ T'' (2 * k))ᶜ x) ∧
      B ⊆ frontier (connectedComponentIn (L.space ∪ T'' (2 * k))ᶜ x) :=
    ⟨x, hunion ▸ hx, hunion ▸ hunbounded, hBfront⟩
  let V := (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪ φ '' S (2 * (i + 1))
  have hV : IsTopologicalSolidTorus V := by
    simpa only [V, show 2 * (i + 1) = 2 * i + 2 by omega] using
      htw.outer_triple_isTopologicalSolidTorus (2 * i)
  have hVI : V ⊆ I :=
    union_subset (union_subset (htw.subsetInterior _) (htw.subsetInterior _))
      (htw.subsetInterior _)
  have hTV : T'' (2 * k) ⊆ interior V := by
    have hinner : S'' (2 * k) ⊆ interior (φ '' S (2 * k)) := by
      simpa using (htw.config (2 * k)).innerSubset 0
    have houter : φ '' S (2 * k) ⊆ V := by
      rcases hk with rfl | rfl
      · exact subset_union_left.trans subset_union_left
      · exact subset_union_right
    exact (htw.boundary_subset_solid _).trans (hinner.trans (interior_mono houter))
  have hCM : L.space ⊆ towerSurface T'' (fun j => (X j).space) P' := by
    intro x hx
    exact Or.inl (mem_iUnion.mpr ⟨i, Or.inr (hLX hx)⟩)
  have hBM : B ⊆ towerSurface T'' (fun j => (X j).space) P' := by
    intro x hx
    exact Or.inl (mem_iUnion.mpr ⟨k, Or.inl (hBT hx)⟩)
  have hVavoid : Disjoint V ({a, b} : Set E3) :=
    ((havoid (2 * i)).union_left (havoid (2 * i + 1))).union_left
      (havoid (2 * (i + 1)))
  have hsep : IsSeparatorIn I
      (towerSurface T'' (fun j => (X j).space) P' \
        (L.space \ (J₀ ∪ J₁))) {a} {b} := by
    exact ⟨hR, hC.separates_after_delete_interior hB hCB hI hV hVI
      (union_subset (hLX.trans (hX.interiorCarrier i)) (hBT.trans hTV)) hCM hBM hR
      (fun hx => disjoint_left.mp hVavoid hx (Or.inl rfl))
      (fun hx => disjoint_left.mp hVavoid hx (Or.inr rfl)) hX.separator.2⟩
  rcases hchoice with hchoice | hchoice
  · subst B
    exact ⟨B₀, B₁, hB₀, hB₁, hcover, hmeet, hCT, hsep, hexterior⟩
  · subst B
    exact ⟨B₁, B₀, hB₁, hB₀, hcover.trans (union_comm _ _),
      (inter_comm _ _).trans hmeet, hCT, hsep, hexterior⟩

end DifferentialGeometry.Topology.PiecewiseLinear
