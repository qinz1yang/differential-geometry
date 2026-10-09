/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusPatchDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentSeamDisks
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceClosedTraces
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerCarrierTorus
import DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.TorusCirclePair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable [DecidableEq E3] {X : ℤ → Geometry.SimplicialComplex ℝ E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

theorem IsCanonicalSurface.exists_annulus_pair_of_returning_component
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314)
    (i : ℤ) (c : ConnectedComponents (X i).space) {J₀ J₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (hdis : Disjoint J₀ J₁) (k : ℤ) (hk : k = i ∨ k = i + 1)
    (h₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (h₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (hess₀ : ¬ boundsDiskIn J₀ (T'' (2 * i + 1)))
    (hess₁ : ¬ boundsDiskIn J₁ (T'' (2 * i + 1))) :
    ∃ B₀ B₁ : Set E3, IsPLAnnulusWithEnds B₀ J₀ J₁ ∧
      IsPLAnnulusWithEnds B₁ J₀ J₁ ∧ T'' (2 * k) = B₀ ∪ B₁ ∧
      B₀ ∩ B₁ = J₀ ∪ J₁ ∧
      (connectedComponentComplex (X i) c).space ∩ T'' (2 * k) = J₀ ∪ J₁ := by
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let L := connectedComponentComplex (X i) c
  let _ : Finite L.faces := (connectedComponentComplex_faces_finite (X i) c).to_subtype
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hLb : (boundaryComplex 2 L).space = J₀ ∪ J₁ := hC.boundaryComplex_space L
  have hess {G : Set E3}
      (hG : G ∈ traceCircles L.space (T'' (2 * k)))
      (hGe : ¬ boundsDiskIn G (T'' (2 * i + 1))) :
      ¬ boundsDiskIn G (T'' (2 * k)) := by
    intro hd
    rcases hk with hk | hk
    · subst k
      exact hGe ((hX.lower_component_boundsDiskIn_iff htw h314 i c hG).mp hd)
    · subst k
      exact hGe ((hX.upper_component_boundsDiskIn_iff htw h314 i c hG).mp hd)
  have hsolid : IsCombinatorialSolidTorus (S'' (2 * k)) := by
    simpa using (htw.config (2 * k)).isPolyhedralSolidTorus 0
  have h₀S : J₀ ⊆ frontier (S'' (2 * k)) :=
    fun _ hx => (htw.boundary_eq _).subset (traceCircles_subset h₀ hx).2
  have h₁S : J₁ ⊆ frontier (S'' (2 * k)) :=
    fun _ hx => (htw.boundary_eq _).subset (traceCircles_subset h₁ hx).2
  obtain ⟨B, B', hB, hB', hBB', hmeet⟩ :=
    hsolid.exists_annulus_pair_of_essential_circles (traceCircles_isPLSphere h₀)
      (traceCircles_isPLSphere h₁) h₀S h₁S hdis
      (by simpa only [← htw.boundary_eq] using hess h₀ hess₀)
      (by simpa only [← htw.boundary_eq] using hess h₁ hess₁)
  refine ⟨B, B', hB, hB', (htw.boundary_eq _).trans hBB'.symm, hmeet, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxL, hxT⟩
    apply hLb.subset
    exact (boundaryComplex_space_connectedComponentComplex 2 (X i) c).symm.subset
      ⟨hX.inter_even_subset_boundary htw i k ⟨hLX hxL, hxT⟩, hxL⟩
  · intro x hx
    rcases hx with hx | hx
    · exact traceCircles_subset h₀ hx
    · exact traceCircles_subset h₁ hx

theorem IsCanonicalSurface.isSeparatorIn_after_delete_returning_component
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T'' I P' a b)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
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
    IsSeparatorIn I
      (towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))) {a} {b} := by
  let L := connectedComponentComplex (X i) c
  have hLX : L.space ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  obtain ⟨B, B', hB, -, hBB', hmeet, hCT⟩ :=
    hX.exists_annulus_pair_of_returning_component htw h314 i c hC hdis k hk h₀ h₁
      hess₀ hess₁
  have hBT : B ⊆ T'' (2 * k) := subset_union_left.trans hBB'.symm.subset
  have hCB : L.space ∩ B = J₀ ∪ J₁ := by
    apply Subset.antisymm
    · rintro x ⟨hxL, hxB⟩
      exact hCT.subset ⟨hxL, hBT hxB⟩
    · intro x hx
      exact ⟨(hCT.symm.subset hx).1, (hmeet.symm.subset hx).1⟩
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
  refine ⟨hR, hC.separates_after_delete_interior hB hCB hI hV hVI
    (union_subset (hLX.trans (hX.interiorCarrier i)) (hBT.trans hTV)) hCM hBM hR
    (fun hx => disjoint_left.mp hVavoid hx (Or.inl rfl))
    (fun hx => disjoint_left.mp hVavoid hx (Or.inr rfl)) hX.separator.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
