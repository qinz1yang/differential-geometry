/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerFiniteWindow
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def evenTorusSeams (T'' : ℤ → Set E3) (i : ℤ) : Set (Set E3) :=
  traceCircles (T'' (2 * i - 1)) (T'' (2 * i)) ∪
    traceCircles (T'' (2 * i)) (T'' (2 * i + 1))

private theorem traceCircles_pairwiseDisjoint {L T : Set E3} :
    (traceCircles L T).PairwiseDisjoint id := by
  rintro C ⟨x, -, rfl, -⟩ D ⟨y, -, rfl, -⟩ hne
  refine disjoint_left.mpr fun z hzx hzy => ?_
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.finite_evenTorusSeams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (evenTorusSeams T'' i).Finite := by
  refine Set.Finite.union ?_ (htw.finite_traceCircles (2 * i))
  simpa only [sub_add_cancel] using htw.finite_traceCircles (2 * i - 1)

theorem evenTorusSeams_isPLSphere {T'' : ℤ → Set E3} {i : ℤ} {G : Set E3}
    (hG : G ∈ evenTorusSeams T'' i) : IsPLSphere 1 G := by
  rcases hG with hG | hG <;> exact traceCircles_isPLSphere hG

theorem evenTorusSeams_subset {T'' : ℤ → Set E3} {i : ℤ} {G : Set E3}
    (hG : G ∈ evenTorusSeams T'' i) : G ⊆ T'' (2 * i) := by
  rcases hG with hG | hG
  · exact (traceCircles_subset hG).trans inter_subset_right
  · exact (traceCircles_subset hG).trans inter_subset_left

theorem IsCanonicalTower.evenTorusSeams_pairwiseDisjoint
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (evenTorusSeams T'' i).PairwiseDisjoint id := by
  intro C hC D hD hne
  have hcross : ∀ {G H : Set E3},
      G ∈ traceCircles (T'' (2 * i - 1)) (T'' (2 * i)) →
      H ∈ traceCircles (T'' (2 * i)) (T'' (2 * i + 1)) → Disjoint G H := by
    intro G H hG hH
    refine (htw.solid_disjoint (i := 2 * i - 1) (k := 2 * i + 1)
      (by rw [le_abs]; omega)).mono ?_ ?_
    · exact ((traceCircles_subset hG).trans inter_subset_left).trans
        (htw.boundary_subset_solid _)
    · exact ((traceCircles_subset hH).trans inter_subset_right).trans
        (htw.boundary_subset_solid _)
  rcases hC with hC | hC <;> rcases hD with hD | hD
  · exact traceCircles_pairwiseDisjoint hC hD hne
  · exact hcross hC hD
  · exact (hcross hD hC).symm
  · exact traceCircles_pairwiseDisjoint hC hD hne

theorem IsCanonicalTower.center_notMem_interior_outer
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    P' ∉ interior (φ '' S i) := by
  have hdis : Disjoint (interior (φ '' S i)) (⋃ k, ⋃ (_ : k ≤ i - 2), φ '' S k) := by
    refine disjoint_iUnion_right.mpr fun k => disjoint_iUnion_right.mpr fun hk => ?_
    exact (htw.apart i k (by rw [le_abs]; omega)).mono_left interior_subset
  have hP : P' ∈ closure (⋃ k, ⋃ (_ : k ≤ i - 2), φ '' S k) := by
    rw [htw.closureLower]
    exact Or.inr rfl
  exact fun hx => disjoint_left.mp (hdis.closure_right isOpen_interior) hx hP

theorem IsCanonicalTower.exists_innermost_seam_disk
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ)
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (G Δ : Set E3) (q : (Fin 3 → ℝ) → E3),
      G ∈ evenTorusSeams T'' i ∧ IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ T'' (2 * i) ∧ q '' stdSimplexBoundary 2 = G ∧
      ∀ H ∈ evenTorusSeams T'' i, H ≠ G → Disjoint Δ H := by
  classical
  let _ : Finite (evenTorusSeams T'' i) := (htw.finite_evenTorusSeams i).to_subtype
  have hS : IsCombinatorialSolidTorus (S'' (2 * i)) := by
    simpa using (htw.config (2 * i)).isPolyhedralSolidTorus 0
  have hT : IsPLTorus (T'' (2 * i)) := by
    rw [htw.boundary_eq]
    exact hS.isPLTorus_frontier
  have hseed : ∃ (G : evenTorusSeams T'' i) (Δ : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T'' (2 * i) ∧
        q '' stdSimplexBoundary 2 = (G : Set E3) := by
    obtain ⟨G, hG, Δ, q, hq, hΔT, hqG⟩ := hnull
    exact ⟨⟨G, hG⟩, Δ, q, hq, hΔT, hqG.symm⟩
  obtain ⟨G, Δ, q, hq, hΔT, hqG, hdis⟩ := hT.exists_innermost_disk
    (fun G : evenTorusSeams T'' i => evenTorusSeams_isPLSphere G.property)
    (fun G => evenTorusSeams_subset G.property)
    (fun G H hne => htw.evenTorusSeams_pairwiseDisjoint i G.property H.property
      (fun heq => hne (Subtype.ext heq))) hseed
  exact ⟨G, Δ, q, G.property, hq, hΔT, hqG,
    fun H hH hne => hdis ⟨H, hH⟩ (fun heq => hne (congrArg Subtype.val heq))⟩

theorem IsCanonicalTower.exists_innermost_seam_neighborhood
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (i : ℤ) {a b : E3} (havoid : Disjoint (φ '' S (2 * i)) ({a, b} : Set E3))
    (hnull : ∃ G ∈ evenTorusSeams T'' i, boundsDiskIn G (T'' (2 * i))) :
    ∃ (G Δ Ω : Set E3) (q : (Fin 3 → ℝ) → E3),
      G ∈ evenTorusSeams T'' i ∧ IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ T'' (2 * i) ∧ q '' stdSimplexBoundary 2 = G ∧ IsOpen Ω ∧ Δ ⊆ Ω ∧
      Ω ⊆ I ∧ Ω ⊆ φ '' S (2 * i) ∧ Disjoint Ω ({P', a, b} : Set E3) ∧
      ∀ H ∈ evenTorusSeams T'' i, H ≠ G → Disjoint Ω H := by
  classical
  obtain ⟨G, Δ, q, hG, hq, hΔT, hqG, hdis⟩ := htw.exists_innermost_seam_disk i hnull
  let F : Set E3 := ⋃ H ∈ evenTorusSeams T'' i \ {G}, H
  have hother : (evenTorusSeams T'' i \ {G}).Finite := (htw.finite_evenTorusSeams i).sdiff
  have hF : IsClosed F := hother.isClosed_biUnion
    fun H hH => (evenTorusSeams_isPLSphere hH.1).isPolyhedron.isClosed
  let Ω : Set E3 := interior (φ '' S (2 * i)) \ (F ∪ ({P', a, b} : Set E3))
  have hinner : T'' (2 * i) ⊆ interior (φ '' S (2 * i)) := by
    have hS : S'' (2 * i) ⊆ interior (φ '' S (2 * i)) := by
      simpa using (htw.config (2 * i)).innerSubset 0
    exact (htw.boundary_subset_solid _).trans hS
  have hΩ : IsOpen Ω := isOpen_interior.sdiff (hF.union (Set.toFinite _).isClosed)
  have hΔΩ : Δ ⊆ Ω := by
    intro x hx
    refine ⟨hinner (hΔT hx), ?_⟩
    rintro (hxF | hxV)
    · obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp hxF
      exact disjoint_left.mp (hdis H hH.1 hH.2) hx hxH
    · rcases hxV with rfl | hxV
      · exact htw.center_notMem_interior_outer _ (hinner (hΔT hx))
      · exact disjoint_left.mp havoid (interior_subset (hinner (hΔT hx))) hxV
  refine ⟨G, Δ, Ω, q, hG, hq, hΔT, hqG, hΩ, hΔΩ,
    (sdiff_subset.trans interior_subset).trans (htw.subsetInterior _),
    sdiff_subset.trans interior_subset, ?_, ?_⟩
  · exact disjoint_left.mpr fun x hx hxV => hx.2 (Or.inr hxV)
  · intro H hH hne
    exact disjoint_left.mpr fun x hx hxH => hx.2 (Or.inl (mem_biUnion ⟨hH, hne⟩ hxH))

end DifferentialGeometry.Topology.PiecewiseLinear
