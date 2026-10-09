/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsGeneralPositionSolidTorusRelative

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def traceCircles (L T : Set E3) : Set (Set E3) :=
  {G | ∃ x ∈ L ∩ T, G = connectedComponentIn (L ∩ T) x ∧ IsPLSphere 1 G}

def boundsDiskIn (G T : Set E3) : Prop :=
  ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
    IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
      G = r '' stdSimplexBoundary 2

noncomputable def nullTraceCount (L T : Set E3) : ℕ :=
  {G ∈ traceCircles L T | boundsDiskIn G T}.ncard

private theorem component_eq_of_finite_circle_union {ι : Type*} [Finite ι]
    {G : ι → Set E3} (hG : ∀ i, IsPLSphere 1 (G i))
    (hdis : Pairwise fun i j => Disjoint (G i) (G j)) {i : ι} {x : E3}
    (hx : x ∈ G i) : connectedComponentIn (⋃ j, G j) x = G i := by
  classical
  let R : Set E3 := ⋃ j ∈ {j | j ≠ i}, G j
  have hR : IsClosed R :=
    (Set.toFinite _).isClosed_biUnion fun j _ => (hG j).isPolyhedron.isClosed
  have hGR : Disjoint (G i) R := by
    refine disjoint_iUnion_right.mpr fun j => disjoint_iUnion_right.mpr fun hj => ?_
    exact hdis (Ne.symm hj)
  have hcover : (⋃ j, G j) ⊆ G i ∪ R := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_biUnion hji hj)
  have hxU : x ∈ ⋃ j, G j := mem_iUnion.mpr ⟨i, hx⟩
  refine Subset.antisymm ?_
    ((hG i).isConnected.isPreconnected.subset_connectedComponentIn hx (subset_iUnion G i))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
    (G i) R (hG i).isPolyhedron.isClosed hR
    ((connectedComponentIn_subset _ _).trans hcover)
    (by rw [hGR.inter_eq, inter_empty]) with h | h
  · exact h
  · exact (disjoint_left.mp hGR hx (h (mem_connectedComponentIn hxU))).elim

theorem traceCircles_eq_range_of_finite_circle_union {L T : Set E3} {ι : Type*} [Finite ι]
    {G : ι → Set E3} (hG : ∀ i, IsPLSphere 1 (G i))
    (hdis : Pairwise fun i j => Disjoint (G i) (G j)) (hcover : L ∩ T = ⋃ i, G i) :
    traceCircles L T = range G := by
  ext C
  constructor
  · rintro ⟨x, hx, hC, -⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ hx)
    refine ⟨i, ?_⟩
    rw [hC, hcover, component_eq_of_finite_circle_union hG hdis hxi]
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := (hG i).nonempty
    refine ⟨x, hcover.symm ▸ mem_iUnion.mpr ⟨i, hx⟩, ?_, hG i⟩
    rw [hcover, component_eq_of_finite_circle_union hG hdis hx]

theorem traceCircles_subset {L T G : Set E3} (hG : G ∈ traceCircles L T) : G ⊆ L ∩ T := by
  obtain ⟨x, -, rfl, -⟩ := hG
  exact connectedComponentIn_subset _ _

theorem traceCircles_isPLSphere {L T G : Set E3} (hG : G ∈ traceCircles L T) :
    IsPLSphere 1 G := hG.choose_spec.2.2

theorem nullTraceCount_le {L T : Set E3} (hfin : (traceCircles L T).Finite) :
    nullTraceCount L T ≤ (traceCircles L T).ncard :=
  Set.ncard_le_ncard (fun _ h => h.1) hfin

theorem nullTraceCount_eq_zero_iff {L T : Set E3} (hfin : (traceCircles L T).Finite) :
    nullTraceCount L T = 0 ↔ ∀ G ∈ traceCircles L T, ¬ boundsDiskIn G T := by
  rw [nullTraceCount, Set.ncard_eq_zero (hfin.subset fun _ h => h.1)]
  simp only [Set.eq_empty_iff_forall_notMem, mem_ofPred_eq, not_and]

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.solid_isPolyhedron
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsPolyhedron (S'' i) := by
  have hi : IsCombinatorialSolidTorus (S'' i) := by
    simpa using (htw.config i).isPolyhedralSolidTorus 0
  exact hi.isPolyhedron

theorem IsCanonicalTower.boundary_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    T'' i = frontier (S'' i) := by
  simpa using (htw.config i).boundaryEq 0

theorem IsCanonicalTower.boundary_isPolyhedron
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsPolyhedron (T'' i) := by
  rw [htw.boundary_eq i]
  exact (htw.solid_isPolyhedron i).frontier

theorem IsCanonicalTower.boundary_subset_solid
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    T'' i ⊆ S'' i := by
  rw [htw.boundary_eq i]
  exact (htw.solid_isPolyhedron i).isClosed.frontier_subset

theorem IsCanonicalTower.solid_subset_outer
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    S'' i ⊆ φ '' S i := by
  have hi : S'' i ⊆ interior (φ '' S i) := by
    simpa using (htw.config i).innerSubset 0
  exact hi.trans interior_subset

theorem IsCanonicalTower.boundary_subset_outer
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    T'' i ⊆ φ '' S i :=
  (htw.boundary_subset_solid i).trans (htw.solid_subset_outer i)

theorem IsCanonicalTower.finite_traceCircles
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (traceCircles (T'' i) (T'' (i + 1))).Finite := by
  obtain ⟨ι, hι, G, hG, hdis, hcover⟩ := (htw.config i).polygons 0
  have : Finite ι := hι
  have heq : T'' i ∩ T'' (i + 1) = ⋃ j, G j := by simpa using hcover
  rw [traceCircles_eq_range_of_finite_circle_union hG hdis heq]
  exact Set.finite_range G

theorem IsCanonicalTower.traceCircles_cover
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    T'' i ∩ T'' (i + 1) = ⋃ G ∈ traceCircles (T'' i) (T'' (i + 1)), G := by
  obtain ⟨ι, hι, G, hG, hdis, hcover⟩ := (htw.config i).polygons 0
  have : Finite ι := hι
  have heq : T'' i ∩ T'' (i + 1) = ⋃ j, G j := by simpa using hcover
  rw [traceCircles_eq_range_of_finite_circle_union hG hdis heq]
  simpa using heq

theorem IsCanonicalTower.finite_labelled_seams
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (window : Finset ℤ) :
    {p : ℤ × Set E3 | p.1 ∈ window ∧ p.2 ∈ traceCircles (T'' p.1) (T'' (p.1 + 1))}.Finite := by
  refine (window.finite_toSet.biUnion fun i _ =>
    (htw.finite_traceCircles i).image (fun G => (i, G))).subset ?_
  rintro ⟨i, G⟩ ⟨hi, hG⟩
  exact mem_biUnion hi ⟨G, hG, rfl⟩

theorem IsCanonicalTower.seam_generator_or_bounds_disks
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (i : ℤ) {G : Set E3}
    (hG : G ∈ traceCircles (T'' i) (T'' (i + 1))) :
    (∀ k ∈ ({i, i + 1} : Set ℤ), ∀ hsub : G ⊆ S'' k, ∀ x : G,
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' k)) x)) ∨
      (boundsDiskIn G (T'' i) ∧ boundsDiskIn G (T'' (i + 1))) := by
  have hpoly := traceCircles_isPLSphere hG
  have hsub : G ⊆ T'' i ∩ T'' (i + 1) := traceCircles_subset hG
  have hd := h314 _ _ _ _ _ _ _ _ _ _ _ (htw.config i) 0 G hpoly (by simpa using hsub)
  rcases hd with hgen | hdisk
  · left
    intro k hk hGS x
    rcases hk with rfl | rfl
    · let gen (Y : Set E3) : Prop := ∀ hsub : G ⊆ Y, ∀ y : G,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, Y)) y)
      have hg : gen (S'' (k + 0)) := hgen 0 (Or.inl rfl)
      rw [add_zero] at hg
      exact hg hGS x
    · simpa using hgen 1 (Or.inr rfl) (by simpa using hGS) x
  · right
    constructor
    · simpa [boundsDiskIn] using hdisk 0 (Or.inl rfl)
    · simpa [boundsDiskIn] using hdisk 1 (Or.inr rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
