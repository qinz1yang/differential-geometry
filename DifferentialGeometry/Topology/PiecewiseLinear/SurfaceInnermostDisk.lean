/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskCircleComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_innermost_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {ι : Type*} [Finite ι] {J : ι → Set E}
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hJK : ∀ i, J i ⊆ K.space)
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hseed : ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ K.space ∧
        q '' stdSimplexBoundary 2 = J i) :
    ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ K.space ∧
        q '' stdSimplexBoundary 2 = J i ∧ ∀ j, j ≠ i → Disjoint D (J j) := by
  classical
  have hside : ∀ {D Y : Set E} {q : (Fin 3 → ℝ) → E} {i : ι},
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ K.space →
      q '' stdSimplexBoundary 2 = J i → IsPreconnected Y → Y ⊆ K.space →
      Disjoint Y (J i) → Y ⊆ D ∨ Disjoint D Y := by
    intro D Y q i hq hDK hqJ hY hYK hYJ
    have hD : IsPLBall 2 D := ⟨q, hq⟩
    have hmeet : D ∩ closure (K.space \ D) = J i := by
      rw [hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hq hDK, hqJ]
    have hcover : Y ⊆ D ∪ closure (K.space \ D) := fun y hy => by
      by_cases hyD : y ∈ D
      · exact Or.inl hyD
      · exact Or.inr (subset_closure ⟨hYK hy, hyD⟩)
    have hdis : Y ∩ (D ∩ closure (K.space \ D)) = ∅ := by
      rw [hmeet]
      exact hYJ.inter_eq
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (K.space \ D))
      hD.isPolyhedron.isClosed isClosed_closure hcover hdis with h | h
    · exact Or.inl h
    · refine Or.inr (Set.disjoint_left.mpr fun y hyD hyY => ?_)
      have hy : y ∈ D ∩ closure (K.space \ D) := ⟨hyD, h hyY⟩
      rw [hmeet] at hy
      exact Set.disjoint_left.mp hYJ hyY hy
  have hex : ∃ n, ∃ (i : ι) (D : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ K.space ∧
        q '' stdSimplexBoundary 2 = J i ∧ {j | j ≠ i ∧ J j ⊆ D}.ncard = n := by
    obtain ⟨i, D, q, hq, hDK, hqJ⟩ := hseed
    exact ⟨_, i, D, q, hq, hDK, hqJ, rfl⟩
  obtain ⟨i, D, q, hq, hDK, hqJ, hn⟩ := Nat.find_spec hex
  have hnone : ∀ j, j ≠ i → ¬ J j ⊆ D := by
    intro j hji hjD
    have hjbd : Disjoint (J j) (q '' stdSimplexBoundary 2) := hqJ ▸ hdisj hji
    obtain ⟨R, Q, q', -, hq', hRQ, hmeet, hq'J, hbdR⟩ :=
      hq.exists_disk_complement_of_circle (hJ j) hjD hjbd
    have hQD : Q ⊆ D := subset_union_right.trans hRQ.subset
    have hQi : Disjoint (J i) Q := by
      refine Set.disjoint_left.mpr fun x hxi hxQ => ?_
      have hxR : x ∈ R := hbdR (hqJ.symm ▸ hxi)
      have hxj : x ∈ J j := hmeet.subset ⟨hxR, hxQ⟩
      exact Set.disjoint_left.mp (hdisj hji) hxj hxi
    have hlt : {k | k ≠ j ∧ J k ⊆ Q}.ncard < {k | k ≠ i ∧ J k ⊆ D}.ncard := by
      refine Set.ncard_lt_ncard (ssubset_of_subset_not_subset
        (fun k hk => ⟨fun hki => ?_, hk.2.trans hQD⟩) fun hsub => ?_)
      · obtain ⟨y, hy⟩ := (hJ k).nonempty
        subst k
        exact Set.disjoint_left.mp hQi hy (hk.2 hy)
      · exact (hsub ⟨hji, hjD⟩).1 rfl
    have hmin := Nat.find_min' hex ⟨j, Q, q', hq', hQD.trans hDK, hq'J, rfl⟩
    omega
  refine ⟨i, D, q, hq, hDK, hqJ, fun j hji => ?_⟩
  rcases hside hq hDK hqJ (hJ j).isConnected.isPreconnected (hJK j) (hdisj hji) with h | h
  · exact absurd h (hnone j hji)
  · exact h

theorem IsPLTorus.exists_innermost_disk {T : Set (EuclideanSpace ℝ (Fin 3))}
    (hT : IsPLTorus T) {ι : Type*} [Finite ι]
    {J : ι → Set (EuclideanSpace ℝ (Fin 3))}
    (hJ : ∀ i, IsPLSphere 1 (J i)) (hJT : ∀ i, J i ⊆ T)
    (hdisj : Pairwise fun i j => Disjoint (J i) (J j))
    (hseed : ∃ (i : ι) (D : Set (EuclideanSpace ℝ (Fin 3)))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ T ∧
        q '' stdSimplexBoundary 2 = J i) :
    ∃ (i : ι) (D : Set (EuclideanSpace ℝ (Fin 3)))
      (q : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ D ⊆ T ∧
        q '' stdSimplexBoundary 2 = J i ∧ ∀ j, j ≠ i → Disjoint D (J j) := by
  obtain ⟨K, hKfin, hK, -, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  rw [← hKT] at hJT hseed ⊢
  exact hK.exists_innermost_disk K hJ hJT hdisj hseed

end DifferentialGeometry.Topology.PiecewiseLinear
