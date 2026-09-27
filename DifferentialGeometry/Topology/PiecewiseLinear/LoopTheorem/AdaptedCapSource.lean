/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_pos_forall_prod_Icc_mem_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {K : Set X} (hK : IsCompact K) {f : X × ℝ → Y}
    (hf : ContinuousOn f (K ×ˢ Icc (-1 : ℝ) 1)) {O : Set Y} (hO : IsOpen O)
    (h0 : ∀ x ∈ K, f (x, 0) ∈ O) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ x ∈ K, ∀ t ∈ Icc (-s) s, f (x, t) ∈ O := by
  obtain ⟨G, hG, hGeq⟩ := continuousOn_iff'.mp hf O hO
  have hK0 : K ×ˢ ({0} : Set ℝ) ⊆ G := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst ht0
    have hmem : (x, (0 : ℝ)) ∈ f ⁻¹' O ∩ K ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨h0 x hx, hx, by norm_num, by norm_num⟩
    rw [hGeq] at hmem
    exact hmem.1
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hK isCompact_singleton hG hK0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hv.mem_nhds (h0v (mem_singleton 0)))
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, fun x hx t ht => ?_⟩
  have hle₁ := min_le_left (ε / 2) 1
  have hle₂ := min_le_right (ε / 2) 1
  have htε : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hmem : (x, t) ∈ G ∩ K ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨huv ⟨hKu hx, hball htε⟩, hx, by linarith [ht.1], by linarith [ht.2]⟩
  rw [← hGeq] at hmem
  exact hmem.1

theorem isPLBall_union_image_outerCollar {E C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)} (hE : IsPLBall 2 E)
    (hρ : IsPLHomeomorphOn ρ (frontier E ×ˢ Icc (-1 : ℝ) 1) C)
    (hρ0 : ∀ x ∈ frontier E, ρ (x, 0) = x)
    (hout : ρ '' (frontier E ×ˢ Icc (-1 : ℝ) 0) ∩ E = frontier E) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) :
    IsPLBall 2 (E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0)) ∧
      frontier (E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0)) = ρ '' (frontier E ×ˢ {-s}) ∧
        E ⊆ interior (E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0)) := by
  obtain ⟨r, hr⟩ := id hE
  have hrb : r '' stdSimplexBoundary 2 = frontier E := hr.image_stdSimplexBoundary
  have hTpoly : IsPolyhedron (frontier E) := hE.isPLSphere_frontier.isPolyhedron
  have hsub : frontier E ×ˢ Icc (-s) 0 ⊆ frontier E ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc (by linarith) (by norm_num))
  have hρs : IsPLHomeomorphOn ρ (frontier E ×ˢ Icc (-s) 0)
      (ρ '' (frontier E ×ˢ Icc (-s) 0)) :=
    hρ.restrict (hTpoly.prod isHPolytope_Icc.isPolyhedron) hsub
  have hneg : IsPLHomeomorphOn (fun u : ℝ => -u) (Icc 0 s) (Icc (-s) 0) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
    refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
    · intro u hu
      change -s ≤ -u ∧ -u ≤ 0
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    · intro u hu
      exact ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, neg_neg u⟩
  have hρ' : IsPLHomeomorphOn (ρ ∘ Prod.map id fun u : ℝ => -u)
      ((r '' stdSimplexBoundary 2) ×ˢ Icc 0 s) (ρ '' (frontier E ×ˢ Icc (-s) 0)) := by
    rw [hrb]
    exact (hTpoly.isPLHomeomorphOn_id.prodMap hneg).trans hρs
  have hfix : ∀ x ∈ r '' stdSimplexBoundary 2,
      (ρ ∘ Prod.map id fun u : ℝ => -u) (x, 0) = x := by
    rw [hrb]
    intro x hx
    change ρ (x, -0) = x
    rw [neg_zero]
    exact hρ0 x hx
  have hmeet : ρ '' (frontier E ×ˢ Icc (-s) 0) ∩ E = r '' stdSimplexBoundary 2 := by
    rw [hrb]
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ (image_mono (prod_mono Subset.rfl
        (Icc_subset_Icc (by linarith) le_rfl)))).trans hout.subset
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, by linarith, le_rfl⟩, hρ0 x hx⟩,
        hE.isPolyhedron.isCompact.isClosed.frontier_subset hx⟩
  obtain ⟨q, hq, hqb, hdisj⟩ := hr.exists_isPLHomeomorphOn_union_collar hs hρ' hfix hmeet
  have himg : (ρ ∘ Prod.map id fun u : ℝ => -u) '' ((r '' stdSimplexBoundary 2) ×ˢ {s}) =
      ρ '' (frontier E ×ˢ {-s}) := by
    rw [hrb]
    ext y
    constructor
    · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
      have hu' : u = s := hu
      exact ⟨(x, -u), ⟨hx, show -u = -s by rw [hu']⟩, rfl⟩
    · rintro ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
      have hu' : u = -s := hu
      refine ⟨(x, -u), ⟨hx, show -u = s by rw [hu', neg_neg]⟩, ?_⟩
      change ρ (x, - -u) = ρ (x, u)
      rw [neg_neg]
  have hqf : q '' stdSimplexBoundary 2 = frontier (E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0)) :=
    hq.image_stdSimplexBoundary
  have hfront : frontier (E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0)) = ρ '' (frontier E ×ˢ {-s}) := by
    rw [← hqf, hqb, himg]
  refine ⟨⟨q, hq⟩, hfront, fun x hx => ?_⟩
  have hxU : x ∈ E ∪ ρ '' (frontier E ×ˢ Icc (-s) 0) := Or.inl hx
  refine (mem_interior_iff_notMem_frontier hxU).mpr fun hxf => ?_
  rw [← hqf] at hxf
  exact Set.disjoint_left.mp hdisj hx hxf

end DifferentialGeometry.Topology.PiecewiseLinear
