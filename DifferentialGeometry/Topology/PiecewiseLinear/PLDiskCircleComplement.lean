/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskCircleStep

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_disk_complement_of_circle {Δ J : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hJ : IsPLSphere 1 J) (hJΔ : J ⊆ Δ) (hJbd : Disjoint J (r '' stdSimplexBoundary 2)) :
    ∃ (R Q : Set E) (q : (Fin 3 → ℝ) → E), IsPolyhedron R ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧ R ∪ Q = Δ ∧ R ∩ Q = J ∧
      q '' stdSimplexBoundary 2 = J ∧ r '' stdSimplexBoundary 2 ⊆ R := by
  obtain ⟨Pl, ρ, hPl, hρ, hρb⟩ := hr.exists_planarModel
  let σ := Function.invFunOn ρ Pl
  have hσ : IsPLHomeomorphOn σ Δ Pl := hρ.symm
  have hρσ : ∀ y ∈ Δ, ρ (σ y) = y := fun y hy => hρ.bijOn.invOn_invFunOn.2 hy
  have hρinj := hρ.bijOn.injOn
  have hPlcl := hPl.isPolyhedron.isClosed
  have hfrPl : frontier Pl ⊆ Pl := hPlcl.frontier_subset
  have hJp : IsPLSphere 1 (σ '' J) :=
    hJ.of_isPLHomeomorphOn (hσ.restrict hJ.isPolyhedron hJΔ)
  have hJint : σ '' J ⊆ interior Pl := by
    rintro _ ⟨y, hy, rfl⟩
    have hyPl := hσ.bijOn.mapsTo (hJΔ hy)
    apply (mem_interior_iff_notMem_frontier hyPl).mpr
    intro hyfr
    have hybd : y ∈ r '' stdSimplexBoundary 2 := by
      rw [← hρb]
      exact ⟨σ y, hyfr, hρσ y (hJΔ hy)⟩
    exact Set.disjoint_left.mp hJbd hy hybd
  have hρJ : ρ '' (σ '' J) = J := by
    rw [image_image]
    exact (image_congr fun y hy => hρσ y (hJΔ hy)).trans (image_id' J)
  let Qp := closure (Schoenflies.inside (σ '' J))
  have hQp : IsPLBall 2 Qp := isPLBall_closure_inside_of_isPLSphere_one hJp
  have hQint : Qp ⊆ interior Pl := closure_inside_subset_interior_of_subset_interior
    hPl (isJordanCurve_of_isPLSphere_one hJp) hJint
  have hQPl : Qp ⊆ Pl := hQint.trans interior_subset
  have hfrQ : frontier Qp = σ '' J := frontier_closure_inside_of_isPLSphere_one hJp
  have hQcl : IsClosed Qp := isClosed_closure
  let Rp := closure (Pl \ Qp)
  have hRPl : Rp ⊆ Pl := closure_minimal sdiff_subset hPlcl
  have hRint : Disjoint Rp (interior Qp) :=
    ((Set.disjoint_left.mpr fun x hx hx' => hx'.2 (interior_subset hx)).closure_right
      isOpen_interior).symm
  have hRQ : Rp ∩ Qp = σ '' J := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxQ⟩
      rw [← hfrQ]
      exact ⟨subset_closure hxQ, fun hxi => Set.disjoint_left.mp hRint hxR hxi⟩
    · intro x hx
      have hxfr : x ∈ frontier Qp := hfrQ.symm ▸ hx
      refine ⟨?_, hQcl.frontier_subset hxfr⟩
      rw [mem_closure_iff]
      intro U hU hxU
      have hU' : U ∩ interior Pl ∈ nhds x :=
        Filter.inter_mem (hU.mem_nhds hxU) (isOpen_interior.mem_nhds (hJint hx))
      obtain ⟨z, ⟨hzU, hzP⟩, hzQ⟩ :=
        mem_closure_iff_nhds.mp (frontier_eq_closure_inter_closure.subset hxfr).2 _ hU'
      exact ⟨z, hzU, interior_subset hzP, hzQ⟩
  have hcover : Rp ∪ Qp = Pl := by
    apply Subset.antisymm (union_subset hRPl hQPl)
    intro x hx
    by_cases hxQ : x ∈ Qp
    · exact Or.inr hxQ
    · exact Or.inl (subset_closure ⟨hx, hxQ⟩)
  have hfrR : frontier Pl ⊆ Rp := fun x hx => subset_closure ⟨hfrPl hx, fun hxQ =>
    Set.disjoint_left.mp disjoint_interior_frontier (hQint hxQ) hx⟩
  have hRp : IsPolyhedron Rp := hPl.isPolyhedron.closure_sdiff hQp.isPolyhedron
  obtain ⟨q, hq⟩ := id hQp
  refine ⟨ρ '' Rp, ρ '' Qp, ρ ∘ q,
    hRp.image_of_isPiecewiseAffineOn (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron hRp hRPl)
      (hρinj.mono hRPl), hq.trans (hρ.restrict hQp.isPolyhedron hQPl), ?_, ?_, ?_, ?_⟩
  · rw [← image_union, hcover, hρ.image_eq]
  · rw [← hρinj.image_inter hRPl hQPl, hRQ, hρJ]
  · rw [image_comp, hq.image_stdSimplexBoundary_eq_frontier (n := 1), hfrQ, hρJ]
  · rw [← hρb]
    exact image_mono hfrR

theorem IsPLHomeomorphOn.exists_replace_disk_of_interior_circle {Δ D J : Set E}
    {r q : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hqb : q '' stdSimplexBoundary 2 = J) (hDΔ : D ∩ Δ = J)
    (hJbd : Disjoint J (r '' stdSimplexBoundary 2)) :
    ∃ (Γ R : Set E) (p : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Γ ∧
      p '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      IsPolyhedron R ∧ R ⊆ Δ ∧ Γ = R ∪ D ∧ R ∩ D = J := by
  have hJ : IsPLSphere 1 J := hqb ▸ hq.isPLSphere_image_stdSimplexBoundary
  have hJΔ : J ⊆ Δ := hDΔ ▸ inter_subset_right
  obtain ⟨R, Q, q', hR, hq', hcover, hmeet, hq'b, hbdR⟩ :=
    hr.exists_disk_complement_of_circle hJ hJΔ hJbd
  have hRΔ : R ⊆ Δ := subset_union_left.trans hcover.subset
  have hRD : R ∩ D = J := by
    apply Subset.antisymm
    · exact fun y hy => hDΔ.subset ⟨hy.2, hRΔ hy.1⟩
    · intro y hy
      exact ⟨(hmeet.symm.subset hy).1, (hDΔ.symm.subset hy).1⟩
  obtain ⟨H, hH, hHid⟩ :=
    exists_isPLHomeomorphOn_replace_ball hR hq' hq hq'b hqb hmeet hRD
  rw [hcover] at hH
  refine ⟨R ∪ D, R, H ∘ r, hr.trans hH, ?_, hR, hRΔ, rfl, hRD⟩
  rw [image_comp, (hHid.mono hbdR).image_eq, image_id]

end DifferentialGeometry.Topology.PiecewiseLinear
