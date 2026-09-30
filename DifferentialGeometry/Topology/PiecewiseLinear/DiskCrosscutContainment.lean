/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskCircleStep

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_disk_subset_of_circle_subset {D₀ J : Set E}
    {q₀ : (Fin 3 → ℝ) → E} (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hJ : IsPLSphere 1 J) (hJD₀ : J ⊆ D₀) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ D₀ ∧ q '' stdSimplexBoundary 2 = J := by
  obtain ⟨Pl, ρ, hPl, hρ, -⟩ := hq₀.exists_planarModel
  let σ := Function.invFunOn ρ Pl
  have hσ : IsPLHomeomorphOn σ D₀ Pl := hρ.symm
  have hJp : IsPLSphere 1 (σ '' J) :=
    hJ.of_isPLHomeomorphOn (hσ.restrict hJ.isPolyhedron hJD₀)
  have hPlinside : closure (Schoenflies.inside (frontier Pl)) = Pl :=
    PlanarJordan.closure_inside_frontier_eq_of_isCompact hPl.isPolyhedron.isCompact
      (isJordanCurve_of_isPLSphere_one hPl.isPLSphere_frontier) hPl.interior_nonempty
  have hinside := PlanarJordan.inside_subset_of_subset_closure_inside
    (Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hPl.isPLSphere_frontier))
    (Schoenflies.jordan_curve_theorem (isJordanCurve_of_isPLSphere_one hJp))
    (by rw [hPlinside]; exact (image_mono hJD₀).trans hσ.image_eq.subset)
  let Q := closure (Schoenflies.inside (σ '' J))
  have hQ : IsPLBall 2 Q := isPLBall_closure_inside_of_isPLSphere_one hJp
  have hQPl : Q ⊆ Pl := (closure_mono hinside).trans hPlinside.subset
  have hQpoly := hQ.isPolyhedron
  obtain ⟨r, hr⟩ := hQ
  have hρJ : ρ '' (σ '' J) = J := by
    rw [image_image]
    exact (image_congr fun y hy => hρ.bijOn.invOn_invFunOn.2 (hJD₀ hy)).trans (image_id' J)
  refine ⟨ρ '' Q, ρ ∘ r, hr.trans (hρ.restrict hQpoly hQPl),
    (image_mono hQPl).trans hρ.image_eq.subset, ?_⟩
  rw [image_comp, hr.image_stdSimplexBoundary_eq_frontier (n := 1),
    frontier_closure_inside_of_isPLSphere_one hJp, hρJ]

theorem IsPLHomeomorphOn.disk_inter_boundary_subset_boundary {D D₀ : Set E}
    {q q₀ : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀) (hDD₀ : D ⊆ D₀) :
    D ∩ (q₀ '' stdSimplexBoundary 2) ⊆ q '' stdSimplexBoundary 2 := by
  obtain ⟨Pl, ρ, hPl, hρ, hρbd⟩ := hq₀.exists_planarModel
  let σ := Function.invFunOn ρ Pl
  have hσ : IsPLHomeomorphOn σ D₀ Pl := hρ.symm
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hq' := hq.trans (hσ.restrict hD.isPolyhedron hDD₀)
  have hDpPl : σ '' D ⊆ Pl := (image_mono hDD₀).trans hσ.image_eq.subset
  rintro x ⟨hxD, hxJ₀⟩
  have hxPl : σ x ∈ frontier Pl := by
    obtain ⟨z, hz, hzx⟩ := hρbd.symm.subset hxJ₀
    rw [← hzx]
    change Function.invFunOn ρ Pl (ρ z) ∈ frontier Pl
    rw [hρ.bijOn.invOn_invFunOn.1 (hPl.isPolyhedron.isClosed.frontier_subset hz)]
    exact hz
  have hxDp : σ x ∈ frontier (σ '' D) :=
    ⟨subset_closure (mem_image_of_mem σ hxD), fun hxint => hxPl.2 (interior_mono hDpPl hxint)⟩
  rw [← hq'.image_stdSimplexBoundary_eq_frontier (n := 1)] at hxDp
  obtain ⟨a, ha, hax⟩ := hxDp
  have hax' : q a = x := hσ.bijOn.injOn (hDD₀ (hq.bijOn.mapsTo ha.1)) (hDD₀ hxD) hax
  exact ⟨a, ha, hax'⟩

theorem IsPLHomeomorphOn.exists_disk_between_proper_arc_and_boundary_arc {D₀ A B : Set E}
    {q₀ : (Fin 3 → ℝ) → E} (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    {γ δ : ℝ → E} (hγ : IsPLHomeomorphOn γ (Icc 0 1) A)
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) B) (hδ0 : δ 0 = γ 0) (hδ1 : δ 1 = γ 1)
    (hAD₀ : A ⊆ D₀) (hBJ₀ : B ⊆ q₀ '' stdSimplexBoundary 2)
    (hAJ₀ : A ∩ (q₀ '' stdSimplexBoundary 2) = {γ 0, γ 1}) :
    ∃ (D : Set E) (q : (Fin 3 → ℝ) → E), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ D₀ ∧ q '' stdSimplexBoundary 2 = A ∪ B ∧ D ∩ (q₀ '' stdSimplexBoundary 2) = B := by
  have hendsB : ({γ 0, γ 1} : Set E) ⊆ B := by
    rw [← hδ0, ← hδ1]
    exact pair_subset (hδ.bijOn.mapsTo (by norm_num)) (hδ.bijOn.mapsTo (by norm_num))
  have hAB : A ∩ B = {γ 0, γ 1} := Subset.antisymm
    (fun x hx => hAJ₀.subset ⟨hx.1, hBJ₀ hx.2⟩)
    (fun x hx => ⟨(pair_subset (hγ.bijOn.mapsTo (by norm_num))
      (hγ.bijOn.mapsTo (by norm_num))) hx, hendsB hx⟩)
  have hJ : IsPLSphere 1 (A ∪ B) :=
    isPLSphere_one_union_of_isPLHomeomorphOn_Icc hγ hδ hδ0 hδ1 hAB
  have hJ₀D₀ : q₀ '' stdSimplexBoundary 2 ⊆ D₀ := by
    rw [← hq₀.image_eq]
    exact image_mono fun x hx => hx.1
  obtain ⟨D, q, hq, hDD₀, hqJ⟩ := hq₀.exists_disk_subset_of_circle_subset hJ
    (union_subset hAD₀ (hBJ₀.trans hJ₀D₀))
  have hsmall := hq.disk_inter_boundary_subset_boundary hq₀ hDD₀
  refine ⟨D, q, hq, hDD₀, hqJ, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxD, hxJ₀⟩
    have hxJ := hqJ.subset (hsmall ⟨hxD, hxJ₀⟩)
    rcases hxJ with hxA | hxB
    · exact hendsB (hAJ₀.subset ⟨hxA, hxJ₀⟩)
    · exact hxB
  · intro x hxB
    obtain ⟨a, ha, hax⟩ := hqJ.symm.subset (Or.inr hxB)
    exact ⟨hax ▸ hq.bijOn.mapsTo ha.1, hBJ₀ hxB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
