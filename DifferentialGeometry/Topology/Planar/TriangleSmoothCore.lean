/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Planar.TriangleRounding
import DifferentialGeometry.Topology.Compactness.Nonvanishing
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.PlanarJordan.InnermostDisk

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Planar

open Schoenflies (Plane)

theorem neg_coord_le_roundedTriangleFunction (b : AffineBasis (Fin 3) ℝ Plane)
    {ε : ℝ} (hε : 0 < ε) (i : Fin 3) (x : Plane) :
    -b.coord i x ≤ roundedTriangleFunction b ε x := by
  have h01 : Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x) ≤
      roundedTriangleFunction b ε x :=
    (le_max_left _ _).trans (Real.smoothMax.max_le hε _ _)
  fin_cases i
  · exact ((le_max_left _ _).trans (Real.smoothMax.max_le hε _ _)).trans h01
  · exact ((le_max_right _ _).trans (Real.smoothMax.max_le hε _ _)).trans h01
  · exact (le_max_right _ _).trans (Real.smoothMax.max_le hε _ _)

theorem roundedTriangleFunction_le_of_le_coord (b : AffineBasis (Fin 3) ℝ Plane)
    {ε m : ℝ} (hε : 0 < ε) {x : Plane} (hx : ∀ i, m ≤ b.coord i x) :
    roundedTriangleFunction b ε x ≤ -m + 2 * ε := by
  have h01 : Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x) ≤ -m + ε :=
    (Real.smoothMax.le_max_add hε _ _).trans
      (add_le_add (max_le (neg_le_neg (hx 0)) (neg_le_neg (hx 1))) (le_refl ε))
  have h2 : -b.coord 2 x ≤ -m + ε := by linarith [hx 2]
  have h := (Real.smoothMax.le_max_add hε
    (Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x)) (-b.coord 2 x)).trans
      (add_le_add (max_le h01 h2) (le_refl ε))
  change Real.smoothMax ε (Real.smoothMax ε (-b.coord 0 x) (-b.coord 1 x))
    (-b.coord 2 x) ≤ -m + 2 * ε
  linarith

theorem exists_diffeomorph_closedBall_subset_triangle
    (b : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : IsCompact K) (hKt : K ⊆ interior (convexHull ℝ (range b))) :
    ∃ D : Plane ≃ₘ[ℝ] Plane,
      K ⊆ D '' ball 0 1 ∧ D '' closedBall 0 1 ⊆ interior (convexHull ℝ (range b)) := by
  have hpos (x : Plane) (hx : x ∈ K) (i : Fin 3) : 0 < b.coord i x := by
    have h := hKt hx
    rw [b.interior_convexHull] at h
    exact h i
  have hi (i : Fin 3) : ∃ δ > 0, ∀ x ∈ K, δ < b.coord i x := by
    obtain ⟨δ, hδ, hb⟩ := DifferentialGeometry.Topology.exists_pos_lt_norm_of_isCompact hK
      (b.coord i).continuous_of_finiteDimensional.continuousOn
      (fun x hx => (hpos x hx i).ne')
    exact ⟨δ, hδ, fun x hx => by
      simpa only [Real.norm_eq_abs, abs_of_pos (hpos x hx i)] using hb x hx⟩
  choose δ hδ hb using hi
  let m := min (1 / 12 : ℝ) (min (δ 0) (min (δ 1) (δ 2)))
  have hm : 0 < m := lt_min (by norm_num) (lt_min (hδ 0) (lt_min (hδ 1) (hδ 2)))
  have hm12 : m ≤ 1 / 12 := min_le_left _ _
  have hmi (i : Fin 3) : m ≤ δ i := by
    fin_cases i
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let ε := m / 8
  have hε : 0 < ε := div_pos hm (by norm_num)
  let f := fun x => roundedTriangleFunction b ε x + m / 2
  have hsub : {x | f x ≤ 0} ⊆ interior (convexHull ℝ (range b)) := by
    intro x hx
    rw [b.interior_convexHull]
    intro i
    have hc := neg_coord_le_roundedTriangleFunction b hε i x
    change roundedTriangleFunction b ε x + m / 2 ≤ 0 at hx
    linarith
  let c := Finset.univ.centroid ℝ b
  have hc (i : Fin 3) : b.coord i c = 1 / 3 := by
    change b.coord i (Finset.univ.centroid ℝ b) = _
    rw [b.coord_apply_centroid (Finset.mem_univ i)]
    norm_num
  have hneg : f c < 0 := by
    have h := roundedTriangleFunction_le_of_le_coord b hε (fun i => (hc i).ge)
    change roundedTriangleFunction b ε c + m / 2 < 0
    dsimp [ε] at h
    linarith
  have hbounded := ((finite_range b).isCompact_convexHull ℝ).isBounded.subset
    (hsub.trans interior_subset)
  obtain ⟨D, -, -, hclosed, hopen, -⟩ := Diffeomorph.exists_diffeomorph_convex_sublevel
    ((convexOn_roundedTriangleFunction b hε).add (convexOn_const (m / 2) convex_univ))
    ((contDiff_roundedTriangleFunction b ε).add contDiff_const) hbounded hneg
  refine ⟨D, ?_, ?_⟩
  · rw [hopen]
    intro x hx
    have h := roundedTriangleFunction_le_of_le_coord b hε
      (fun i => (hmi i).trans (hb i x hx).le)
    change roundedTriangleFunction b ε x + m / 2 < 0
    dsimp [ε] at h
    linarith
  · rw [hclosed]
    exact hsub

theorem exists_smooth_jordan_disk_subset_triangle
    (b : AffineBasis (Fin 3) ℝ Plane) {K : Set Plane}
    (hK : IsCompact K) (hKt : K ⊆ interior (convexHull ℝ (range b))) :
    ∃ γ : AddCircle (1 : ℝ) → Plane,
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ ∧
      K ⊆ Schoenflies.inside (range γ) ∧
      closure (Schoenflies.inside (range γ)) ⊆ interior (convexHull ℝ (range b)) := by
  obtain ⟨D, hKD, hDt⟩ := exists_diffeomorph_closedBall_subset_triangle b hK hKt
  obtain ⟨γ, hγ, hrange⟩ := exists_isSmoothEmbedding_addCircle_range_eq_sphere
    (E := Plane) (by simp) 0 zero_lt_one
  refine ⟨D ∘ γ, hγ.diffeomorph_comp D, ?_, ?_⟩
  · rw [range_comp, hrange]
    have h := PlanarJordan.image_ball_eq_inside_image_sphere D.toHomeomorph 0 zero_lt_one
    simp only [Diffeomorph.coe_toHomeomorph] at h
    rw [← h]
    exact hKD
  · rw [range_comp, hrange]
    have h := PlanarJordan.image_closedBall_eq_closure_inside_image_sphere
      D.toHomeomorph 0 zero_lt_one
    simp only [Diffeomorph.coe_toHomeomorph] at h
    rw [← h]
    exact hDt

theorem exists_smooth_jordan_core_triangle
    (b : AffineBasis (Fin 3) ℝ Plane) {U : Set Plane}
    (hU : IsOpen U) (hboundary : frontier (convexHull ℝ (range b)) ⊆ U) :
    ∃ γ : AddCircle (1 : ℝ) → Plane,
      Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) ∞ γ ∧
      closure (Schoenflies.inside (range γ)) ⊆ interior (convexHull ℝ (range b)) ∧
      convexHull ℝ (range b) \ Schoenflies.inside (range γ) ⊆ U := by
  have hC : IsCompact (convexHull ℝ (range b)) := (finite_range b).isCompact_convexHull ℝ
  have hK : IsCompact (convexHull ℝ (range b) \ U) := hC.diff hU
  have hKt : convexHull ℝ (range b) \ U ⊆ interior (convexHull ℝ (range b)) := by
    intro x hx
    by_contra hint
    exact hx.2 (hboundary ⟨subset_closure hx.1, hint⟩)
  obtain ⟨γ, hγ, hinside, hclosed⟩ := exists_smooth_jordan_disk_subset_triangle b hK hKt
  refine ⟨γ, hγ, hclosed, ?_⟩
  intro x hx
  by_contra hxU
  exact hx.2 (hinside ⟨hx.1, hxU⟩)

end DifferentialGeometry.Topology.Planar
