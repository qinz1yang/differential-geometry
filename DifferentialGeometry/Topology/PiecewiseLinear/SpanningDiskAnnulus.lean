/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceAnnulusComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_annulus_complement_of_spanning_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ K.space = r '' stdSimplexBoundary 2)
    (hU : U ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (hRfin : R.faces.Finite),
      letI := hRfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 R ∧ IsOrientable 2 R ∧
      eulerChar R = eulerChar K ∧
      ∃ (W : Set E) (ρ : E × ℝ → E) (D₀ D₁ : Set E) (q₀ q₁ : (Fin 3 → ℝ) → E),
        IsPolyhedron W ∧ W ⊆ K.space ∧ W ⊆ U ∧ W ∈ 𝓝ˢ[K.space] (r '' stdSimplexBoundary 2) ∧
        IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W ∧
        (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧
        R.space = closure (K.space \ W) ∧ R.space ⊆ K.space \ r '' stdSimplexBoundary 2 ∧
        Disjoint R.space D ∧
        IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
        IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧
        D ⊆ q₀ '' openSimplex (stdVertices 1) ∧ D ⊆ q₁ '' openSimplex (stdVertices 1) ∧
        D₀ ∩ D₁ = D ∧
        D₀ = D ∪ ρ '' ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 0) ∧
        D₁ = D ∪ ρ '' ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) ∧
        q₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) ∧
        q₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) ∧
        R.space ∩ D₀ = q₀ '' stdSimplexBoundary 2 ∧
        R.space ∩ D₁ = q₁ '' stdSimplexBoundary 2 ∧
        (boundaryComplex 2 R).space = q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 ∧
        W ∩ R.space = q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 ∧
        W ∪ R.space = K.space ∧ D₀ ∪ D₁ = D ∪ W ∧ R.space ∪ D₀ ∪ D₁ = K.space ∪ D ∧
        D₀ ∪ D₁ ⊆ D ∪ (K.space ∩ U) ∧ D₀ ∪ D₁ ∈ 𝓝ˢ[K.space ∪ D] D ∧
        (IsPreconnected (K.space \ r '' stdSimplexBoundary 2) → IsConnected R.space) := by
  let J := r '' stdSimplexBoundary 2
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJK : J ⊆ K.space := hmeet.symm.subset.trans inter_subset_right
  obtain ⟨R, hRfin, hR, hRo, hRχ, W, ρ, hW, hWK, hWU, hWnhds, hρ, hzero,
      hRspace, hRK, hRbd, hWR, hcover, -, -, -, hRc⟩ :=
    hK.exists_annulus_complement_of_isOrientable K hor hJ hJK hU
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hD₀, hD₁, hpair, hD₀eq, hD₁eq, hbd₀, hbd₁,
      hpairUnion, hpairNhds⟩ := exists_disk_pair_of_spanning_disk_of_bicollar
    (isPolyhedron_space K).isClosed hr hmeet hρ hzero hWK hWnhds
  have hRD : Disjoint R.space D := disjoint_left.mpr fun x hxR hxD =>
    (hRK hxR).2 (hmeet.subset ⟨hxD, (hRK hxR).1⟩)
  have hends : J ×ˢ {(-1 : ℝ), 1} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := by
    rintro z ⟨hz, ht | ht⟩
    · exact ⟨hz, ht.symm ▸ ⟨le_rfl, by norm_num⟩⟩
    · exact ⟨hz, ht.symm ▸ ⟨by norm_num, le_rfl⟩⟩
  have hinter (T : Set ℝ) (hT : T ⊆ Icc (-1 : ℝ) 1) :
      R.space ∩ ρ '' (J ×ˢ T) = ρ '' (J ×ˢ ({(-1 : ℝ), 1} ∩ T)) := by
    have hTW : ρ '' (J ×ˢ T) ⊆ W :=
      (image_mono (prod_mono Subset.rfl hT)).trans hρ.image_eq.subset
    calc
      R.space ∩ ρ '' (J ×ˢ T) = (W ∩ R.space) ∩ ρ '' (J ×ˢ T) := by
        ext x
        exact ⟨fun hx => ⟨⟨hTW hx.2, hx.1⟩, hx.2⟩, fun hx => ⟨hx.1.2, hx.2⟩⟩
      _ = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∩ ρ '' (J ×ˢ T) := by rw [hWR]
      _ = ρ '' ((J ×ˢ {(-1 : ℝ), 1}) ∩ (J ×ˢ T)) :=
        (hρ.bijOn.injOn.image_inter hends (prod_mono Subset.rfl hT)).symm
      _ = ρ '' (J ×ˢ ({(-1 : ℝ), 1} ∩ T)) := by rw [prod_inter_prod, inter_self]
  have hneg : {(-1 : ℝ), 1} ∩ Icc (-1 : ℝ) 0 = {(-1 : ℝ)} := by
    ext t
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨ht | ht, hlo, hhi⟩
      · exact ht
      · linarith
    · rintro rfl
      norm_num
  have hpos : {(-1 : ℝ), 1} ∩ Icc (0 : ℝ) 1 = {(1 : ℝ)} := by
    ext t
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_Icc]
    constructor
    · rintro ⟨ht | ht, hlo, hhi⟩
      · linarith
      · exact ht
    · rintro rfl
      norm_num
  have hmeet₀ : R.space ∩ D₀ = q₀ '' stdSimplexBoundary 2 := by
    rw [hD₀eq, inter_union_distrib_left, hRD.inter_eq, empty_union,
      hinter _ (Icc_subset_Icc le_rfl zero_le_one), hneg, hbd₀]
  have hmeet₁ : R.space ∩ D₁ = q₁ '' stdSimplexBoundary 2 := by
    rw [hD₁eq, inter_union_distrib_left, hRD.inter_eq, empty_union,
      hinter _ (Icc_subset_Icc (by norm_num) le_rfl), hpos, hbd₁]
  have hcircles : q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 =
      ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by
    rw [hbd₀, hbd₁, ← image_union, ← prod_union, singleton_union]
  have htotal : R.space ∪ D₀ ∪ D₁ = K.space ∪ D := by
    rw [union_assoc, hpairUnion, union_comm D W, ← union_assoc, union_comm R.space W, hcover]
  refine ⟨R, hRfin, hR, hRo, hRχ, W, ρ, D₀, D₁, q₀, q₁, hW, hWK, hWU, hWnhds,
    hρ, hzero, hRspace, hRK, hRD, hq₀, hq₁, ?_, ?_, hpair, hD₀eq, hD₁eq, hbd₀, hbd₁,
    hmeet₀, hmeet₁, hRbd.trans hcircles.symm, hWR.trans hcircles.symm,
    hcover, hpairUnion, htotal, ?_, hpairNhds, hRc⟩
  · rwa [hq₀.image_openSimplex_stdVertices]
  · rwa [hq₁.image_openSimplex_stdVertices]
  · exact hpairUnion.subset.trans (union_subset_union Subset.rfl fun _ hx => ⟨hWK hx, hWU hx⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
