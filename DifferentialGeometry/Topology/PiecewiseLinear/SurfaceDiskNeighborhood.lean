/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceBicollarSides
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifold.exists_isPLHomeomorphOn_disk_neighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hor : IsOrientable 2 K)
    {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDK : D ⊆ K.space) (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ (D' : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ K.space ∩ U ∧
      D ⊆ D' \ q '' stdSimplexBoundary 2 ∧ D' ∈ 𝓝ˢ[K.space] D := by
  let J := r '' stdSimplexBoundary 2
  let B := closure (K.space \ D)
  have hJ : IsPLSphere 1 J := hr.isPLSphere_image_stdSimplexBoundary
  have hJD : J ⊆ D := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hBK : B ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hDB : D ∩ B = J := hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hDK
  have hcover : K.space ⊆ D ∪ B := fun y hy => by
    by_cases hyD : y ∈ D
    · exact Or.inl hyD
    · exact Or.inr (subset_closure ⟨hy, hyD⟩)
  obtain ⟨O, hO, hDO, hOU⟩ := mem_nhdsSetWithin.mp hU
  have hOJ : O ∈ 𝓝ˢ[K.space] J := mem_nhdsSetWithin.mpr
    ⟨O, hO, hJD.trans hDO, inter_subset_left⟩
  obtain ⟨W, ρ, -, hWK, hWO, hWnhds, hρ, hfix⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K hor hJ (hJD.trans hDK) hOJ
  have hJW : J ⊆ W := fun x hx => by
    rw [← hfix x hx]
    exact hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hmeet : W ∩ (D ∩ B) = J := by
    rw [hDB, inter_eq_right.mpr hJW]
  obtain ⟨V, hV, hJV, hVW⟩ := mem_nhdsSetWithin.mp hWnhds
  obtain ⟨x, hxJ⟩ := hJ.nonempty
  have hxD : x ∈ closure (D \ J) := by
    rw [show closure (D \ J) = D from hr.closure_sdiff_image_stdSimplexBoundary]
    exact hJD hxJ
  obtain ⟨a, haV, haD, haJ⟩ := mem_closure_iff.mp hxD V hV (hJV hxJ)
  have ha : (W \ B).Nonempty := ⟨a, hVW ⟨haV, hDK haD⟩,
    fun haB => haJ (hDB.subset ⟨haD, haB⟩)⟩
  have hxB : x ∈ B := (hDB.symm.subset hxJ).2
  obtain ⟨b, hbV, hbK, hbD⟩ := mem_closure_iff.mp hxB V hV (hJV hxJ)
  have hb : (W \ D).Nonempty := ⟨b, hVW ⟨hbV, hbK⟩, hbD⟩
  obtain ⟨σ, hσ, hσ0⟩ := hρ.exists_half_collar_of_closed_cover hJ hfix
    (show IsPLBall 2 D from ⟨r, hr⟩).isPolyhedron.isClosed isClosed_closure
    (hWK.trans hcover) hmeet ha hb
  have hAD : (W ∩ B) ∩ D = J := by
    ext y
    constructor
    · rintro ⟨⟨-, hyB⟩, hyD⟩
      exact hDB.subset ⟨hyD, hyB⟩
    · intro hyJ
      exact ⟨⟨hJW hyJ, (hDB.symm.subset hyJ).2⟩, hJD hyJ⟩
  obtain ⟨q, hq, -, hqD⟩ := hr.exists_isPLHomeomorphOn_union_collar zero_lt_one hσ hσ0 hAD
  have hsub : D ∪ (W ∩ B) ⊆ K.space ∩ U := by
    rintro y (hyD | ⟨hyW, -⟩)
    · exact ⟨hDK hyD, hOU ⟨hDO hyD, hDK hyD⟩⟩
    · exact ⟨hWK hyW, hOU ⟨hWO hyW, hWK hyW⟩⟩
  refine ⟨D ∪ (W ∩ B), q, hq, hsub,
    fun y hy => ⟨Or.inl hy, fun hybd => disjoint_left.mp hqD hy hybd⟩, ?_⟩
  apply mem_nhdsSetWithin.mpr
  refine ⟨V ∪ Bᶜ, hV.union isClosed_closure.isOpen_compl, ?_, ?_⟩
  · intro y hyD
    by_cases hyB : y ∈ B
    · exact Or.inl (hJV (hDB.subset ⟨hyD, hyB⟩))
    · exact Or.inr hyB
  · rintro y ⟨hyV | hyB, hyK⟩
    · by_cases hyD : y ∈ D
      · exact Or.inl hyD
      · exact Or.inr ⟨hVW ⟨hyV, hyK⟩, subset_closure ⟨hyK, hyD⟩⟩
    · by_cases hyD : y ∈ D
      · exact Or.inl hyD
      · exact (hyB (subset_closure ⟨hyK, hyD⟩)).elim

end DifferentialGeometry.Topology.PiecewiseLinear
