/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.EuclideanSurfaceOrientation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLTorus.exists_disk_neighborhood {T D U : Set E3} (hT : IsPLTorus T)
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hDT : D ⊆ T) (hU : U ∈ 𝓝ˢ[T] D) :
    ∃ (D' : Set E3) (q : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' ∧ D' ⊆ T ∩ U ∧
      D ⊆ D' \ q '' stdSimplexBoundary 2 ∧ D' ∈ 𝓝ˢ[T] D := by
  obtain ⟨K, hKfin, hK, hKconn, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  rw [← hKT] at hDT hU ⊢
  exact hK.exists_isPLHomeomorphOn_disk_neighborhood K
    (hK.isOrientable_euclidean_three K hKconn) hr hDT hU

theorem IsPLTorus.exists_exterior_collar_of_crossing {T X J U : Set E3}
    (hT : IsPLTorus T) (hJ : IsPLSphere 1 J) (hJT : J ⊆ T)
    (hJX : J ⊆ frontier X) (hX : IsClosed X) (hU : IsOpen U) (hJU : J ⊆ U)
    (htrace : U ∩ T ∩ frontier X ⊆ J) {x : E3} (hxJ : x ∈ J)
    (hcross : HasPLCrossingAt T (frontier X) x) (hreg : x ∈ closure (interior X)) :
    ∃ (W : Set E3) (ρ : E3 × ℝ → E3),
      IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ y ∈ J, ρ (y, 0) = y) ∧ W ⊆ (T \ interior X) ∩ U ∧
      W ∈ 𝓝ˢ[T \ interior X] J ∧ W ∩ X = J := by
  obtain ⟨K, hKfin, hK, hKconn, hKT⟩ := hT.exists_combinatorial_triangulation
  let _ : Finite K.faces := hKfin.to_subtype
  have hKU : U ∈ 𝓝ˢ[K.space] J := mem_nhdsSetWithin.mpr
    ⟨U, hU, hJU, inter_subset_left⟩
  obtain ⟨V, σ, -, hVK, hVU, hVnhds, hσ, hσ0⟩ :=
    hK.exists_bicollar_of_isPLSphere_one K (hK.isOrientable_euclidean_three K hKconn)
      hJ (hJT.trans hKT.symm.subset) hKU
  have hVT : V ⊆ T := hVK.trans hKT.subset
  rw [hKT] at hVnhds
  have hJV : J ⊆ V := fun y hy => by
    rw [← hσ0 y hy]
    exact hσ.bijOn.mapsTo ⟨hy, by norm_num⟩
  have hfront : V ∩ frontier X = J := Subset.antisymm
    (fun y hy => htrace ⟨⟨hVU hy.1, hVT hy.1⟩, hy.2⟩)
    (fun y hy => ⟨hJV hy, hJX hy⟩)
  obtain ⟨ψ⟩ := hT.2
  have hlocal : ∀ N ∈ 𝓝 x, ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
      (g : EuclideanSpace ℝ (Fin 2) → E3), 0 < r ∧ ContinuousOn g (Metric.ball c r) ∧
        InjOn g (Metric.ball c r) ∧ MapsTo g (Metric.ball c r) (T ∩ N) ∧ g c = x := by
    intro N hN
    exact exists_ball_chart_of_homeomorph_sphere_prod ψ (hJT hxJ)
      (mem_nhdsWithin_of_mem_nhds hN)
  obtain ⟨hinner, houter⟩ := hcross.mem_closure_sides hlocal hX hreg
  obtain ⟨O, hO, hJO, hOV⟩ := mem_nhdsSetWithin.mp hVnhds
  obtain ⟨a, haO, haT, haI⟩ := mem_closure_iff.mp hinner O hO (hJO hxJ)
  obtain ⟨b, hbO, hbT, hbX⟩ := mem_closure_iff.mp houter O hO (hJO hxJ)
  obtain ⟨ρ, hρ, hρ0⟩ := hσ.exists_half_collar_of_frontier hJ hσ0 hX hfront
    ⟨a, hOV ⟨haO, haT⟩, haI⟩ ⟨b, hOV ⟨hbO, hbT⟩, hbX⟩
  refine ⟨V \ interior X, ρ, hρ, hρ0,
    fun y hy => ⟨⟨hVT hy.1, hy.2⟩, hVU hy.1⟩, ?_, ?_⟩
  · apply mem_nhdsSetWithin.mpr
    exact ⟨O, hO, hJO, fun y hy => ⟨hOV ⟨hy.1, hy.2.1⟩, hy.2.2⟩⟩
  · refine Subset.antisymm ?_ ?_
    · rintro y ⟨⟨hyV, hyI⟩, hyX⟩
      exact hfront.subset ⟨hyV, hX.frontier_eq.symm ▸ ⟨hyX, hyI⟩⟩
    · intro y hy
      exact ⟨⟨hJV hy, (hJX hy).2⟩, hX.frontier_subset (hJX hy)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
