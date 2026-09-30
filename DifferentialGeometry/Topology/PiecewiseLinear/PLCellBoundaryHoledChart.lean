/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.HoledSphereExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace E3 M]

theorem IsPLCellOn.exists_planar_chart_boundary_complement
    {S B : Set M} (hS : IsPLCellOn 3 S B)
    {ι : Type*} (D J : ι → Set M)
    (hD : ∀ i, IsPLCellOn 2 (D i) (J i))
    (hDB : ∀ i, D i ⊆ B)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (i₀ : ι) :
    ∃ (P : Set E3) (u : E3 → M) (χ : E3 → Plane) (Δ : Set Plane),
      IsPLBall 3 P ∧ IsPLHomeomorphInto 3 u P ∧
      S = u '' P ∧ B = u '' frontier P ∧ IsPLBall 2 Δ ∧
      IsPLHomeomorphOn χ
        (frontier P \ (Function.invFunOn u P '' D i₀ \
          Function.invFunOn u P '' J i₀)) Δ ∧
      χ '' (Function.invFunOn u P '' J i₀) = frontier Δ ∧
      ∀ i, i ≠ i₀ →
        χ '' (Function.invFunOn u P '' D i) ⊆ interior Δ ∧
        IsPLHomeomorphOn χ (Function.invFunOn u P '' D i)
          (χ '' (Function.invFunOn u P '' D i)) ∧
        χ '' (Function.invFunOn u P '' J i) =
          frontier (χ '' (Function.invFunOn u P '' D i)) := by
  classical
  obtain ⟨P, r, u, hr, hu, hSdef, hBdef⟩ := hS
  have hP : IsPLBall 3 P := ⟨r, hr⟩
  have hB : B = u '' frontier P := by
    rw [hBdef, hr.image_stdSimplexBoundary_eq_frontier]
  have hfrontP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hDQ (i : ι) : D i ⊆ u '' P :=
    (hDB i).trans (hB ▸ image_mono hfrontP)
  have hqExists (i : ι) :
      ∃ q : (Fin 3 → ℝ) → E3,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
          (Function.invFunOn u P '' D i) ∧
        Function.invFunOn u P '' J i = q '' stdSimplexBoundary 2 :=
    (hD i).exists_isPLHomeomorphOn_invFunOn hu (hDQ i)
  choose q hq hqJ using hqExists
  have hDS (i : ι) : Function.invFunOn u P '' D i ⊆ frontier P := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ : x ∈ u '' frontier P := hB ▸ hDB i hx
    rw [hu.injOn.leftInvOn_invFunOn (hfrontP hz)]
    exact hz
  have hdis' : Pairwise fun i j =>
      Disjoint (Function.invFunOn u P '' D i) (Function.invFunOn u P '' D j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hx' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hDQ i hx)
    have hy' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hDQ j hy)
    have hxy : x = y := by
      rw [← hx', ← hy', hyx]
    exact disjoint_left.mp (hdis hij) hx (hxy ▸ hy)
  obtain ⟨χ, Δ, hΔ, hχ, hχ₀, hχi⟩ :=
    hP.isPLSphere_frontier.exists_holed_chart hq hDS hdis' i₀
  refine ⟨P, u, χ, Δ, hP, hu, hSdef, hB, hΔ, ?_, ?_, ?_⟩
  · simpa only [← hqJ i₀] using hχ
  · simpa only [← hqJ i₀] using hχ₀
  · intro i hi
    obtain ⟨-, hinside, hpl, hrim⟩ := hχi i hi
    exact ⟨hinside, hpl, by simpa only [← hqJ i] using hrim⟩

end DifferentialGeometry.Topology.PiecewiseLinear
