/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_openSimplex_eq_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) P) :
    f '' openSimplex (stdVertices n) = interior P := by
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  rw [hf.image_openSimplex_stdVertices, hf.image_stdSimplexBoundary_eq_frontier,
    hP.isPolyhedron.isCompact.isClosed.frontier_eq, sdiff_sdiff_cancel_left interior_subset]

theorem isConnected_interior_of_isPLBall {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hP : IsPLBall (n + 1) P) : IsConnected (interior P) :=
  hP.isConnected_interior_of_finrank (by simp)

theorem IsPLBall.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ interior P) :
    ∃ f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) P ∧ f (stdCenter n) = p := by
  obtain ⟨f, hf⟩ := hP
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  have hc0 : f (stdCenter n) ∈ interior P := by
    rw [← hf.image_openSimplex_eq_interior]
    exact mem_image_of_mem f (stdCenter_mem_openSimplex n)
  obtain ⟨h, hh, hfix, hhp⟩ := exists_isPLHomeomorphOn_map_point_eqOn_compl
    isOpen_interior (isConnected_interior_of_isPLBall hP).isPreconnected hc0 hp
  have hint : h '' interior P = interior P := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_contra hy
      have h2 : h x = x := h.injective (hfix hy)
      exact hy (by rw [h2]; exact hx)
    · intro y hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      by_contra hx
      have h1 := hfix hx
      rw [h.apply_symm_apply, id_eq] at h1
      exact hx (by rw [← h1]; exact hy)
  have hcl := hP.closure_interior
  have hPP : h '' P = P :=
    calc h '' P = h '' closure (interior P) := by rw [hcl]
      _ = closure (h '' interior P) := h.image_closure _
      _ = closure (interior P) := by rw [hint]
      _ = P := hcl
  have hhP : IsPLHomeomorphOn h P P := by
    have hres := hh.restrict hP.isPolyhedron (subset_univ P)
    rwa [hPP] at hres
  exact ⟨h ∘ f, hf.trans hhP, hhp⟩

theorem IsPLBall.exists_isPLHomeomorphOn_coneSet_of_mem_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ interior P) :
    ∃ f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn f
          (coneSet (stdCenter n)
            (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space) P ∧
        f (stdCenter n) = p := by
  obtain ⟨f, hf, hfc⟩ := hP.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq hp
  refine ⟨f, ?_, hfc⟩
  rwa [← coneComplex_space_eq_coneSet (isConeBase_std n), coneComplex_std_space]

theorem IsPLHomeomorphOn.exists_stdCenter_eq_of_mem_image_openSimplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} {P : Set E}
    {g : (Fin (m + 2) → ℝ) → E} (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) P)
    {x : E} (hx : x ∈ g '' openSimplex (stdVertices m)) :
    ∃ f : (Fin (m + 2) → ℝ) → E,
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) P ∧ f (stdCenter m) = x := by
  obtain ⟨T, hT, hTcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (E := EuclideanSpace ℝ (Fin (m + 1))) (n := m)
      (by simp) 0 Filter.univ_mem
  have hC : IsPLBall (m + 1) (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (m + 1))))) :=
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  obtain ⟨u, hu⟩ := id hC
  obtain ⟨y, hy, rfl⟩ := hx
  have hyS : y ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2)) := openSimplex_stdVertices_subset_stdSimplex hy
  have hz : u y ∈ interior (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (m + 1))))) := by
    rw [← hu.image_openSimplex_eq_interior]
    exact mem_image_of_mem u hy
  obtain ⟨f₀, hf₀, hf₀c⟩ := hC.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq hz
  refine ⟨g ∘ (Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) ∘ f₀),
    (hf₀.trans hu.symm).trans hg, ?_⟩
  change g (Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) (f₀ (stdCenter m))) = g y
  rw [hf₀c, hu.bijOn.invOn_invFunOn.1 hyS]

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_eq_boundaryComplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E] {m : ℕ}
    {P : Set E} {g : (Fin (m + 2) → ℝ) → E} (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) P)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : K.space = P) :
    g '' stdSimplexBoundary (m + 1) = (boundaryComplex (m + 1) K).space := by
  have hgK : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) K.space := hK.symm ▸ hg
  rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hgK, simplexBoundary_stdVertices_space]

theorem IsPLHomeomorphOn.image_openSimplex_eq_sdiff_boundaryComplex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E] {m : ℕ}
    {P : Set E} {g : (Fin (m + 2) → ℝ) → E} (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) P)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : K.space = P) :
    g '' openSimplex (stdVertices m) = P \ (boundaryComplex (m + 1) K).space := by
  rw [hg.image_openSimplex_stdVertices, hg.image_stdSimplexBoundary_eq_boundaryComplex K hK]

theorem IsPLBall.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq_of_notMem_boundaryComplex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E]
    {m : ℕ} {P : Set E} (hP : IsPLBall (m + 1) P)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : K.space = P) {x : E} (hx : x ∈ P \ (boundaryComplex (m + 1) K).space) :
    ∃ f : (Fin (m + 2) → ℝ) → E,
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin (m + 2))) P ∧ f (stdCenter m) = x := by
  obtain ⟨g, hg⟩ := hP
  refine hg.exists_stdCenter_eq_of_mem_image_openSimplex ?_
  rw [hg.image_openSimplex_eq_sdiff_boundaryComplex K hK]
  exact hx

end DifferentialGeometry.Topology.PiecewiseLinear
