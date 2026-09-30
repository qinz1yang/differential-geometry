/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCut
import DifferentialGeometry.Topology.PiecewiseLinear.RegionCellPush
import DifferentialGeometry.Topology.PiecewiseLinear.PLSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.ClosedBallImage
import DifferentialGeometry.Topology.Simplex.NormedBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.exists_pair_union_eq_inter_eq_of_boundary_trace
    {P D : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (htrace : D ∩ frontier P = g '' stdSimplexBoundary 2) :
    ∃ P₀ P₁ : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P₀ ∧ IsPLBall 3 P₁ ∧ P₀ ∪ P₁ = P ∧ P₀ ∩ P₁ = D ∧
        D ⊆ frontier P₀ ∧ D ⊆ frontier P₁ := by
  classical
  let T := {x : EuclideanSpace ℝ (Fin 3) |
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1}
  have hT : IsPLBall 3 T := isPLBall_triangle_prism
  have hTconv : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx₀, hx₁, hxsum, hx₂₀, hx₂₁⟩
    rcases hy with ⟨hy₀, hy₁, hysum, hy₂₀, hy₂₁⟩
    change 0 ≤ a * x 0 + b * y 0 ∧ 0 ≤ a * x 1 + b * y 1 ∧
      (a * x 0 + b * y 0) + (a * x 1 + b * y 1) ≤ 1 ∧
      0 ≤ a * x 2 + b * y 2 ∧ a * x 2 + b * y 2 ≤ 1
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith
  obtain ⟨p, hp⟩ := id hP
  obtain ⟨q, hq⟩ := id hT
  let u := q ∘ Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 4))
  have hu : IsPLHomeomorphOn u P T := hp.symm.trans hq
  let D' := u '' D
  let g' := u ∘ g
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hD'T : D' ⊆ T := by
    dsimp only [D']
    exact (image_mono hDP).trans hu.image_eq.subset
  have hg' : IsPLHomeomorphOn g' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' := by
    dsimp only [g', D']
    exact hg.trans (hu.restrict hD.isPolyhedron hDP)
  have hfront : u '' frontier P = frontier T := by
    have hup : EqOn (u ∘ p) q (stdSimplexBoundary 3) := by
      intro x hx
      dsimp only [u, Function.comp_apply]
      rw [hp.bijOn.invOn_invFunOn.1 hx.1]
    calc
      u '' frontier P = u '' (p '' stdSimplexBoundary 3) :=
        congrArg (fun S => u '' S) hp.image_stdSimplexBoundary_eq_frontier.symm
      _ = (u ∘ p) '' stdSimplexBoundary 3 := image_image u p _
      _ = q '' stdSimplexBoundary 3 := hup.image_eq
      _ = frontier T := hq.image_stdSimplexBoundary_eq_frontier
  have htrace' : D' ∩ frontier T = g' '' stdSimplexBoundary 2 := by
    calc
      D' ∩ frontier T = (u '' D) ∩ (u '' frontier P) := by
        dsimp only [D']
        rw [hfront]
      _ = u '' (D ∩ frontier P) :=
        (hu.bijOn.injOn.image_inter hDP hP.isPolyhedron.isClosed.frontier_subset).symm
      _ = u '' (g '' stdSimplexBoundary 2) := congrArg (fun S => u '' S) htrace
      _ = (u ∘ g) '' stdSimplexBoundary 2 := image_image u g _
      _ = g' '' stdSimplexBoundary 2 := rfl
  obtain ⟨D₀, D₁, hDunion, hDinter, ⟨f₀, f₁, hf₀, hf₁, hf₀J, hf₁J⟩,
      hS₀, hS₁, hSinter, -⟩ :=
    exists_isPLSphere_pair_of_spanning_disk hT.isPLSphere_frontier hg'
      ((inter_comm (frontier T) D').trans htrace')
  have hD₀ : IsPLBall 2 D₀ := ⟨f₀, hf₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨f₁, hf₁⟩
  have hD₀T : D₀ ⊆ frontier T := subset_union_left.trans hDunion.subset
  have hD₁T : D₁ ⊆ frontier T := subset_union_right.trans hDunion.subset
  obtain ⟨B₀, hB₀, hB₀front, -⟩ := hS₀.exists_isPLBall_frontier_eq
  obtain ⟨B₁, hB₁, hB₁front, -⟩ := hS₁.exists_isPLBall_frontier_eq
  have hTclosed : IsClosed T := hT.isPolyhedron.isClosed
  have hB₀closed : IsClosed B₀ := hB₀.isPolyhedron.isClosed
  have hB₁closed : IsClosed B₁ := hB₁.isPolyhedron.isClosed
  have hB₀T : B₀ ⊆ T :=
    DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_closed
      hB₀.isPolyhedron.isCompact hTconv hTclosed (by
        rw [hB₀front]
        exact union_subset (hD₀T.trans hTclosed.frontier_subset) hD'T)
  have hB₁T : B₁ ⊆ T :=
    DifferentialGeometry.Analysis.IsCompact.subset_of_frontier_subset_convex_closed
      hB₁.isPolyhedron.isCompact hTconv hTclosed (by
        rw [hB₁front]
        exact union_subset (hD₁T.trans hTclosed.frontier_subset) hD'T)
  have hD₀B₀ : D₀ ⊆ B₀ :=
    subset_union_left.trans hB₀front.symm.subset |>.trans hB₀closed.frontier_subset
  have hpatch : frontier T ∩ B₀ = D₀ := by
    apply Subset.antisymm
    · rintro x ⟨hxT, hxB⟩
      rcases hDunion.symm.subset hxT with hx₀ | hx₁
      · exact hx₀
      · by_cases hxf : x ∈ frontier B₀
        · rcases hB₀front.subset hxf with hx₀ | hxD
          · exact hx₀
          · exact (hDinter.symm.subset (htrace'.subset ⟨hxD, hxT⟩)).1
        · have hxi : x ∈ interior B₀ := (mem_interior_iff_notMem_frontier hxB).mpr hxf
          exact (hxT.2 (interior_mono hB₀T hxi)).elim
    · intro x hx₀
      exact ⟨hD₀T hx₀, hD₀B₀ hx₀⟩
  have houterDiff : frontier T \ B₀ = D₁ \ (g' '' stdSimplexBoundary 2) := by
    ext x
    constructor
    · rintro ⟨hxT, hxB⟩
      have hxnot₀ : x ∉ D₀ := fun hx₀ => hxB (hD₀B₀ hx₀)
      rcases hDunion.symm.subset hxT with hx₀ | hx₁
      · exact (hxnot₀ hx₀).elim
      · exact ⟨hx₁, fun hxJ => hxnot₀ (hDinter.symm.subset hxJ).1⟩
    · rintro ⟨hx₁, hxJ⟩
      refine ⟨hD₁T hx₁, ?_⟩
      intro hxB
      exact hxJ (hDinter.subset ⟨hpatch.subset ⟨hD₁T hx₁, hxB⟩, hx₁⟩)
  have hinnerDiff : frontier B₀ \ frontier T = D' \ (g' '' stdSimplexBoundary 2) := by
    ext x
    constructor
    · rintro ⟨hxf, hxT⟩
      rcases hB₀front.subset hxf with hx₀ | hxD
      · exact (hxT (hD₀T hx₀)).elim
      · exact ⟨hxD, fun hxJ => hxT (htrace'.symm.subset hxJ).2⟩
    · rintro ⟨hxD, hxJ⟩
      refine ⟨hB₀front.symm.subset (Or.inr hxD), ?_⟩
      intro hxT
      exact hxJ (htrace'.subset ⟨hxD, hxT⟩)
  have houterClosure : closure (frontier T \ B₀) = D₁ := by
    rw [houterDiff, ← hf₁J]
    exact hf₁.closure_sdiff_image_stdSimplexBoundary
  have hinnerClosure : closure (frontier B₀ \ frontier T) = D' := by
    rw [hinnerDiff]
    exact hg'.closure_sdiff_image_stdSimplexBoundary
  let C := closure (T \ B₀)
  have hCfront : frontier C = frontier B₁ := by
    calc
      frontier C = closure (frontier T \ B₀) ∪ closure (frontier B₀ \ frontier T) :=
        frontier_closure_sdiff_eq_of_isPLSphere_frontier hT.isPolyhedron hT.closure_interior
          hT.isPLSphere_frontier hB₀ hB₀T (by rwa [hpatch])
      _ = D₁ ∪ D' := by rw [houterClosure, hinnerClosure]
      _ = frontier B₁ := hB₁front.symm
  have hCT : C ⊆ T := by
    dsimp only [C]
    exact closure_minimal sdiff_subset hTclosed
  have hCcompact : IsCompact C := by
    exact hT.isPolyhedron.isCompact.of_isClosed_subset (by
      dsimp only [C]
      exact isClosed_closure) hCT
  have hCreg : closure (interior C) = C := by
    dsimp only [C]
    exact DifferentialGeometry.Topology.closure_interior_closure_sdiff
      hT.closure_interior hB₀closed
  have hB₁int : IsConnected (interior B₁) := isConnected_interior_of_isPLBall hB₁
  obtain ⟨b₁, hb₁⟩ := id hB₁
  let φ₁ : B₁ ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hb₁.homeomorph.symm.trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)
  have hB₁ext : IsConnected B₁ᶜ :=
    DifferentialGeometry.Topology.isConnected_compl_of_homeomorphClosedBall_of_isBicollared
      (by rw [← Module.finrank_eq_rank']; norm_num) φ₁ hB₁.isBicollared_frontier
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hD₁.nonempty
    have hxfB₁ : x ∈ frontier B₁ := hB₁front.symm.subset (Or.inl hx)
    have hxfC : x ∈ frontier C := hCfront.symm.subset hxfB₁
    have hCclosed : IsClosed C := by
      dsimp only [C]
      exact isClosed_closure
    exact ⟨x, hCclosed.frontier_subset hxfC⟩
  have hCB₁ : C = B₁ :=
    DifferentialGeometry.Topology.eq_of_isCompact_of_frontier_eq hCcompact
      hB₁.isPolyhedron.isCompact hCreg hB₁.closure_interior hB₁int.isPreconnected
      hB₁ext.isPreconnected hCne hCfront
  have hcover : B₀ ∪ B₁ = T := by
    apply Subset.antisymm (union_subset hB₀T hB₁T)
    intro x hxT
    by_cases hx₀ : x ∈ B₀
    · exact Or.inl hx₀
    · exact Or.inr (hCB₁.subset (subset_closure ⟨hxT, hx₀⟩))
  have hCavoid : C ⊆ (interior B₀)ᶜ := by
    dsimp only [C]
    apply closure_minimal
    · rintro x ⟨-, hx₀⟩ hxi
      exact hx₀ (interior_subset hxi)
    · exact isOpen_interior.isClosed_compl
  have hB₁intAvoid : interior B₁ ⊆ B₀ᶜ := by
    rw [← hCB₁]
    exact DifferentialGeometry.Topology.interior_closure_sdiff_subset_compl
      hB₀.closure_interior
  have hinter : B₀ ∩ B₁ = D' := by
    apply Subset.antisymm
    · rintro x ⟨hx₀, hx₁⟩
      have hxf₀ : x ∈ frontier B₀ := by
        by_contra h
        have hxi : x ∈ interior B₀ := (mem_interior_iff_notMem_frontier hx₀).mpr h
        exact (hCavoid (hCB₁.symm.subset hx₁)) hxi
      have hxf₁ : x ∈ frontier B₁ := by
        by_contra h
        have hxi : x ∈ interior B₁ := (mem_interior_iff_notMem_frontier hx₁).mpr h
        exact (hB₁intAvoid hxi) hx₀
      exact hSinter.subset ⟨hB₀front.subset hxf₀, hB₁front.subset hxf₁⟩
    · intro x hxD
      exact ⟨hB₀closed.frontier_subset (hB₀front.symm.subset (Or.inr hxD)),
        hB₁closed.frontier_subset (hB₁front.symm.subset (Or.inr hxD))⟩
  let v := Function.invFunOn u P
  have hv : IsPLHomeomorphOn v T P := hu.symm
  let C₀ := v '' B₀
  let C₁ := v '' B₁
  have hv₀ : IsPLHomeomorphOn v B₀ C₀ := by
    dsimp only [C₀]
    exact hv.restrict hB₀.isPolyhedron hB₀T
  have hv₁ : IsPLHomeomorphOn v B₁ C₁ := by
    dsimp only [C₁]
    exact hv.restrict hB₁.isPolyhedron hB₁T
  have hC₀ : IsPLBall 3 C₀ := hB₀.of_isPLHomeomorphOn hv₀
  have hC₁ : IsPLBall 3 C₁ := hB₁.of_isPLHomeomorphOn hv₁
  have hbackD : v '' D' = D := by
    dsimp only [v, D']
    rw [image_image]
    have hinv : EqOn (Function.invFunOn u P ∘ u) id D := fun x hx =>
      hu.bijOn.invOn_invFunOn.1 (hDP hx)
    exact hinv.image_eq.trans (image_id D)
  have hCcover : C₀ ∪ C₁ = P := by
    dsimp only [C₀, C₁]
    rw [← image_union, hcover]
    exact hv.image_eq
  have hCinter : C₀ ∩ C₁ = D := by
    dsimp only [C₀, C₁]
    rw [← hv.bijOn.injOn.image_inter hB₀T hB₁T, hinter, hbackD]
  obtain ⟨b₀, hb₀⟩ := id hB₀
  have hc₀ : IsPLHomeomorphOn (v ∘ b₀) (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) C₀ := hb₀.trans hv₀
  have hc₁ : IsPLHomeomorphOn (v ∘ b₁) (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) C₁ := hb₁.trans hv₁
  have hDC₀ : D ⊆ frontier C₀ := by
    rw [← hc₀.image_stdSimplexBoundary_eq_frontier]
    calc
      D = v '' D' := hbackD.symm
      _ ⊆ v '' frontier B₀ :=
        image_mono (fun _ hx => hB₀front.symm.subset (Or.inr hx))
      _ = v '' (b₀ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₀.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₀) '' stdSimplexBoundary 3 := image_image v b₀ _
  have hDC₁ : D ⊆ frontier C₁ := by
    rw [← hc₁.image_stdSimplexBoundary_eq_frontier]
    calc
      D = v '' D' := hbackD.symm
      _ ⊆ v '' frontier B₁ :=
        image_mono (fun _ hx => hB₁front.symm.subset (Or.inr hx))
      _ = v '' (b₁ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₁.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₁) '' stdSimplexBoundary 3 := image_image v b₁ _
  exact ⟨C₀, C₁, hC₀, hC₁, hCcover, hCinter, hDC₀, hDC₁⟩

private theorem IsPLBall.exists_pair_union_eq_inter_eq_with_boundary_of_boundary_trace
    {P D : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPLBall 3 P)
    {g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (htrace : D ∩ frontier P = g '' stdSimplexBoundary 2) :
    ∃ P₀ P₁ : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 P₀ ∧ IsPLBall 3 P₁ ∧ P₀ ∪ P₁ = P ∧ P₀ ∩ P₁ = D ∧
        D ⊆ frontier P₀ ∧ D ⊆ frontier P₁ ∧
        P₀ ∩ frontier P ⊆ frontier P₀ ∧ P₁ ∩ frontier P ⊆ frontier P₁ ∧
        frontier P₀ = D ∪ (P₀ ∩ frontier P) ∧
        frontier P₁ = D ∪ (P₁ ∩ frontier P) := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hcover, hinter, hD₀, hD₁⟩ :=
    hP.exists_pair_union_eq_inter_eq_of_boundary_trace hg hDP htrace
  have hP₀P : P₀ ⊆ P := subset_union_left.trans hcover.subset
  have hP₁P : P₁ ⊆ P := subset_union_right.trans hcover.subset
  have houter₀ : P₀ ∩ frontier P ⊆ frontier P₀ := by
    intro x hx
    rw [hP₀.isPolyhedron.isClosed.frontier_eq]
    refine ⟨hx.1, fun hxi => ?_⟩
    rw [hP.isPolyhedron.isClosed.frontier_eq] at hx
    exact hx.2.2 (interior_mono hP₀P hxi)
  have houter₁ : P₁ ∩ frontier P ⊆ frontier P₁ := by
    intro x hx
    rw [hP₁.isPolyhedron.isClosed.frontier_eq]
    refine ⟨hx.1, fun hxi => ?_⟩
    rw [hP.isPolyhedron.isClosed.frontier_eq] at hx
    exact hx.2.2 (interior_mono hP₁P hxi)
  have hfrontier₀ : frontier P₀ = D ∪ (P₀ ∩ frontier P) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxP₁ : x ∈ P₁
      · exact Or.inl (hinter.subset ⟨hP₀.isPolyhedron.isClosed.frontier_subset hx, hxP₁⟩)
      · right
        refine ⟨hP₀.isPolyhedron.isClosed.frontier_subset hx, ?_⟩
        refine ⟨?_, ?_⟩
        · exact hcover ▸ subset_closure (Or.inl (hP₀.isPolyhedron.isClosed.frontier_subset hx))
        · intro hxIntP
          have hxOpen : P₁ᶜ ∩ interior P ∈ 𝓝 x :=
            (hP₁.isPolyhedron.isClosed.isOpen_compl.inter isOpen_interior).mem_nhds
              ⟨hxP₁, hxIntP⟩
          have hsub : P₁ᶜ ∩ interior P ⊆ P₀ := by
            intro y hy
            exact (hcover.symm.subset (interior_subset hy.2)).resolve_right hy.1
          exact (mem_frontier_iff_notMem_interior
            (hP₀.isPolyhedron.isClosed.frontier_subset hx)).mp hx
              (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hxOpen hsub))
    · exact union_subset hD₀ houter₀
  have hfrontier₁ : frontier P₁ = D ∪ (P₁ ∩ frontier P) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxP₀ : x ∈ P₀
      · exact Or.inl (hinter.subset ⟨hxP₀, hP₁.isPolyhedron.isClosed.frontier_subset hx⟩)
      · right
        refine ⟨hP₁.isPolyhedron.isClosed.frontier_subset hx, ?_⟩
        refine ⟨?_, ?_⟩
        · exact hcover ▸ subset_closure (Or.inr (hP₁.isPolyhedron.isClosed.frontier_subset hx))
        · intro hxIntP
          have hxOpen : P₀ᶜ ∩ interior P ∈ 𝓝 x :=
            (hP₀.isPolyhedron.isClosed.isOpen_compl.inter isOpen_interior).mem_nhds
              ⟨hxP₀, hxIntP⟩
          have hsub : P₀ᶜ ∩ interior P ⊆ P₁ := by
            intro y hy
            exact (hcover.symm.subset (interior_subset hy.2)).resolve_left hy.1
          exact (mem_frontier_iff_notMem_interior
            (hP₁.isPolyhedron.isClosed.frontier_subset hx)).mp hx
              (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hxOpen hsub))
    · exact union_subset hD₁ houter₁
  exact ⟨P₀, P₁, hP₀, hP₁, hcover, hinter, hD₀, hD₁, houter₀, houter₁,
    hfrontier₀, hfrontier₁⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsPLBall.exists_complex_pair_union_eq_inter_eq_with_boundary_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ K₀ K₁ : Geometry.SimplicialComplex ℝ E,
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
        K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
          D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space ∧
          K₀.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₀).space ∧
          K₁.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₁).space ∧
          (boundaryComplex 3 K₀).space =
            D ∪ (K₀.space ∩ (boundaryComplex 3 K).space) ∧
          (boundaryComplex 3 K₁).space =
            D ∪ (K₁.space ∩ (boundaryComplex 3 K).space) := by
  let _ : DecidableEq E := Classical.decEq E
  let T := {x : EuclideanSpace ℝ (Fin 3) |
    0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 ∧ 0 ≤ x 2 ∧ x 2 ≤ 1}
  have hT : IsPLBall 3 T := isPLBall_triangle_prism
  obtain ⟨p, hp⟩ := id hK
  obtain ⟨q, hq⟩ := id hT
  let u := q ∘ Function.invFunOn p (Convexity.StdSimplex.coordinateSet ℝ (Fin 4))
  have hu : IsPLHomeomorphOn u K.space T := hp.symm.trans hq
  let D' := u '' D
  let g' := u ∘ g
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hD'T : D' ⊆ T := by
    dsimp only [D']
    exact (image_mono hDK).trans hu.image_eq.subset
  have hg' : IsPLHomeomorphOn g' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D' := by
    dsimp only [g', D']
    exact hg.trans (hu.restrict hD.isPolyhedron hDK)
  have hfront : u '' (boundaryComplex 3 K).space = frontier T := by
    have hup : EqOn (u ∘ p) q (stdSimplexBoundary 3) := by
      intro x hx
      dsimp only [u, Function.comp_apply]
      rw [hp.bijOn.invOn_invFunOn.1 hx.1]
    calc
      u '' (boundaryComplex 3 K).space = u '' (p '' stdSimplexBoundary 3) :=
        congrArg (fun S => u '' S) (hp.image_stdSimplexBoundary_eq_boundaryComplex K rfl).symm
      _ = (u ∘ p) '' stdSimplexBoundary 3 := image_image u p _
      _ = q '' stdSimplexBoundary 3 := hup.image_eq
      _ = frontier T := hq.image_stdSimplexBoundary_eq_frontier
  have htrace' : D' ∩ frontier T = g' '' stdSimplexBoundary 2 := by
    calc
      D' ∩ frontier T = (u '' D) ∩ (u '' (boundaryComplex 3 K).space) := by
        dsimp only [D']
        rw [hfront]
      _ = u '' (D ∩ (boundaryComplex 3 K).space) :=
        (hu.bijOn.injOn.image_inter hDK (boundaryComplex_space_subset 3 K)).symm
      _ = u '' (g '' stdSimplexBoundary 2) := congrArg (fun S => u '' S) htrace
      _ = (u ∘ g) '' stdSimplexBoundary 2 := image_image u g _
      _ = g' '' stdSimplexBoundary 2 := rfl
  obtain ⟨B₀, B₁, hB₀, hB₁, hcover, hinter, hDB₀, hDB₁, houter₀, houter₁,
      hfrontier₀, hfrontier₁⟩ :=
    hT.exists_pair_union_eq_inter_eq_with_boundary_of_boundary_trace hg' hD'T htrace'
  have hB₀T : B₀ ⊆ T := subset_union_left.trans hcover.subset
  have hB₁T : B₁ ⊆ T := subset_union_right.trans hcover.subset
  let v := Function.invFunOn u K.space
  have hv : IsPLHomeomorphOn v T K.space := hu.symm
  let P₀ := v '' B₀
  let P₁ := v '' B₁
  have hv₀ : IsPLHomeomorphOn v B₀ P₀ := by
    dsimp only [P₀]
    exact hv.restrict hB₀.isPolyhedron hB₀T
  have hv₁ : IsPLHomeomorphOn v B₁ P₁ := by
    dsimp only [P₁]
    exact hv.restrict hB₁.isPolyhedron hB₁T
  have hP₀ : IsPLBall 3 P₀ := hB₀.of_isPLHomeomorphOn hv₀
  have hP₁ : IsPLBall 3 P₁ := hB₁.of_isPLHomeomorphOn hv₁
  have hbackD : v '' D' = D := by
    dsimp only [v, D']
    rw [image_image]
    have hinv : EqOn (Function.invFunOn u K.space ∘ u) id D := fun x hx =>
      hu.bijOn.invOn_invFunOn.1 (hDK hx)
    exact hinv.image_eq.trans (image_id D)
  have hPcover : P₀ ∪ P₁ = K.space := by
    dsimp only [P₀, P₁]
    rw [← image_union, hcover]
    exact hv.image_eq
  have hPinter : P₀ ∩ P₁ = D := by
    dsimp only [P₀, P₁]
    rw [← hv.bijOn.injOn.image_inter hB₀T hB₁T, hinter, hbackD]
  obtain ⟨b₀, hb₀⟩ := id hB₀
  obtain ⟨b₁, hb₁⟩ := id hB₁
  have hp₀ : IsPLHomeomorphOn (v ∘ b₀) (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) P₀ := hb₀.trans hv₀
  have hp₁ : IsPLHomeomorphOn (v ∘ b₁) (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) P₁ := hb₁.trans hv₁
  obtain ⟨K₀, hK₀fin, hK₀space⟩ := hP₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨K₁, hK₁fin, hK₁space⟩ := hP₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite K₀.faces := hK₀fin.to_subtype
  let _ : Finite K₁.faces := hK₁fin.to_subtype
  have hDbd₀ : D ⊆ (boundaryComplex 3 K₀).space := by
    rw [← hp₀.image_stdSimplexBoundary_eq_boundaryComplex K₀ hK₀space]
    calc
      D = v '' D' := hbackD.symm
      _ ⊆ v '' frontier B₀ := image_mono hDB₀
      _ = v '' (b₀ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₀.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₀) '' stdSimplexBoundary 3 := image_image v b₀ _
  have hDbd₁ : D ⊆ (boundaryComplex 3 K₁).space := by
    rw [← hp₁.image_stdSimplexBoundary_eq_boundaryComplex K₁ hK₁space]
    calc
      D = v '' D' := hbackD.symm
      _ ⊆ v '' frontier B₁ := image_mono hDB₁
      _ = v '' (b₁ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₁.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₁) '' stdSimplexBoundary 3 := image_image v b₁ _
  have hbackBoundary : v '' frontier T = (boundaryComplex 3 K).space := by
    calc
      v '' frontier T = v '' (u '' (boundaryComplex 3 K).space) :=
        congrArg (fun S => v '' S) hfront.symm
      _ = (v ∘ u) '' (boundaryComplex 3 K).space := image_image v u _
      _ = id '' (boundaryComplex 3 K).space := by
        apply EqOn.image_eq
        intro x hx
        exact hu.bijOn.invOn_invFunOn.1 (boundaryComplex_space_subset 3 K hx)
      _ = (boundaryComplex 3 K).space := image_id _
  have hbackBoundary₀ : v '' frontier B₀ = (boundaryComplex 3 K₀).space := by
    calc
      v '' frontier B₀ = v '' (b₀ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₀.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₀) '' stdSimplexBoundary 3 := image_image v b₀ _
      _ = (boundaryComplex 3 K₀).space :=
        hp₀.image_stdSimplexBoundary_eq_boundaryComplex K₀ hK₀space
  have hbackBoundary₁ : v '' frontier B₁ = (boundaryComplex 3 K₁).space := by
    calc
      v '' frontier B₁ = v '' (b₁ '' stdSimplexBoundary 3) :=
        congrArg (fun S => v '' S) hb₁.image_stdSimplexBoundary_eq_frontier.symm
      _ = (v ∘ b₁) '' stdSimplexBoundary 3 := image_image v b₁ _
      _ = (boundaryComplex 3 K₁).space :=
        hp₁.image_stdSimplexBoundary_eq_boundaryComplex K₁ hK₁space
  have houterK₀ : K₀.space ∩ (boundaryComplex 3 K).space ⊆
      (boundaryComplex 3 K₀).space := by
    rw [hK₀space, ← hbackBoundary, ← hbackBoundary₀,
      ← hv.bijOn.injOn.image_inter hB₀T hT.isPolyhedron.isClosed.frontier_subset]
    exact image_mono houter₀
  have houterK₁ : K₁.space ∩ (boundaryComplex 3 K).space ⊆
      (boundaryComplex 3 K₁).space := by
    rw [hK₁space, ← hbackBoundary, ← hbackBoundary₁,
      ← hv.bijOn.injOn.image_inter hB₁T hT.isPolyhedron.isClosed.frontier_subset]
    exact image_mono houter₁
  have hboundaryK₀ : (boundaryComplex 3 K₀).space =
      D ∪ (K₀.space ∩ (boundaryComplex 3 K).space) := by
    calc
      (boundaryComplex 3 K₀).space = v '' frontier B₀ := hbackBoundary₀.symm
      _ = v '' (D' ∪ (B₀ ∩ frontier T)) := congrArg (fun S => v '' S) hfrontier₀
      _ = v '' D' ∪ v '' (B₀ ∩ frontier T) := image_union _ _ _
      _ = D ∪ (v '' B₀ ∩ v '' frontier T) := by
        rw [hbackD, hv.bijOn.injOn.image_inter hB₀T
          hT.isPolyhedron.isClosed.frontier_subset]
      _ = D ∪ (K₀.space ∩ (boundaryComplex 3 K).space) := by
        rw [hK₀space, hbackBoundary]
  have hboundaryK₁ : (boundaryComplex 3 K₁).space =
      D ∪ (K₁.space ∩ (boundaryComplex 3 K).space) := by
    calc
      (boundaryComplex 3 K₁).space = v '' frontier B₁ := hbackBoundary₁.symm
      _ = v '' (D' ∪ (B₁ ∩ frontier T)) := congrArg (fun S => v '' S) hfrontier₁
      _ = v '' D' ∪ v '' (B₁ ∩ frontier T) := image_union _ _ _
      _ = D ∪ (v '' B₁ ∩ v '' frontier T) := by
        rw [hbackD, hv.bijOn.injOn.image_inter hB₁T
          hT.isPolyhedron.isClosed.frontier_subset]
      _ = D ∪ (K₁.space ∩ (boundaryComplex 3 K).space) := by
        rw [hK₁space, hbackBoundary]
  refine ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀space.symm ▸ hP₀, hK₁space.symm ▸ hP₁,
    ?_, ?_, hDbd₀, hDbd₁, houterK₀, houterK₁, hboundaryK₀, hboundaryK₁⟩
  · rwa [hK₀space, hK₁space]
  · rwa [hK₀space, hK₁space]

open Classical in
theorem IsPLBall.exists_complex_pair_union_eq_inter_eq_with_outer_boundary_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ K₀ K₁ : Geometry.SimplicialComplex ℝ E,
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
        K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
          D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space ∧
          K₀.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₀).space ∧
          K₁.space ∩ (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 K₁).space := by
  obtain ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
      houter₀, houter₁, -, -⟩ :=
    hK.exists_complex_pair_union_eq_inter_eq_with_boundary_of_boundary_trace K hg hDK htrace
  exact ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁,
    houter₀, houter₁⟩

open Classical in
theorem IsPLBall.exists_complex_pair_union_eq_inter_eq_of_boundary_trace
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    {D : Set E} {g : (Fin 3 → ℝ) → E}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (htrace : D ∩ (boundaryComplex 3 K).space = g '' stdSimplexBoundary 2) :
    ∃ K₀ K₁ : Geometry.SimplicialComplex ℝ E,
      K₀.faces.Finite ∧ K₁.faces.Finite ∧ IsPLBall 3 K₀.space ∧ IsPLBall 3 K₁.space ∧
        K₀.space ∪ K₁.space = K.space ∧ K₀.space ∩ K₁.space = D ∧
          D ⊆ (boundaryComplex 3 K₀).space ∧ D ⊆ (boundaryComplex 3 K₁).space := by
  obtain ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁, -, -⟩ :=
    hK.exists_complex_pair_union_eq_inter_eq_with_outer_boundary_of_boundary_trace
      K hg hDK htrace
  exact ⟨K₀, K₁, hK₀fin, hK₁fin, hK₀, hK₁, hcover, hinter, hD₀, hD₁⟩

end DifferentialGeometry.Topology.PiecewiseLinear
