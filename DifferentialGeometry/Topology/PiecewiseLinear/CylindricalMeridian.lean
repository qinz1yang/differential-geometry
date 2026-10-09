/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem IsCylindricalDiagram.exists_essential_slice_disk
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ (boundaryComplex 2 D).space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let C := f '' ((boundaryComplex 2 D).space ×ˢ {t})
    let B := f '' (D.space ×ˢ {t})
    ∃ r : (Fin 3 → ℝ) → F,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B ∧ r '' stdSimplexBoundary 2 = C ∧
      IsPLSphere 1 C ∧ B ⊆ M.space ∧ frontier M.space ∩ B = C ∧
      (B \ C).Nonempty ∧ B \ C ⊆ interior M.space ∧ IsConnected (frontier M.space \ C) ∧
      ∃ (hCf : C ⊆ frontier M.space) (hCM : C ⊆ M.space),
        ¬ (⟨Set.inclusion hCf, continuous_inclusion hCf⟩ : C(C, frontier M.space)).Nullhomotopic ∧
        (⟨Set.inclusion hCM, continuous_inclusion hCM⟩ : C(C, M.space)).Nullhomotopic := by
  let J := (boundaryComplex 2 D).space
  let C := f '' (J ×ˢ {t})
  let B := f '' (D.space ×ˢ {t})
  have hJ : IsPLSphere 1 J := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hJD : J ⊆ D.space := boundaryComplex_space_subset 2 D
  have hfront := hf.frontier_eq_image_side D M hD hM hdim
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  have hcore := hside.isPLHomeomorphOn_slice hJ.isPolyhedron ht
  have hslice := hf.isPLHomeomorphOn_slice hD.isPolyhedron ht
  have hD' := hD
  obtain ⟨p, hp⟩ := hD'
  have hcap : IsPLHomeomorphOn (fun x => f (p x, t)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B :=
    hp.trans hslice
  have hJp : p '' stdSimplexBoundary 2 = J := by
    rw [show J = (boundaryComplex 2 D).space from rfl,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D hp,
      simplexBoundary_stdVertices_space]
  have hbd : (fun x => f (p x, t)) '' stdSimplexBoundary 2 = C := by
    dsimp [C]
    rw [prod_singleton, ← hJp, image_image, image_image]
  have hBsub : B ⊆ M.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ht⟩)
  have hCD : C ⊆ B := image_mono (prod_mono hJD Subset.rfl)
  have hCf : C ⊆ frontier M.space := by
    rw [hfront]
    exact image_mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ ht⟩)
  have hmeet : frontier M.space ∩ B = C := by
    rw [hfront]
    exact hf.image_subcylinder_inter_slice hJD hside.image_top_eq_bottom ht
  have hBint : B \ C ⊆ interior M.space := by
    intro x hx
    by_contra hnot
    exact hx.2 (hmeet.subset ⟨⟨subset_closure (hBsub hx.1), hnot⟩, hx.1⟩)
  have hconn : IsConnected (frontier M.space \ C) := by
    rw [hfront]
    exact hside.isConnected_sdiff_slice hJ.isConnected ht
  have hnon : ¬ (⟨Set.inclusion hCf, continuous_inclusion hCf⟩ :
      C(C, frontier M.space)).Nullhomotopic := by
    intro hn
    let w : C(frontier M.space, f '' (J ×ˢ Icc (0 : ℝ) 1)) := Homeomorph.setCongr hfront
    have hn' := (hn.comp_left (hcore.homeomorph : C(J, C))).comp_right w
    apply hside.not_nullhomotopic_slice hJ hends ht
    convert hn' using 1
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hnull := (hD.of_isPLHomeomorphOn hslice).nullhomotopic_inclusion hCD hBsub
  obtain ⟨x, hxB, hxnot⟩ := hcap.isConnected_sdiff_image_stdSimplexBoundary.nonempty
  exact ⟨_, hcap, hbd, hJ.of_isPLHomeomorphOn hcore, hBsub, hmeet,
    ⟨x, hxB, fun hxC => hxnot (hbd.symm.subset hxC)⟩,
    hBint, hconn, hCf, hCD.trans hBsub, hnon, hnull⟩

end DifferentialGeometry.Topology.PiecewiseLinear
