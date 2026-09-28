/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusCompression
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_embedded_solid_torus_meridian :
    ∃ (N : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (C D : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      N.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 3 N ∧
      IsTopologicalSolidTorus N.space ∧
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ r '' stdSimplexBoundary 2 = C ∧
      IsPLSphere 1 C ∧ D ⊆ N.space ∧ frontier N.space ∩ D = C ∧
      D \ C ⊆ interior N.space ∧ (D \ frontier N.space).Nonempty ∧
      IsConnected (frontier N.space \ C) ∧
      Homology.bettiOne (frontier N.space) = 2 ∧
      ∃ (hCb : C ⊆ frontier N.space) (hCN : C ⊆ N.space),
        ¬ (⟨Set.inclusion hCb, continuous_inclusion hCb⟩ : C(C, frontier N.space)).Nullhomotopic ∧
        (⟨Set.inclusion hCN, continuous_inclusion hCN⟩ : C(C, N.space)).Nullhomotopic ∧
        ∃ (x : C) (p : Path x x),
          FundamentalGroup.map (⟨Set.inclusion hCb, continuous_inclusion hCb⟩ :
            C(C, frontier N.space)) x (Path.Homotopic.Quotient.mk p) ≠ 1 ∧
          FundamentalGroup.map (⟨Set.inclusion hCN, continuous_inclusion hCN⟩ :
            C(C, N.space)) x (Path.Homotopic.Quotient.mk p) = 1 := by
  obtain ⟨f, K, R, P, hKfin, hRfin, hPfin, hK, hKc, htorus, hKsp, hR, hRc, hRcl,
    hcover, htrace, hRbd, hW, hC, hWnhds, hn, hCc, hDmid, hDmeet, hr₀, hr₁, hdis,
    hKmeet₀, hKmeet₁, hmeet₀, hmeet₁, hbd₀, hbd₁, hP, hPsp, hβK, hβP, hlt, hregion⟩ :=
      exists_embedded_torus_compression_separating_points
  obtain ⟨N, q, z, hNfin, hN, hsolid, hf, hends, hKfront, hball, hPfront,
    -, -, -, -, -⟩ := hregion
  let C := f '' (stdSimplexBoundary 2 ×ˢ {(1 / 4 : ℝ)})
  let D := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 / 4 : ℝ)})
  let r := fun x => f (x, (1 / 4 : ℝ))
  have hboundary : r '' stdSimplexBoundary 2 = C := by
    dsimp [r, C]
    rw [prod_singleton, image_image]
  have hCD : C ⊆ D := image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)
  have hDN : D ⊆ N.space := by
    rw [← hf.image_eq]
    exact image_mono (fun _ hx => ⟨hx.1, hx.2.symm ▸ by norm_num⟩)
  have hDball : IsPLBall 2 D := ⟨r, hDmid⟩
  have hnull := hDball.nullhomotopic_inclusion hCD hDN
  rw [hKfront] at hDmeet hn hCc hβK
  obtain ⟨hCb, hnon⟩ := hn
  have hDint : D \ C ⊆ interior N.space := by
    intro y hy
    by_contra hnot
    exact hy.2 (hDmeet.subset ⟨⟨subset_closure (hDN hy.1), hnot⟩, hy.1⟩)
  obtain ⟨x, hxD, hxnot⟩ := hDmid.isConnected_sdiff_image_stdSimplexBoundary.nonempty
  have hxnotb : x ∉ frontier N.space := by
    intro hxb
    exact hxnot (hboundary.symm.subset (hDmeet.subset ⟨hxb, hxD⟩))
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hC
  let c : C := e 0
  let p : Path c c := circleToPath (⟨(e : C(loopCircle, C)), rfl⟩ : basedCircleLoop c)
  have hp : pathToCircle p = (e : C(loopCircle, C)) :=
    congrArg Subtype.val ((basedPathCircleHomeomorph c).apply_symm_apply
      (⟨(e : C(loopCircle, C)), rfl⟩ : basedCircleLoop c))
  let i : C(C, frontier N.space) := ⟨Set.inclusion hCb, continuous_inclusion hCb⟩
  have hnontrivial : FundamentalGroup.map i c (Path.Homotopic.Quotient.mk p) ≠ 1 := by
    intro h
    have hnul := (pathToCircle_nullhomotopic_iff (p.map i.continuous)).mpr
      (Path.Homotopic.Quotient.eq.mp h)
    rw [pathToCircle_natural, hp] at hnul
    have hback := hnul.comp_left (e.symm : C(C, loopCircle))
    apply hnon
    convert hback using 1
    apply ContinuousMap.ext
    intro y
    exact congrArg i (e.apply_symm_apply y).symm
  refine ⟨N, C, D, r, hNfin, hN, hsolid, hDmid, hboundary, hC, hDN, hDmeet, hDint,
    ⟨x, hxD, hxnotb⟩, hCc, hβK, hCb, hCD.trans hDN, hnon, hnull, c, p,
    hnontrivial, ?_⟩
  exact fundamentalGroup_map_eq_one_of_nullhomotopic _ hnull c _

end DifferentialGeometry.Topology.PiecewiseLinear
