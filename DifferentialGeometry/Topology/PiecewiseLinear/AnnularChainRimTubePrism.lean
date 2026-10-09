/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimPrism
import DifferentialGeometry.Topology.PiecewiseLinear.TubeCenteredPrismCoordinates

open Set Topology
open DifferentialGeometry.Simplex

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Triangle" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "Interval" => Icc (-1 : ℝ) 1

theorem IsTube.exists_centered_product_homeomorph
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ e : (Triangle × Interval) ≃ₜ ↥(h '' C u ∪ h '' C v),
      range (fun p : Triangle => (e (p, ⟨0, by norm_num⟩) : E3)) = h '' D {u, v} ∧
      range (fun b : boundary (Fin 3) => (e (b.val, ⟨0, by norm_num⟩) : E3)) =
        h '' Dbd {u, v} ∧
      (e (Convexity.StdSimplex.coordinateBarycenter, ⟨0, by norm_num⟩) : E3) =
        h (({u, v} : Finset E3).centroid ℝ id) := by
  obtain ⟨ρ, hρ, hρP, hρD, hρR, -, -⟩ := ht.exists_centered_prism_coordinates hu hv huv he
  let e₀ := (Homeomorph.Set.prod (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Icc (-1 : ℝ) 1)).symm.trans
    hρ.homeomorph
  let e₁ := (ht.isEmbedding_dualBall_pair hu hv).toHomeomorph.trans
    (Homeomorph.setCongr ((Set.range_domRestrict h (C u ∪ C v)).trans (image_union h _ _)))
  let e := e₀.trans e₁
  have heval (p : Triangle) (t : Interval) :
      (e (p, t) : E3) = h (ρ (p.val, t.val)) := rfl
  refine ⟨e, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      change h (ρ (p.val, 0)) ∈ h '' D {u, v}
      exact ⟨ρ (p.val, 0), hρD ▸ mem_image_of_mem ρ ⟨p.property, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨⟨p, t⟩, ⟨hp, ht⟩, hpt⟩ := hρD.symm.subset hy
      change t = 0 at ht
      subst t
      refine ⟨⟨p, hp⟩, ?_⟩
      exact (heval _ _).trans (congrArg h hpt)
  · ext x
    constructor
    · rintro ⟨b, rfl⟩
      change h (ρ (b.val.val, 0)) ∈ h '' Dbd {u, v}
      exact ⟨ρ (b.val.val, 0), hρR ▸ mem_image_of_mem ρ ⟨⟨b.val.property, b.property⟩, rfl⟩,
        rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨⟨p, t⟩, ⟨hp, ht⟩, hpt⟩ := hρR.symm.subset hy
      change t = 0 at ht
      subst t
      refine ⟨⟨⟨p, hp.1⟩, hp.2⟩, ?_⟩
      exact (heval _ _).trans (congrArg h hpt)
  · rw [heval]
    have hb : (Convexity.StdSimplex.coordinateBarycenter : Triangle).val = stdCenter 1 := by
      ext i
      norm_num [Convexity.StdSimplex.coordinateBarycenter, stdCenter]
    change h (ρ ((Convexity.StdSimplex.coordinateBarycenter : Triangle).val, 0)) = _
    rw [hb, hρP]

end DifferentialGeometry.Topology.PiecewiseLinear
