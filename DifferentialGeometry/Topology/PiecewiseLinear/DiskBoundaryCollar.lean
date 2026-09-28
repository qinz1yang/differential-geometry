/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollarGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskBoundary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_isPLHomeomorphOn_union_collar
    {D W : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc a b) W)
    (hfix : ∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, a) = x)
    (hmeet : W ∩ D = r '' stdSimplexBoundary 2) :
    ∃ q : (Fin 3 → ℝ) → E, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D ∪ W) ∧
      q '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {b}) ∧
      Disjoint D (q '' stdSimplexBoundary 2) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  let J := r '' stdSimplexBoundary 2
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hJD : J ⊆ D := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  obtain ⟨K, hKfin, hKspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hD
  have hrK : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) K.space := hKspace.symm ▸ hr
  have hboundary : (boundaryComplex 2 K).space = J := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hrK,
      simplexBoundary_stdVertices_space]
  have hJ : IsPLSphere 1 J := hboundary ▸ isPLSphere_boundaryComplex_space_of_isPLBall K hK
  have hmodel : IsPLBall 2 (D ×ˢ {a} ∪ J ×ˢ Icc a b) := by
    have h := isPLBall_prism_bottom_union_side K hK hab
    rwa [hKspace, hboundary] at h
  obtain ⟨g, hg, _, hgs⟩ := exists_isPLHomeomorphOn_bottom_union_collar_sides
    hJ.isPolyhedron hD.isPolyhedron Subset.rfl hab hρ hfix hmeet
  rw [inter_eq_right.mpr hJD, hρ.image_eq] at hg
  rw [inter_eq_right.mpr hJD] at hgs
  obtain ⟨p, hp⟩ := hmodel
  have hpB := hr.image_stdSimplexBoundary_prism_bottom_union_side hab hp
  have htop : J ×ˢ {b} ⊆ J ×ˢ Icc a b := by
    intro z hz
    exact ⟨hz.1, hz.2.symm ▸ ⟨hab.le, le_rfl⟩⟩
  have hqB : (g ∘ p) '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {b}) := by
    rw [image_comp, hpB]
    exact (hgs.mono htop).image_eq
  refine ⟨g ∘ p, hp.trans hg, hqB, ?_⟩
  rw [hqB]
  apply disjoint_left.mpr
  rintro y hyD ⟨z, hz, hzy⟩
  have hyJ : y ∈ J := hmeet.subset ⟨hzy ▸ hρ.bijOn.mapsTo (htop hz), hyD⟩
  have heq : z = (y, a) := hρ.bijOn.injOn (htop hz) ⟨hyJ, le_rfl, hab.le⟩
    (hzy.trans (hfix y hyJ).symm)
  exact hab.ne ((congrArg Prod.snd heq).symm.trans hz.2)

end DifferentialGeometry.Topology.PiecewiseLinear
