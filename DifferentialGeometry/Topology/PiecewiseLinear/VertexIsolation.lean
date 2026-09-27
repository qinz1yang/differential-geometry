/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubspace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hzero : (SimplicialComplex.geometricLink K {p}).space ∩
      {x | ℓ x = ℓ p} = ∅) :
    {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p := by
  have hstar : ∀ᶠ x in 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p,
      x ∈ closedStar K p ↔ x ∈ K.space :=
    (eventually_mem_closedStar_iff K p).filter_mono nhdsWithin_le_nhds
  filter_upwards [hstar, self_mem_nhdsWithin]
    with x hxstar hx
  have hxclosed : x ∈ closedStar K p := hxstar.mpr hx.1
  rw [closedStar_eq_coneComplex_space K hp] at hxclosed
  rcases (mem_coneComplex_space_iff _).mp hxclosed with hxp | ⟨z, hz, s, hs, hs1, hzx⟩
  · exact hxp ▸ mem_singleton p
  · have hzlevel : ℓ z = ℓ p := by
      have hlevel := hx.2
      change ℓ x = ℓ p at hlevel
      rw [hzx, map_add, map_smul, map_sub, smul_eq_mul] at hlevel
      have hmul : s * (ℓ z - ℓ p) = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hs.ne')
    have hzmem : z ∈ (SimplicialComplex.geometricLink K {p}).space ∩
        {y | ℓ y = ℓ p} := ⟨hz, hzlevel⟩
    rw [hzero] at hzmem
    exact hzmem.elim

theorem notMem_heightSingularPoints_of_geometricLink_section_eq_empty
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hzero : (SimplicialComplex.geometricLink K {p}).space ∩
      {x | ℓ x = ℓ p} = ∅) :
    p ∉ heightSingularPoints K.space ℓ :=
  notMem_heightSingularPoints_of_isolated
    (singleton_mem_nhdsWithin_fiber_of_geometricLink_section_eq_empty K hp ℓ hzero)

theorem notMem_heightSingularPoints_of_geometricLink_strictly_above
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (habove : ∀ x ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ p < ℓ x) :
    p ∉ heightSingularPoints K.space ℓ := by
  apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty K hp ℓ
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxeq⟩
  exact (habove x hx).ne' hxeq

theorem notMem_heightSingularPoints_of_geometricLink_strictly_below
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    (hbelow : ∀ x ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ x < ℓ p) :
    p ∉ heightSingularPoints K.space ℓ := by
  apply notMem_heightSingularPoints_of_geometricLink_section_eq_empty K hp ℓ
  rw [eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxeq⟩
  exact (hbelow x hx).ne hxeq

end DifferentialGeometry.Topology.PiecewiseLinear
