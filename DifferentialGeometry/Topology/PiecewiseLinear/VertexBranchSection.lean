/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.HeightLevelLink
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem closedStar_eq_coneSet_geometricLink [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ K.faces) :
    closedStar K p = coneSet p (SimplicialComplex.geometricLink K {p}).space :=
  (closedStar_eq_coneComplex_space K hp).trans
    (coneComplex_space_eq_coneSet (isConeBase_geometricLink K (p := p)))

omit [FiniteDimensional ℝ E] in
theorem exists_mem_geometricLink_smul_of_mem_closedStar [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ K.faces) {x : E}
    (hx : x ∈ closedStar K p) (hxp : x ≠ p) :
    ∃ z ∈ (SimplicialComplex.geometricLink K {p}).space, ∃ s : ℝ, 0 < s ∧
      x = p + s • (z - p) := by
  rw [closedStar_eq_coneSet_geometricLink K hp] at hx
  rcases mem_coneSet_iff.mp hx with rfl | ⟨z, hz, s, hs, -, rfl⟩
  · exact absurd rfl hxp
  · exact ⟨z, hz, s, hs, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem exists_mem_geometricLink_apply_lt_of_mem_closedStar [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    {x : E} (hx : x ∈ closedStar K p) (hlt : ℓ x < ℓ p) :
    ∃ z ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ z < ℓ p := by
  have hxp : x ≠ p := by
    rintro rfl
    exact lt_irrefl _ hlt
  obtain ⟨z, hz, s, hs, rfl⟩ := exists_mem_geometricLink_smul_of_mem_closedStar K hp hx hxp
  refine ⟨z, hz, ?_⟩
  rw [map_add, map_smul, map_sub, smul_eq_mul] at hlt
  nlinarith

omit [FiniteDimensional ℝ E] in
theorem exists_mem_geometricLink_lt_apply_of_mem_closedStar [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ)
    {x : E} (hx : x ∈ closedStar K p) (hlt : ℓ p < ℓ x) :
    ∃ z ∈ (SimplicialComplex.geometricLink K {p}).space, ℓ p < ℓ z := by
  have hxp : x ≠ p := by
    rintro rfl
    exact lt_irrefl _ hlt
  obtain ⟨z, hz, s, hs, rfl⟩ := exists_mem_geometricLink_smul_of_mem_closedStar K hp hx hxp
  refine ⟨z, hz, ?_⟩
  rw [map_add, map_smul, map_sub, smul_eq_mul] at hlt
  nlinarith

theorem exists_pair_geometricLink_fiber_of_isPLSphere_one [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) (hfiber : IsPLSphere 1 (K.space ∩ {x | ℓ x = ℓ p})) :
    ∃ a b : E, a ≠ b ∧
      (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p} = {a, b} :=
  Set.encard_eq_two.mp (encard_geometricLink_fiber_of_isPLSphere_one K hp ℓ hfiber)

theorem exists_linearEquiv_normalForm_of_isPLSphere_one_fiber [DecidableEq E]
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    (hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p}))
    {u v : E} (hu : u ∈ closedStar M p) (hv : v ∈ closedStar M p)
    (hult : ℓ u < ℓ p) (hvlt : ℓ p < ℓ v) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  obtain ⟨a, b, hab, hlevel⟩ :=
    exists_pair_geometricLink_fiber_of_isPLSphere_one M hp ℓ.toLinearMap hfiber
  exact exists_linearEquiv_normalForm_of_geometricLink_section hn K M hM hp hK ℓ hℓ hside hlink
    hab hlevel (exists_mem_geometricLink_lt_apply_of_mem_closedStar M hp ℓ.toLinearMap hv hvlt)
    (exists_mem_geometricLink_apply_lt_of_mem_closedStar M hp ℓ.toLinearMap hu hult)

theorem encard_geometricLink_fiber_le_two_of_isPLBall_one [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) (hfiber : IsPLBall 1 (K.space ∩ {x | ℓ x = ℓ p})) :
    ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤ 2 := by
  obtain ⟨F, f, hFfin, hFspace, hpF, hf⟩ := exists_isPLHomeomorphOn_geometricLink_fiber K hp ℓ
  let _ : Finite F.faces := hFfin.to_subtype
  have hF : IsPLBall 1 F.space := hFspace.symm ▸ hfiber
  rcases isPLSphere_or_isPLBall_geometricLink_of_isPLBall F hF hpF with h | h
  · obtain ⟨a, b, hab, hpair⟩ := isPLSphere_zero_iff.mp (h.of_isPLHomeomorphOn hf)
    rw [hpair, Set.encard_pair hab]
  · obtain ⟨z, hz⟩ := isPLBall_zero_iff.mp (h.of_isPLHomeomorphOn hf)
    rw [hz, Set.encard_singleton]
    norm_num

theorem geometricLink_fiber_eq_pair_of_isPLBall_one [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {p : E} (hp : {p} ∈ K.faces)
    (ℓ : E →ₗ[ℝ] ℝ) (hfiber : IsPLBall 1 (K.space ∩ {x | ℓ x = ℓ p})) {a b : E} (hab : a ≠ b)
    (ha : a ∈ (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p})
    (hb : b ∈ (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}) :
    (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p} = {a, b} := by
  have hsub : ({a, b} : Set E) ⊆
      (SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p} := by
    rintro x (rfl | rfl)
    · exact ha
    · exact hb
  have hcard : ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤
      ({a, b} : Set E).encard := by
    rw [Set.encard_pair hab]
    exact encard_geometricLink_fiber_le_two_of_isPLBall_one K hp ℓ hfiber
  exact (((Set.finite_singleton b).insert a).eq_of_subset_of_encard_le hsub hcard).symm

end DifferentialGeometry.Topology.PiecewiseLinear
