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

end DifferentialGeometry.Topology.PiecewiseLinear
