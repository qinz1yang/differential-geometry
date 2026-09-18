import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialPairImage
import DifferentialGeometry.Topology.PiecewiseLinear.VertexBranchSection

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_linearEquiv_normalForm_of_geometricLink_pair [DecidableEq E]
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hlinkM : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    {a b : E} (hab : a ≠ b)
    (hlevel : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ p < ℓ x)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < ℓ p) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  obtain ⟨R, hRfin, -, hRK, -, hRside⟩ := exists_triangulation_union_with_halfSpace_faces K
    (isPolyhedron_space K) ℓ.toLinearMap.toAffineMap (ℓ p)
  let _ : Finite R.faces := hRfin.to_subtype
  change IsSubdivision (restrict R K.space) K at hRK
  let K₂ := restrict R K.space
  let _ : Finite K₂.faces := (restrict_faces_finite R K.space).to_subtype
  have hK₂space : K₂.space = K.space := hRK.space_eq
  have hside₂ : ∀ s ∈ K₂.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x} := by
    intro s hs
    simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
      hRside s (restrict_faces_subset R K.space hs)
  have hM₂ : IsSubdivision (restrict K₂ M.space) M := hRK.restrict M hM
  let M₂ := restrict K₂ M.space
  let _ : Finite M₂.faces := (restrict_faces_finite K₂ M.space).to_subtype
  have hM₂space : M₂.space = M.space := hM₂.space_eq
  have hM₂faces : M₂.faces ⊆ K₂.faces := restrict_faces_subset K₂ M.space
  have hpM₂ : ({p} : Finset E) ∈ M₂.faces := hM₂.singleton_mem hp
  have hsideM₂ : ∀ s ∈ M₂.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ.toLinearMap x ≤ ℓ.toLinearMap p}
      ∨ convexHull ℝ (s : Set E) ⊆ {x | ℓ.toLinearMap p ≤ ℓ.toLinearMap x} := by
    intro s hs
    simpa only [ContinuousLinearMap.coe_coe] using hside₂ s (hM₂faces hs)
  obtain ⟨f, hf, hfeq, hflt, hfgt⟩ :=
    exists_isPLHomeomorphOn_geometricLink_of_isSubdivision_preserving_height_sign hM₂ hp
      ℓ.toLinearMap hsideM₂
  simp only [ContinuousLinearMap.coe_coe] at hfeq hflt hfgt
  have hlink₂ : IsPLSphere 1 (SimplicialComplex.geometricLink M₂ {p}).space :=
    hlinkM.of_isPLHomeomorphOn hf.symm
  have hneg₂ : ∃ x ∈ (SimplicialComplex.geometricLink M₂ {p}).space, ℓ x < ℓ p := by
    obtain ⟨x, hx, hlt⟩ := hneg
    obtain ⟨y, hy, -⟩ := hflt.symm.subset ⟨hx, hlt⟩
    exact ⟨y, hy.1, hy.2⟩
  have hpos₂ : ∃ x ∈ (SimplicialComplex.geometricLink M₂ {p}).space, ℓ p < ℓ x := by
    obtain ⟨x, hx, hlt⟩ := hpos
    obtain ⟨y, hy, -⟩ := hfgt.symm.subset ⟨hx, hlt⟩
    exact ⟨y, hy.1, hy.2⟩
  have hinjf : Set.InjOn f
      ((SimplicialComplex.geometricLink M₂ {p}).space ∩ {x | ℓ x = ℓ p}) :=
    hf.bijOn.injOn.mono Set.inter_subset_left
  have hcard : ((SimplicialComplex.geometricLink M₂ {p}).space ∩
      {x | ℓ x = ℓ p}).encard = 2 := by
    rw [← hinjf.encard_image, hfeq, hlevel, Set.encard_pair hab]
  obtain ⟨a₂, b₂, hab₂, hlevel₂⟩ := Set.encard_eq_two.mp hcard
  obtain ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, hnear⟩ :=
    exists_linearEquiv_normalForm_of_geometricLink_section hn K₂ M₂ hM₂faces hpM₂
      (by rw [hK₂space]; exact hK) ℓ hℓ hside₂ hlink₂ hab₂ hlevel₂ hpos₂ hneg₂
  refine ⟨U, V, h, L, hU, hV, hpU, hPLh, hhp, ?_⟩
  rw [← hM₂space]
  exact hnear

theorem exists_linearEquiv_normalForm_of_isPLSphere_link [DecidableEq E]
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hlinkM : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    (hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p}))
    {u v : E} (hu : u ∈ closedStar M p) (hv : v ∈ closedStar M p)
    (hult : ℓ u < ℓ p) (hvlt : ℓ p < ℓ v) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  obtain ⟨a, b, hab, hlevel⟩ :=
    exists_pair_geometricLink_fiber_of_isPLSphere_one M hp ℓ.toLinearMap hfiber
  refine exists_linearEquiv_normalForm_of_geometricLink_pair hn K M hM hp hK ℓ hℓ hlinkM hab
    (by simpa only [ContinuousLinearMap.coe_coe] using hlevel)
    (by
      simpa only [ContinuousLinearMap.coe_coe] using
        exists_mem_geometricLink_lt_apply_of_mem_closedStar M hp ℓ.toLinearMap hv hvlt)
    (by
      simpa only [ContinuousLinearMap.coe_coe] using
        exists_mem_geometricLink_apply_lt_of_mem_closedStar M hp ℓ.toLinearMap hu hult)

theorem exists_linearEquiv_normalForm_of_isCombinatorialManifold
    (hn : Module.finrank ℝ E = 3) (K M : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite M.faces] (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces)
    (hK : K.space ∈ 𝓝 p) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hMan : IsCombinatorialManifold 2 M)
    (hfiber : IsPLSphere 1 (M.space ∩ {x | ℓ x = ℓ p}))
    {u v : E} (hu : u ∈ closedStar M p) (hv : v ∈ closedStar M p)
    (hult : ℓ u < ℓ p) (hvlt : ℓ p < ℓ v) :
    ∃ (U V : Set E) (h : E → E) (L : E ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ p ∈ U ∧ IsPLHomeomorphOn h U V ∧ h p = 0 ∧
        ∀ᶠ y in 𝓝 p, (y ∈ M.space → (L (h y)).2.2 = 0) ∧ (ℓ y = ℓ p → (L (h y)).2.1 = 0) := by
  classical
  exact exists_linearEquiv_normalForm_of_isPLSphere_link hn K M hM hp hK ℓ hℓ (hMan p hp) hfiber
    hu hv hult hvlt

theorem exists_linearEquiv_normalForm_two_sheets
    (K₁ N₁ : Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ))
    [Finite K₁.faces] [Finite N₁.faces] (hN : N₁.faces ⊆ K₁.faces)
    {q : ℝ × ℝ × ℝ} (hq : {q} ∈ N₁.faces) (hK : K₁.space ∈ 𝓝 q)
    (hlinkN : IsPLSphere 1 (SimplicialComplex.geometricLink N₁ {q}).space)
    {a b : ℝ × ℝ × ℝ} (hab : a ≠ b)
    (hlevel : (SimplicialComplex.geometricLink N₁ {q}).space ∩ {x | x.2.2 = q.2.2} = {a, b})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {q}).space, q.2.2 < x.2.2)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {q}).space, x.2.2 < q.2.2) :
    ∃ (U V : Set (ℝ × ℝ × ℝ)) (h : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
      (L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ q ∈ U ∧ IsPLHomeomorphOn h U V ∧ h q = 0 ∧
        ∀ᶠ y in 𝓝 q, (y ∈ N₁.space → (L (h y)).2.2 = 0) ∧
          (y.2.2 = q.2.2 → (L (h y)).2.1 = 0) := by
  classical
  have hn : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  have hℓne : (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) ≠ 0 := by
    intro h0
    have h1 : ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = 0 := by
      rw [h0]
      rfl
    exact one_ne_zero h1
  exact exists_linearEquiv_normalForm_of_geometricLink_pair hn K₁ N₁ hN hq hK
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) hℓne hlinkN hab
    hlevel hpos hneg

theorem exists_pair_height_section_of_isPLSphere_one {S : Set (ℝ × ℝ × ℝ)}
    (hS : IsPLSphere 1 S) (ℓ : (ℝ × ℝ × ℝ) →L[ℝ] ℝ) (r : ℝ)
    (hneg : ∃ x ∈ S, ℓ x < r) (hpos : ∃ x ∈ S, r < ℓ x) :
    ∃ a b : ℝ × ℝ × ℝ, a ≠ b ∧ a ∈ S ∩ {x : ℝ × ℝ × ℝ | ℓ x = r} ∧
      b ∈ S ∩ {x : ℝ × ℝ × ℝ | ℓ x = r} := by
  obtain ⟨x, hxS, hx⟩ := hneg
  obtain ⟨y, hyS, hy⟩ := hpos
  obtain ⟨z, hzS, hz⟩ := hS.isConnected_one.isPreconnected.intermediate_value hxS hyS
    ℓ.continuous.continuousOn ⟨hx.le, hy.le⟩
  have hxz : x ≠ z := by
    rintro rfl
    exact hx.ne hz
  have hyz : y ≠ z := by
    rintro rfl
    exact hy.ne' hz
  obtain ⟨w, hw, hwlevel⟩ :=
    (hS.isConnected_sdiff_singleton_one z).isPreconnected.intermediate_value ⟨hxS, hxz⟩
      ⟨hyS, hyz⟩ ℓ.continuous.continuousOn ⟨hx.le, hy.le⟩
  exact ⟨z, w, fun h => hw.2 h.symm, ⟨hzS, hz⟩, ⟨hw.1, hwlevel⟩⟩

theorem exists_linearEquiv_normalForm_two_sheets_of_arc_section
    (K₁ N₁ : Geometry.SimplicialComplex ℝ (ℝ × ℝ × ℝ))
    [Finite K₁.faces] [Finite N₁.faces] (hN : N₁.faces ⊆ K₁.faces)
    {q : ℝ × ℝ × ℝ} (hq : {q} ∈ N₁.faces) (hK : K₁.space ∈ 𝓝 q)
    (hlinkN : IsPLSphere 1 (SimplicialComplex.geometricLink N₁ {q}).space)
    (harc : IsPLBall 1 (N₁.space ∩ {x : ℝ × ℝ × ℝ | x.2.2 = q.2.2}))
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {q}).space, q.2.2 < x.2.2)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink N₁ {q}).space, x.2.2 < q.2.2) :
    ∃ (U V : Set (ℝ × ℝ × ℝ)) (h : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
      (L : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] ℝ × ℝ × ℝ),
      IsOpen U ∧ IsOpen V ∧ q ∈ U ∧ IsPLHomeomorphOn h U V ∧ h q = 0 ∧
        ∀ᶠ y in 𝓝 q, (y ∈ N₁.space → (L (h y)).2.2 = 0) ∧
          (y.2.2 = q.2.2 → (L (h y)).2.1 = 0) := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := exists_pair_height_section_of_isPLSphere_one hlinkN
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) q.2.2 hneg hpos
  have hlevel := geometricLink_fiber_eq_pair_of_isPLBall_one N₁ hq
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))) harc hab ha hb
  exact exists_linearEquiv_normalForm_two_sheets K₁ N₁ hN hq hK hlinkN hab hlevel hpos hneg

end DifferentialGeometry.Topology.PiecewiseLinear
