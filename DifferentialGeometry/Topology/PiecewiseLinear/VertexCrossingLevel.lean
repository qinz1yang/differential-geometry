import DifferentialGeometry.Topology.PiecewiseLinear.HeightChange
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex
import DifferentialGeometry.Topology.PiecewiseLinear.VertexCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem isGlueIso_affineImage
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (A : E ≃ᵃ[ℝ] F) :
    IsGlueIso K (affineImage K A) A A.symm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mem_affineImage_faces_iff K A).mpr ⟨s, hs, rfl⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := (mem_affineImage_faces_iff K A).mp ht
    have heq : (s.image A).image A.symm = s := by
      ext x
      simp
    rw [heq]
    exact hs
  · intro s hs v hv
    exact A.symm_apply_apply v
  · intro t ht v hv
    exact A.apply_symm_apply v

open Classical in
theorem affineImage_faces_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K M : Geometry.SimplicialComplex ℝ E} (hM : M.faces ⊆ K.faces)
    (A : E ≃ᵃ[ℝ] F) : (affineImage M A).faces ⊆ (affineImage K A).faces := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := (mem_affineImage_faces_iff M A).mp ht
  exact (mem_affineImage_faces_iff K A).mpr ⟨s, hM hs, rfl⟩

open Classical in
theorem geometricLink_affineImage_space
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : E ≃ᵃ[ℝ] F)
    {p : E} (hp : {p} ∈ K.faces) :
    (SimplicialComplex.geometricLink (affineImage K A) {A p}).space =
      A '' (SimplicialComplex.geometricLink K {p}).space := by
  let _ : Finite (affineImage K A).faces := (affineImage_faces_finite K A).to_subtype
  have h := ((isGlueIso_affineImage K A).geometricLink hp).isPLHomeomorphOn
  rw [← h.image_eq]
  apply image_congr
  intro x hx
  exact simplicialMap_eqOn_affine
    (SimplicialComplex.geometricLink K {p}) A.toAffineMap hx

theorem hasPLCrossingAt_fiber_of_geometricLink_section_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (K M : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite M.faces]
    (hM : M.faces ⊆ K.faces) {p : E} (hp : {p} ∈ M.faces) (hK : K.space ∈ 𝓝 p)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hside : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ ℓ p} ∨
      convexHull ℝ (s : Set E) ⊆ {x | ℓ p ≤ ℓ x})
    (hlink : IsPLSphere 1 (SimplicialComplex.geometricLink M {p}).space)
    {a b : E} (hab : a ≠ b)
    (hlevel : (SimplicialComplex.geometricLink M {p}).space ∩ {x | ℓ x = ℓ p} = {a, b})
    (hpos : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ p < ℓ x)
    (hneg : ∃ x ∈ (SimplicialComplex.geometricLink M {p}).space, ℓ x < ℓ p) :
    HasPLCrossingAt M.space {x | ℓ x = ℓ p} p := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let A : E ≃ᵃ[ℝ] E := AffineEquiv.constVAdd ℝ E (-p)
  let K' := affineImage K A
  let M' := affineImage M A
  let _ : Finite K'.faces := (affineImage_faces_finite K A).to_subtype
  let _ : Finite M'.faces := (affineImage_faces_finite M A).to_subtype
  have hAp : A p = 0 := by
    change -p + p = 0
    exact neg_add_cancel p
  have hM' : M'.faces ⊆ K'.faces := affineImage_faces_subset hM A
  have hp' : {A p} ∈ M'.faces := (isGlueIso_affineImage M A).singleton_mem hp
  have hKspace : K'.space = A '' K.space := affineImage_space K A
  have hMspace : M'.space = A '' M.space := affineImage_space M A
  have hAfun : (A : E → E) = fun x => x - p := by
    funext x
    change -p + x = x - p
    rw [sub_eq_add_neg, add_comm]
  have hK' : K'.space ∈ 𝓝 (A p) := by
    rw [hKspace, hAfun]
    simpa only [Homeomorph.coe_subRight] using
      (Homeomorph.subRight p).isOpenMap.image_mem_nhds hK
  have hlinkspace : (SimplicialComplex.geometricLink M' {A p}).space =
      A '' (SimplicialComplex.geometricLink M {p}).space :=
    geometricLink_affineImage_space M A hp
  have hlink' : IsPLSphere 1 (SimplicialComplex.geometricLink M' {A p}).space := by
    exact hlink.of_isPLHomeomorphOn
      (((isGlueIso_affineImage M A).geometricLink hp).isPLHomeomorphOn.congr
        (simplicialMap_eqOn_affine
          (SimplicialComplex.geometricLink M {p}) A.toAffineMap).symm)
  have hside' : ∀ s ∈ K'.faces, convexHull ℝ (s : Set E) ⊆ {x | ℓ x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ ℓ x} := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := (mem_affineImage_faces_iff K A).mp hs
    obtain hlow | hhigh := hside t ht
    · left
      rw [Finset.coe_image]
      change convexHull ℝ (A.toAffineMap '' (t : Set E)) ⊆ {x | ℓ x ≤ 0}
      rw [← A.toAffineMap.image_convexHull]
      rintro _ ⟨x, hx, rfl⟩
      change ℓ (A.toAffineMap x) ≤ 0
      rw [show A.toAffineMap x = x - p by exact congrFun hAfun x]
      rw [map_sub, sub_nonpos]
      exact hlow hx
    · right
      rw [Finset.coe_image]
      change convexHull ℝ (A.toAffineMap '' (t : Set E)) ⊆ {x | 0 ≤ ℓ x}
      rw [← A.toAffineMap.image_convexHull]
      rintro _ ⟨x, hx, rfl⟩
      change 0 ≤ ℓ (A.toAffineMap x)
      rw [show A.toAffineMap x = x - p by exact congrFun hAfun x]
      rw [map_sub, sub_nonneg]
      exact hhigh hx
  have hlevel' : (SimplicialComplex.geometricLink M' {A p}).space ∩ {x | ℓ x = 0} =
      {A a, A b} := by
    have hfiber : {x | ℓ x = 0} = A '' {x | ℓ x = ℓ p} := by
      ext y
      constructor
      · intro hy
        refine ⟨y + p, ?_, ?_⟩
        · change ℓ (y + p) = ℓ p
          rw [map_add, hy, zero_add]
        · rw [hAfun]
          exact add_sub_cancel_right y p
      · rintro ⟨x, hx, rfl⟩
        change ℓ (A x) = 0
        rw [hAfun, map_sub, sub_eq_zero]
        exact hx
    rw [hlinkspace, hfiber, ← image_inter A.injective, hlevel, image_pair]
  have hpos' : ∃ x ∈ (SimplicialComplex.geometricLink M' {A p}).space, 0 < ℓ x := by
    obtain ⟨x, hx, hlt⟩ := hpos
    refine ⟨A x, hlinkspace.symm ▸ mem_image_of_mem A hx, ?_⟩
    rw [hAfun, map_sub, sub_pos]
    exact hlt
  have hneg' : ∃ x ∈ (SimplicialComplex.geometricLink M' {A p}).space, ℓ x < 0 := by
    obtain ⟨x, hx, hlt⟩ := hneg
    refine ⟨A x, hlinkspace.symm ▸ mem_image_of_mem A hx, ?_⟩
    rw [hAfun, map_sub, sub_neg]
    exact hlt
  have hcross' : HasPLCrossingAt M'.space {x | ℓ x = 0} (A p) :=
    hasPLCrossingAt_fiber_of_geometricLink_section hdimE K' M' hM' hp' hK' ℓ hℓ
      (by simpa only [hAp] using map_zero ℓ) hside' hlink' (A.injective.ne hab) hlevel'
      hpos' hneg'
  have hPL : IsPLHomeomorphOn (Homeomorph.subRight p) univ univ := by
    simpa only [Homeomorph.coe_subRight, sub_eq_add_neg] using isPLHomeomorphOn_add_const (-p)
  have hfiber : (Homeomorph.subRight p) '' {x | ℓ x = ℓ p} = {x | ℓ x = 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ℓ (x - p) = 0
      rw [map_sub, sub_eq_zero]
      exact hx
    · intro hy
      refine ⟨y + p, ?_, ?_⟩
      · change ℓ (y + p) = ℓ p
        rw [map_add, hy, zero_add]
      · exact add_sub_cancel_right y p
  apply (hasPLCrossingAt_image_homeomorph_iff (Homeomorph.subRight p) hPL).mp
  have hMimage : (Homeomorph.subRight p) '' M.space = M'.space := by
    rw [hMspace, hAfun]
    rfl
  have hpoint : (Homeomorph.subRight p) p = A p := by
    rw [hAp]
    exact sub_self p
  rw [hfiber, hMimage, hpoint]
  exact hcross'

end DifferentialGeometry.Topology.PiecewiseLinear
