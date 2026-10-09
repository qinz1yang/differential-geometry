import DifferentialGeometry.Geometry.Metric.TwoRayConeData

set_option autoImplicit false

namespace GC.MetricGeometry

open Set
open scoped NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X]

namespace TwoRayConeData

variable {p : X} (C : TwoRayConeData p)

theorem ray_eq_unitRay {γ : ℝ≥0 → X} (hγ : γ ∈ C.rays) {t : ℝ≥0} (ht : t ≠ 0) :
    γ = C.toRadialConeData.unitRay (γ t) := by
  have hx : γ t ≠ p := by
    intro hh
    have hd := C.dist_apex hγ t
    rw [hh, dist_self] at hd
    exact ht (NNReal.eq hd.symm)
  apply C.toRadialConeData.unitRay_unique hx γ (C.isometry γ hγ) (C.basepoint γ hγ)
  have ht' : nndist p (γ t) = t := NNReal.eq (C.dist_apex hγ t)
  rw [ht']

theorem rays_eq_of_meet {γ η : ℝ≥0 → X} (hγ : γ ∈ C.rays) (hη : η ∈ C.rays)
    {s t : ℝ≥0} (hs : s ≠ 0) (hmeet : γ s = η t) : γ = η := by
  have hst : s = t := by
    apply NNReal.eq
    rw [← C.dist_apex hγ, hmeet, C.dist_apex hη]
  have ht : t ≠ 0 := hst ▸ hs
  rw [C.ray_eq_unitRay hγ hs, C.ray_eq_unitRay hη ht, hmeet]

theorem toRadialConeData_map_ray {γ : ℝ≥0 → X} (hγ : γ ∈ C.rays) (s t : ℝ≥0) :
    C.toRadialConeData.map s (γ t) = γ (s * t) := by
  by_cases ht : t = 0
  · subst t
    rw [mul_zero, C.basepoint γ hγ, C.toRadialConeData.map_apex]
  · have hγeq := C.ray_eq_unitRay hγ ht
    have ht' : nndist p (γ t) = t := NNReal.eq (C.dist_apex hγ t)
    have hh := congrFun hγeq (s * t)
    rw [RadialConeData.unitRay, ht', mul_div_cancel_right₀ s ht] at hh
    exact hh.symm

theorem mem_rays_iff {γ : ℝ≥0 → X} : γ ∈ C.rays ↔ Isometry γ ∧ γ 0 = p := by
  constructor
  · intro hγ
    exact ⟨C.isometry γ hγ, C.basepoint γ hγ⟩
  · rintro ⟨hγ, hz⟩
    have hx : γ 1 ≠ p := by
      intro hh
      exact one_ne_zero (hγ.injective (hh.trans hz.symm))
    have hr : dist p (γ 1) = 1 := by
      rw [← hz, hγ.dist_eq]
      change |(0 : ℝ) - 1| = 1
      norm_num
    have hn : nndist p (γ 1) = 1 := NNReal.eq hr
    have hcan := C.toRadialConeData.unitRay_unique hx γ hγ hz (by rw [hn])
    have hchosen := C.toRadialConeData.unitRay_unique hx (C.chosenRay (γ 1))
      (C.isometry _ (C.chosenRay_mem _)) (C.basepoint _ (C.chosenRay_mem _))
      (C.chosenRay_through _)
    rw [hcan.trans hchosen.symm]
    exact C.chosenRay_mem _

theorem not_subsingleton (C : TwoRayConeData p) : ¬ Subsingleton X := by
  intro hs
  let := hs
  obtain ⟨γ, hγ, t, _⟩ := C.coverage p
  have he : (0 : ℝ≥0) = 1 := (C.isometry γ hγ).injective (Subsingleton.elim _ _)
  exact zero_ne_one he

end TwoRayConeData

namespace RadialConeData

theorem toTwoRayConeData_toRadialConeData_map {p : X} (H : RadialConeData p)
    [Nontrivial X] (s : ℝ≥0) (x : X) :
    H.toTwoRayConeData.toRadialConeData.map s x = H.map s x := by
  by_cases hx : x = p
  · subst x
    rw [H.toTwoRayConeData.toRadialConeData.map_apex, H.map_apex]
  · have hn : nndist p x ≠ 0 := by simpa only [ne_eq, nndist_eq_zero] using (Ne.symm hx)
    have hmem : H.unitRay x ∈ H.toTwoRayConeData.rays := ⟨⟨x, hx⟩, rfl⟩
    have hh := H.toTwoRayConeData.toRadialConeData_map_ray hmem s (nndist p x)
    rw [H.unitRay_through hx] at hh
    rw [unitRay, mul_div_cancel_right₀ s hn] at hh
    exact hh

noncomputable def ofSubsingleton (p : X) [Subsingleton X] : RadialConeData p where
  map _ _ := p
  map_zero _ := rfl
  map_one x := Subsingleton.elim p x
  dist_sq s t x y := by
    have hx : x = p := Subsingleton.elim _ _
    have hy : y = p := Subsingleton.elim _ _
    subst x
    subst y
    simp only [dist_self, radialConeKernel, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_add, zero_div, sub_zero]

end RadialConeData

theorem nonempty_radialConeData_iff_subsingleton_or_twoRayConeData {p : X} :
    Nonempty (RadialConeData p) ↔ Subsingleton X ∨ Nonempty (TwoRayConeData p) := by
  classical
  constructor
  · intro h
    rcases subsingleton_or_nontrivial X with hs | hn
    · exact Or.inl hs
    · let := hn
      exact Or.inr (nonempty_radialConeData_iff_twoRayConeData.mp h)
  · intro h
    rcases h with hs | hC
    · let := hs
      exact ⟨RadialConeData.ofSubsingleton p⟩
    · obtain ⟨C⟩ := hC
      exact ⟨C.toRadialConeData⟩

end GC.MetricGeometry
