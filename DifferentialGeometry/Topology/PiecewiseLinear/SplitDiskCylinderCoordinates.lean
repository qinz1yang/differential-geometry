/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CenteredDiskSimplexMap
import DifferentialGeometry.Topology.PiecewiseLinear.RevolvedTorusTower
import DifferentialGeometry.Topology.PiecewiseLinear.TubeCenteredPrismCoordinates

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private noncomputable def meridianCoordinates (x : E3) : EuclideanSpace ℝ (Fin 2) :=
  x 0 • EuclideanSpace.single 0 1 + x 2 • EuclideanSpace.single 1 1

private theorem meridianCoordinates_apply_zero (x : E3) : meridianCoordinates x 0 = x 0 := by
  simp [meridianCoordinates]

private theorem meridianCoordinates_apply_one (x : E3) : meridianCoordinates x 1 = x 2 := by
  simp [meridianCoordinates]

private theorem norm_meridianCoordinates_sq (x : E3) :
    ‖meridianCoordinates x‖ ^ 2 = x 0 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, meridianCoordinates_apply_zero,
    meridianCoordinates_apply_one]

private theorem continuous_meridianCoordinates : Continuous meridianCoordinates :=
  ((continuous_euclideanApply 0).smul continuous_const).add
    ((continuous_euclideanApply 2).smul continuous_const)

private theorem exists_cylinderPoint (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ∃ x : E3, x 0 = z 0 ∧ x 1 = t ∧ x 2 = z 1 :=
  ⟨z 0 • EuclideanSpace.single 0 1 + t • EuclideanSpace.single 1 1 +
    z 1 • EuclideanSpace.single 2 1, by simp, by simp, by simp⟩

private theorem meridianCoordinates_eq {x : E3} {z : EuclideanSpace ℝ (Fin 2)} (h0 : x 0 = z 0)
    (h2 : x 2 = z 1) : meridianCoordinates x = z := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change meridianCoordinates x 0 = z 0
    rw [meridianCoordinates_apply_zero, h0]
  · change meridianCoordinates x 1 = z 1
    rw [meridianCoordinates_apply_one, h2]

private theorem meridianCoordinates_mem_closedBall_iff (x : E3) :
    meridianCoordinates x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      x 0 ^ 2 + x 2 ^ 2 ≤ 1 := by
  rw [mem_closedBall_zero_iff, ← norm_meridianCoordinates_sq]
  constructor
  · intro h
    nlinarith [norm_nonneg (meridianCoordinates x)]
  · intro h
    nlinarith [norm_nonneg (meridianCoordinates x)]

private theorem meridianCoordinates_mem_sphere_iff (x : E3) :
    meridianCoordinates x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      x 0 ^ 2 + x 2 ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm, ← norm_meridianCoordinates_sq]
  constructor
  · intro h
    rw [h, one_pow]
  · intro h
    nlinarith [norm_nonneg (meridianCoordinates x)]

open Classical in
theorem IsTube.exists_unitSolidCylinder_coordinates {K : Geometry.SimplicialComplex ℝ E3}
    {N N' : Set E3} {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {u v : E3} (hu : u ∈ K.vertices) (hv : v ∈ K.vertices)
    (huv : u ≠ v) (he : ({u, v} : Finset E3) ∈ K.faces) :
    ∃ φ : E3 → E3, ContinuousOn φ unitSolidCylinder ∧ InjOn φ unitSolidCylinder ∧
      φ '' unitSolidCylinder = h '' C u ∪ h '' C v ∧ φ '' unitMeridianDisk = h '' D {u, v} ∧
      φ '' unitMeridianCircle = h '' Dbd {u, v} ∧
      φ 0 = h (({u, v} : Finset E3).centroid ℝ id) := by
  obtain ⟨g, hgc, hgi, hgB, hgS, hg0⟩ :=
    exists_continuous_injective_image_closedBall_eq_stdSimplex
  obtain ⟨ρ, hρ, hρ0, hρD, hρR, -, -⟩ := ht.exists_centered_prism_coordinates hu hv huv he
  let Γ : E3 → (Fin 3 → ℝ) × ℝ := fun x => (g (meridianCoordinates x), x 1)
  have hΓc : Continuous Γ :=
    (hgc.comp continuous_meridianCoordinates).prodMk (continuous_euclideanApply 1)
  have hΓi : Function.Injective Γ := by
    intro x y hxy
    have h1 : g (meridianCoordinates x) = g (meridianCoordinates y) := congrArg Prod.fst hxy
    have h2 : x 1 = y 1 := congrArg Prod.snd hxy
    have h3 := hgi h1
    have h0 : x 0 = y 0 := by
      rw [← meridianCoordinates_apply_zero x, ← meridianCoordinates_apply_zero y, h3]
    have h4 : x 2 = y 2 := by
      rw [← meridianCoordinates_apply_one x, ← meridianCoordinates_apply_one y, h3]
    refine PiLp.ext fun i => ?_
    fin_cases i
    · exact h0
    · exact h2
    · exact h4
  have hΓcyl : Γ '' unitSolidCylinder = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
    ext ⟨s, t⟩
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, hxst⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxst
      refine ⟨?_, abs_le.mp hx2⟩
      rw [← hgB]
      exact mem_image_of_mem g ((meridianCoordinates_mem_closedBall_iff x).mpr hx1)
    · rintro ⟨hs, htI⟩
      rw [← hgB] at hs
      obtain ⟨z, hz, rfl⟩ := hs
      obtain ⟨x, hx0, hx1, hx2⟩ := exists_cylinderPoint z t
      have hmx : meridianCoordinates x = z := meridianCoordinates_eq hx0 hx2
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · rw [← meridianCoordinates_mem_closedBall_iff, hmx]
        exact hz
      · rw [hx1]
        exact abs_le.mpr htI
      · change (g (meridianCoordinates x), x 1) = (g z, t)
        rw [hmx, hx1]
  have hΓdisk : Γ '' unitMeridianDisk = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(0 : ℝ)} := by
    ext ⟨s, t⟩
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, hxst⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxst
      refine ⟨?_, hx2⟩
      rw [← hgB]
      exact mem_image_of_mem g ((meridianCoordinates_mem_closedBall_iff x).mpr hx1)
    · rintro ⟨hs, htI⟩
      rw [← hgB] at hs
      obtain ⟨z, hz, rfl⟩ := hs
      obtain ⟨x, hx0, hx1, hx2⟩ := exists_cylinderPoint z t
      have hmx : meridianCoordinates x = z := meridianCoordinates_eq hx0 hx2
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · rw [← meridianCoordinates_mem_closedBall_iff, hmx]
        exact hz
      · rw [hx1]
        exact htI
      · change (g (meridianCoordinates x), x 1) = (g z, t)
        rw [hmx, hx1]
  have hΓrim : Γ '' unitMeridianCircle = stdSimplexBoundary 2 ×ˢ {(0 : ℝ)} := by
    ext ⟨s, t⟩
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, hxst⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxst
      refine ⟨?_, hx2⟩
      rw [← hgS]
      exact mem_image_of_mem g ((meridianCoordinates_mem_sphere_iff x).mpr hx1)
    · rintro ⟨hs, htI⟩
      rw [← hgS] at hs
      obtain ⟨z, hz, rfl⟩ := hs
      obtain ⟨x, hx0, hx1, hx2⟩ := exists_cylinderPoint z t
      have hmx : meridianCoordinates x = z := meridianCoordinates_eq hx0 hx2
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · rw [← meridianCoordinates_mem_sphere_iff, hmx]
        exact hz
      · rw [hx1]
        exact htI
      · change (g (meridianCoordinates x), x 1) = (g z, t)
        rw [hmx, hx1]
  have hΓ0 : Γ 0 = (stdCenter 1, 0) := by
    have hm0 : meridianCoordinates 0 = 0 := meridianCoordinates_eq (by simp) (by simp)
    change (g (meridianCoordinates 0), (0 : E3) 1) = (stdCenter 1, 0)
    rw [hm0, hg0]
    simp
  have hmaps : MapsTo Γ unitSolidCylinder (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
    fun x hx => hΓcyl ▸ mem_image_of_mem Γ hx
  have hCN : C u ∪ C v ⊆ N := union_subset (ht.dualCell_subset hu) (ht.dualCell_subset hv)
  have hmaps' : MapsTo (ρ ∘ Γ) unitSolidCylinder N :=
    fun x hx => hCN (hρ.bijOn.mapsTo (hmaps hx))
  have himg : ∀ X : Set E3, (fun x => h (ρ (Γ x))) '' X = h '' (ρ '' (Γ '' X)) := fun X => by
    rw [image_image, image_image]
  refine ⟨fun x => h (ρ (Γ x)),
    ht.continuousOn.comp (hρ.isPiecewiseAffineOn.continuousOn.comp hΓc.continuousOn hmaps)
      hmaps',
    ht.injOn.comp (hρ.bijOn.injOn.comp hΓi.injOn hmaps) hmaps', ?_, ?_, ?_, ?_⟩
  · rw [himg, hΓcyl, hρ.bijOn.image_eq, image_union]
  · rw [himg, hΓdisk, hρD]
  · rw [himg, hΓrim, hρR]
  · change h (ρ (Γ 0)) = _
    rw [hΓ0, hρ0]

end DifferentialGeometry.Topology.PiecewiseLinear
