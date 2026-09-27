/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ConvexLevelSet
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsHPolytope.preimage_affineMap_of_injective {P : Set F} (hP : IsHPolytope P)
    (A : E →ᵃ[ℝ] F) (hA : Function.Injective A) : IsHPolytope (A ⁻¹' P) := by
  obtain ⟨ι, hι, l, c, hrepr⟩ := hP.2
  let _ : Finite ι := hι
  have hlinear : Function.Injective A.linear := A.linear_injective_iff.mpr hA
  have hemb : IsClosedEmbedding A := by
    have h := (Homeomorph.addRight (A 0)).isClosedEmbedding.comp
      (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hlinear))
    convert h using 1
    ext x
    change A x = A.linear x + A 0
    simpa using A.map_vadd 0 x
  refine ⟨hemb.isCompact_preimage hP.isCompact, ι, inferInstance,
    fun i => (l i).comp A.linear, fun i => c i - l i (A 0), ?_⟩
  ext x
  have hAx : A x = A.linear x + A 0 := by simpa using A.map_vadd 0 x
  simp only [mem_preimage, hrepr, mem_ofPred_eq, LinearMap.comp_apply, hAx, map_add]
  exact forall_congr' fun i => le_sub_iff_add_le.symm

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem IsHPolytope.isPLBall_inter_fiber {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {C : Set E} (hC : IsHPolytope C)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hinter : (interior C ∩ {x | ℓ x = r}).Nonempty) :
    IsPLBall n (C ∩ {x | ℓ x = r}) := by
  obtain ⟨e, π, hleft, hfixed, hheight⟩ := exists_affine_coordinates_of_linear_fiber hn ℓ hℓ r
  have hQ : IsHPolytope (e ⁻¹' C) := hC.preimage_affineMap_of_injective e hleft.injective
  obtain ⟨x, hx, hxr⟩ := hinter
  have hxQ : π x ∈ interior (e ⁻¹' C) :=
    preimage_interior_subset_interior_preimage e.continuous_of_finiteDimensional
      (by change e (π x) ∈ interior C; rwa [(hfixed x).mpr hxr])
  have hball : IsPLBall n (e ⁻¹' C) := by simpa using hQ.isPLBall ⟨π x, hxQ⟩
  apply hball.of_isPLHomeomorphOn
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hQ.isPolyhedron
    ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron hQ.isPolyhedron
      (subset_univ _))
  refine ⟨fun y hy => ⟨hy, hheight y⟩, hleft.injective.injOn, ?_⟩
  rintro y ⟨hy, hyr⟩
  exact ⟨π y, by change e (π y) ∈ C; rwa [(hfixed y).mpr hyr], (hfixed y).mpr hyr⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem IsHPolytope.isPLBall_inter_slab {C : Set E} (hC : IsHPolytope C)
    (a : E →ᵃ[ℝ] ℝ) {r s : ℝ}
    (hinter : (interior C ∩ {x | r < a x ∧ a x < s}).Nonempty) :
    IsPLBall (Module.finrank ℝ E) (C ∩ {x | r ≤ a x ∧ a x ≤ s}) := by
  have hpoly : IsHPolytope (C ∩ {x | r ≤ a x ∧ a x ≤ s}) :=
    hC.inter_preimage isHPolytope_Icc a
  apply hpoly.isPLBall
  obtain ⟨x, hx, hr, hs⟩ := hinter
  refine ⟨x, ?_⟩
  rw [interior_inter]
  refine ⟨hx, ?_⟩
  have ho : IsOpen {y | r < a y ∧ a y < s} :=
    (isOpen_lt continuous_const a.continuous_of_finiteDimensional).inter
      (isOpen_lt a.continuous_of_finiteDimensional continuous_const)
  have hsub : {y | r < a y ∧ a y < s} ⊆ {y | r ≤ a y ∧ a y ≤ s} :=
    fun _ hy => ⟨hy.1.le, hy.2.le⟩
  apply interior_mono hsub
  rw [ho.interior_eq]
  exact ⟨hr, hs⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem IsHPolytope.isPLBall_inter_fiber_of_lt_of_lt {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {C : Set E} (hC : IsHPolytope C)
    (hinter : (interior C).Nonempty) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hbelow : ∃ x ∈ C, ℓ x < r) (habove : ∃ y ∈ C, r < ℓ y) :
    IsPLBall n (C ∩ {x | ℓ x = r}) := by
  obtain ⟨x, hx, hxr⟩ := Topology.exists_mem_interior_fiber_of_convex hC.convex hinter
    ℓ.continuous_of_finiteDimensional hbelow habove
  exact hC.isPLBall_inter_fiber hn ℓ hℓ ⟨x, hx, hxr⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem IsHPolytope.isPLBall_inter_slab_of_le_of_le {C : Set E} (hC : IsHPolytope C)
    (hinter : (interior C).Nonempty) (a : E →ᵃ[ℝ] ℝ) {r s : ℝ} (hrs : r < s)
    (hbelow : ∃ x ∈ C, a x ≤ r) (habove : ∃ y ∈ C, s ≤ a y) :
    IsPLBall (Module.finrank ℝ E) (C ∩ {x | r ≤ a x ∧ a x ≤ s}) := by
  obtain ⟨x, hx, hxr⟩ := hbelow
  obtain ⟨y, hy, hsy⟩ := habove
  obtain ⟨z, hz, hzm⟩ := Topology.exists_mem_interior_fiber_of_convex hC.convex hinter
    a.continuous_of_finiteDimensional
    (r := (r + s) / 2) ⟨x, hx, by linarith⟩ ⟨y, hy, by linarith⟩
  exact hC.isPLBall_inter_slab a ⟨z, hz, by rw [hzm]; linarith, by rw [hzm]; linarith⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isPLBall_convexHull_inter_fiber {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hbelow : ∃ x ∈ T, ℓ x < r) (habove : ∃ y ∈ T, r < ℓ y) :
    IsPLBall n (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hinter : (interior (convexHull ℝ (T : Set E))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex hT (by omega)]
    exact ⟨T.centroid ℝ id, centroid_mem_openSimplex hne⟩
  exact (isHPolytope_convexHull_of_affineIndependent T hT).isPLBall_inter_fiber_of_lt_of_lt
    hn hinter ℓ hℓ
    (by obtain ⟨x, hx, hxr⟩ := hbelow; exact ⟨x, subset_convexHull ℝ _ hx, hxr⟩)
    (by obtain ⟨y, hy, hry⟩ := habove; exact ⟨y, subset_convexHull ℝ _ hy, hry⟩)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isPLBall_convexHull_inter_slab (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = Module.finrank ℝ E + 1)
    (a : E →ᵃ[ℝ] ℝ) {r s : ℝ} (hrs : r < s)
    (hbelow : ∃ x ∈ T, a x ≤ r) (habove : ∃ y ∈ T, s ≤ a y) :
    IsPLBall (Module.finrank ℝ E) (convexHull ℝ (T : Set E) ∩ {x | r ≤ a x ∧ a x ≤ s}) := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hinter : (interior (convexHull ℝ (T : Set E))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex hT hcard]
    exact ⟨T.centroid ℝ id, centroid_mem_openSimplex hne⟩
  exact (isHPolytope_convexHull_of_affineIndependent T hT).isPLBall_inter_slab_of_le_of_le
    hinter a hrs
    (by obtain ⟨x, hx, hxr⟩ := hbelow; exact ⟨x, subset_convexHull ℝ _ hx, hxr⟩)
    (by obtain ⟨y, hy, hsy⟩ := habove; exact ⟨y, subset_convexHull ℝ _ hy, hsy⟩)
end DifferentialGeometry.Topology.PiecewiseLinear
